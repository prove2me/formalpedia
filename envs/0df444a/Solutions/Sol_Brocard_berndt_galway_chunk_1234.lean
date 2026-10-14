-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1234
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:54:30.306429+00:00
-- url     : https://prove2.me/submissions/36ba6434-bf3a-4b07-a5d4-bbbaa9380702

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 221762589 ≤ n < 221942446 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 221763839 1250 221762589 221762609
    0xa08070e0402121b0c030306040e01092901060f1b02040b03011104050910030c0e070203040e130b2811070b180106080a0b130c0e19060b0702010207051306 68
    0x4802e4442c003103c0304900351003015442c46003084400071921200305566035100c2c035030003441c995102c110410000d0b241605041016542c1d80000c0800100e02481c400041e02081e00c406030b60031800500b4070907244059101d03909121600006442d2a90b120315007a004148024982001e5603090020038000c090100110b50150f03c4c0820600304a024600900201c0c0c02c21142c0c0c0000b41e4074031810b00c440c0c2409210041159000540510a0710b03000c07411254444490301c1164201580c801504c041000240d071001092904290740c0c2060010b05204117a000c122600540c031048000003149865040001121219a80d500d00c11000c01c5100780454900c02e422101d10600c03030402e4914656022000c220527484d9600c1c154000a0550011420700300703060304060030b40a95960754068000340142c8900884141d08210804100000110117a5000b01e101180c500000583c00b0014411220345411030f01001c68140207400060383c0c0041c1240a07034906541040310b4401301c1540c403015202c84c1d04280829 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 221765089 1250 221763839 221763847
    0x1030e0f0102031f051030050705030906070f02120a02070b0c0105100816031416060305060f040605090c070c241b02010e060c0304080102070b04050705030607050a08070e0402 77
    0x4000c0c013850880d01070616680d80104280c0d101d00b0003210f00100940f0030041420f4a950605405091180b410301d000f4940b5050041d140c8660100122241200c000c000f00b1030100602c41c1302001013186035484655030401d8225548400c4019641e0712407045000c02c42040001c1041d8000d200340404801022840b18445d100c41440f076a04c2c0c0070301422100810040d604180006250400080103410910603014400070030342581c4916081c0030f030003890300d0a02c1c8500b044040c61410036034521001000780340c0d00026282088400c0099881c40490710324031981c10b104042c0020313951a00242d801610841c0d50550703905444ca07000f60070031240d0740b14044100c00642107445c0c1404100800109106690b0754a03c00300d001c1040c0e602420b45100701038002110034040403042d06182000b44000708a0702c0860381010303641c0041c9426a40301441c1203d10116201c10b0100300041040080050300040300605981d190590b001403c0b40282002d1400b00608030303000c180c009010b83e02d040c94043c0c000d84150360b0303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 221766339 1250 221765089 221765101
    0x2090a06030311120409020f09100e090c130509130b040807020307090615140f130905010510050706091a010305010c11030a0e040509030405180103050105060103150501030e0f010203 80
    0x3014188410740c040303410b003011142070500110710f40d550b9030900c0480c981064101000c000003034000e080f0300d49007031508000320100c5645d0310207100c82803056543c4051801d40303040e0912520200142c00401e10303c00c03d09c03441a4158078100c00744240c900644081e90680e03a85000aa04440c9045014000d40c2654040c071041c03015030f2000301a054025022501102d0f507882812040b44c549108603424007203443c000080ca90f00c41c8a03058034004d00300e5000c0781441d4003c590610b150740124002d172204a84c80e41c003080020010f00030036006000444000000020340c01c0c01410038850b815004101d20f6842c201d02041042c1100125007a210180041c060b40d82c40703240081c0200500050351000c60050170300c4401a14002084650070075803a40c9100031641d20324148805007070041d0092286000074000413505486240d0406500c20031240309141c00c0d451414460f00710303480600014101400e2282200044d140202d801c800c4a40030f28000403011441c20426003803070501200b07041a94000010320807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 221767589 1250 221766339 221766341
    0x20f0706020f0316020c090f130c080c040e010902150d15060c0317090d14190504180b06041202060c010c02010f0b030c03060f10030c180c0c050a02040b04020702090a 73
    0x11150121401d00354000c03401204c00c0c0e036100048a6010361180d500000181e0145054030b142e174024144000701c1210495640e965003140c2c2a82c0c00020784d56200d12120012440c1c1401400c0c140d1001000070882c682d866004111180403401081e200e8680004070b40b40341001c158000310f66444ea184002d480c09480700401000a986444140c1c0042e05500c502154803880c18907042c0200a024000c1c0b21584210b4401e80d003503089402902c0031901c0912000240404074032010007404681da54490390f49042445e4150847c040c54503240c460791404084011507250b0300c00319015600000ba0b128580403451000407194482c41110860301d50070108400005130301500710b0800d080d0700d180180315140080043c036641e0211030350781d154950300c0400801c488a0b503a42003240c0000c8185054101a51030707448040107400b55611108140303000001d100100d01462052180d41d0f0340d1403403e40022511912555a40d612514000e8411a0f40c1c0648442541c0e8540c110341410358003a208410510300790010348 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 221768839 1250 221767589 221767591
    0x20d061a010806100c0201140c010908071a16031d0a0b090613020310020a14030c0a0306060806030c010809070f18111201030f0c030611031b0c0d03020f0706020f03 72
    0x241c007240d41000440d41514113816030b081c42c2207240c1c0d5a2110203c5035001119224180304e04a040c4200400114070340f1142800740050300c41c02905465912051032030030f00744038940144c903a10b0541c1c20400b400882e4510041c0e4010084540c6004600340300d10a08454044081c400090843d01c16200e4801c00c000700d20b1945880781c00b412056446580d18051024000c10800078005e600d40c21440c041d49600314694040c10403c03440c0e16000c0142c3c90740c038418074501e61054881603c40f240100d01707200700300e03454090741e0044d14461901a5075828503002007561903049903c41d9041c0f004060000710403400400140009101d0040411500d550b58002040800a007481c8802002d00700850070f00c04d040210210359030040551351580890b8a5134645155080c0414400c07030340e600780e008001000c924580034025107448055421956400e0056110400415540c000420008103010501d440c2201050050026130f4608015a0f00c1d2644500007120b44141d0000901c4c1070f10104070f40607881c003c03a02031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 221770089 1250 221768839 221768891
    0x9010905010f0506010507080c280b070201110403140f0316020102010e030a09050904060b03010c030518070e0a1107050708070e0c0301030519030c0b16121b0c020d06 73
    0xc000070000c2c11010016500c2c1222102d0101e0700801490b00064805001403400c1a550710176149a1104580794000c2841030b4442021500c6010340c0000500c45410140b94110342c560000b08443c0306664500c00c2c06020700e10000e0310b01030300301c40540e50501e0180550f003002450541980e170f641400c19965540050045010f1b8010f41c07800300c1c2c002d40c3d42400001c171070b184030840e10b40381032041c030308400c0080e00b8070014402c42d50551110791001440c0c50900409502008584000c10103240620f2000304540c8148103104403940010020428405002c80340da40003021082d0214001c50034500144007445250350080c407910800c1c600280d060000b082d20811340341417004c00b800645881001d00b9090100b80030250240c0c20800301c00448410040d9052801446420404c500499607181c9040c8928200c03205083e0312103115019100d6540640901d581c0c00c041c46003000f4100346402d008034200c601c069040188029650201c055580328200c200416921041c24050242220b079000c160202c0c1000c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 221771339 1250 221770089 221770091
    0x8030703090507061e030203101502160303090e0a090f0b090c0a08010504140303010303020c01030209210609010e01020a020a0f020a0503030304060209130218010f0504080a08072121060e0901090501 87
    0xd180145c9100e40202c900a580901c00c541e00541400e1380d429072034a00104002c15440b40c00704070720380c1c5000480c405c1d001354003030b895444220749014000c9080c0c086c002e00c0f1004991900c044180000e0075500320101040d04028100520764680c500c540c54841520b4050380d028880e0303900082d402030150401881035104801c3c150702c0c0e40d0007031261583c03070200780030040c0035030480c1c004000254801d0740070b000c60500c02040342c40f1005001103441d040c4000780d141c2c051150000410480000c40c240210241003002c1e5008510b01000480d0080d2103281c800f000528540324030541d4401e55803424014800f9083c01000d8075a603081502d0101d00a50080700d00c140144c444d00d04481031140503109550000003400210841d84070003000444004244180c0f8000f403020600000c190a5800c120401c00107205402c045d03503440c09820000f8680e4103030760700130101a05d6400318801440e0301115100140480b07810303010070b882c0310f00f1020303018203c55000640b42001810801c0b0344e824054110005481c05100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 221772589 1250 221771339 221771387
    0x80c070e060f0406050d03030f0b0904030e0f0a050112020306060c0d0203071a040c060509040603060e01021804020f090d030c0203010903030606120c0509010f0309060203010b0715020406020a0803070309050706 92
    0x2043c8010384031144101035011030180d5007000424000e81007800c01d152184000600141c10900117280030f078003928240e00041164119400b541030902000c00c1c0680200d4a82e0000d81c58600001d220504030024019919000300104002d40c988805646a1050744c801340c446000b503c407402540c0f6003184106030360340811007c0b500e0994540c2681c4600070780d00210040c101c1400d001c816201b41e0b110f2009250019074950000003c1503251007041100c100810015071b580d1290f841d80420104013050180c42180304001210804070301c101224651702c8281c1d41001e00740c3c0b40e41019500304100c6600a5055401c1c03516040030140c0c10740c410700940707000362200034500f00e400c00c0f00002c8512505030b02000c188100004a80b6602a40d41d16111184510340405c04a01c29074070381041c2d810a0f40300941d4103c01148000410590104280d010704080c0c008504092400c90001d5403a18503002c0074116030030000114084c02c0c40386e00401c09080d08031044801d0b141c0c3d15000207200051640f0014401c480f885 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 221773839 1250 221772589 221772619
    0xa030e12150c0715050c130902031608040f0b04051605010305060f0108091f0b010801210308100f080f0c010c05060703090f0203010203132d0206090402040315020408010c0f08070c080c070e06 84
    0x2700c241c82c05035444810007962203504000c143c0380901c000c0c2090741c030303c40b070700c03043c2c00001d6204032482d440749120300050030b041c40910426020701000b0303801c820306041c144010044141c0380c101404000d8502441c1c03882c85a203aa10001e401e22a481041e140485414204560b010306c594002c004081400c2ea03d500ba5a03171b80c3c110052a000c011207040030515550580040860320841c022070b0409542001e600c001e86c2d5504070904403460719400000e643d0414000000098000d0000e5507911b4001e003081e03100c40700c10781d544030744510000303000d0824941c1d90140380080c8051901c2a140c45030380903000f190b503400c045060002200c0003140071110010745c0403400c554450854607801801c1044184460505155070070000036030003490307091750000e030700b804000045103c001481200510b24000160340341c0c14100f02c6421343d185401e55405229029400603082584506500e81c4140c440c45c01a40b00c0c4844d00c0c082419100d01c48242c0003911a8084c01320315441e240d101140251030032115911091054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 221775089 1250 221773839 221773841
    0x10b13060e1f05160c1e030206041509091424060a03050606070803010321030507050406050a030617010204140406031a040501020c0a030e12150c0715050c1309 70
    0x40c00c038a40015007185610b40803440060240900c00d102e00302241022105140025003a50310310054900b160a204200a0041c0c0d00032004200320b40b0105900c003160440c2c010408610071307840381d200d12500d1000043c000a00c00c1d116800500b1b0030a41c00d21028116414500101d0742c140d903000380d030b5602215080110303d090302d40b00f009118081c121505000c1440000d50003048000c1075180c2014040100200007034447d002540030f548201400d507480c9520505002042d02041d505400f8940781c481030103583d80e000310a071400c0b5500b82c5051541e900368203034120060070095200b824051585802c1400154040d0007901c2a00d244a040311490010034080100b661294031001c0c02403a4a0140c030641c41c20314080d1179034840c1c0100005450070301c88290312403500700c0c1500142c000400d80301131240e0038a8000036000410000600605800d403011150040080000d04412003600000a100040141104100e60b03688203964003003002d480c00d403000d0480b40c0d0048800040c0d5810307204d0049514566 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 221776339 1250 221775089 221775107
    0x60518090d030911040e1609020c150609010e040f15050714090d030818150103021f090b030714040e0115050304080d0b0f031b010206180c27010b1306 66
    0x7001d4041e000305031410600c401031102401240d018026047d500704403243e590211380003040c0207000181d4483c055400345050100b00040d01c000f007000b010a001d500c2d6200f0604070b0544100e4a41c03151903482d40e1902e407400445494004291403030f5016440e080c0780655206d50300c14455500ca490442e85884098211403242e0410719074030151410454010070320030614a84e01004055440809007080148240b60810f2030200503004840b0500510031810007400e098401e4510120000c1640c40c032001c0a002c1d61902c1c02032890301c000102c00070381e0701071042407003000001c0040300640d612911441c0c8400c00740d909006512100c101000b48a07001445441224462a0407041040c200051241304102921150700fa140c2d00c2580c0c02154601d9a505000744100d40f010100302050301c4401ca0000390034008020552011400c140141089001000c50745140c511011292034245801d0010f07590291014a40780c8254032102800200b203010350b8100804610901c1c02040844540d01c0b41e0480703500f10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 221777589 1250 221776339 221776343
    0x90506090a200613030c030201091a07030c170408011b0203071205131d0406050a0501061d06040f0b0406090e010f03020d02130510050a050904020121060518090d0309 73
    0xb601112581010b00d0001e01c1440c51401403110380740070200f403007003109a00c003508207440b00c480c086403c20856800842d00750040c08074400220b054042040404100d00408101901b4480302a50f42d00810411055500003054034480c01d80c1c46039142c0e86035034000c0c03485450407140030301c0d950804900b035070000040d1000e40303074810f02c0c031a400400384e902100c00da006415240055000035002007043c02803c110308401d410103012016080c43c00e803c080083d00c0c8007a003a0340c0703070602d0000140b010a600042410841c5160349a140016070201d0214100d80f01d50b07444214903440c20303100415441c2d10000180100d503055074543d00070380d89034030a07140380e80300c00e21030401a50701180f020401400c285100d01e900c00d00082c00c052815540501c804141c1c0c0c7e0445680080c0c000c0c0141c14002ea142403030a0070058101038610b1821890140c0c0080c00c01c0c0703407044084402d850680441b4000e1700d081d4000b90f01038200a80901c00030010349014128104040d9001401030041c6102041701c1480380c030400010603 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 221778839 1250 221777589 221777603
    0x2402210306010c0309050406090f2f0703050904020403060c12150512150f0a1505030606060c03040906080a03030f0c0806060d20042405030402040b13090501090506090a 74
    0x3440e808010740d602d0080d4201203091041c5180005910b47da54802c0d0001443c2d508404101024020b004000302c4000109469511500101c1652840c2d100d8440854480d8185405680e030303aa20300302500c80f8000c800c0c1c1268403900000c2c0100401150341c01a6107544880c0d10f030094500742c000009829998070301000f49200f400c01400304030b00d16000b030761050303c0c80d20b52050320462041c0c1c580108a01c901120080d00600f01c00080c0941040148251807465800c001082101030510740082e44500e405007040e03115185c0850300150345802401200c004021090081015654884400751100740031001900428a040360900000710a4050701000684c0b5a032000342d00d5988600b000595000103c000301082e580325806003550004544d0400c2250a0410050320740c0c1c50704000d6110b4050700005001d01103420940300000b02e0700301c130640341c020350304440104002e461140451328000c10040c0302040b040c10034002209201d01940404000c5000d007055aa059540d01071041c0d455806410003000c1c1d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 221780089 1250 221778839 221778841
    0x90605060304112202070c080d1404091a100c0303050c030106050d050c0d0c0503040501150503030d0b010323060901080c010f0825080a0c0305060105120402030724022103 75
    0x1511344620040002500d484002d66450340350400e01080340c104500c100c80700810640306100340301d0100038000c147c5416103411303080c010541100804c1d0380585d11500c0072407070b00c5900102442054514524000002616625051504500040c09003850590a03404a441e00b804a0040070380c41086034161070440d03d6252070038204d2101c000041030001c180080207101844100e440c903006000341507501020b6130700d1070b0b2079003450b0510710708450b901c0300c100441c00e800e44003c010304d84000c82910201611840005410515000140c01805035100b80c80070542441141a002809c00003210b0f005940c241d0700c29030241e88800580d5900c80880a42c1400316443c0d8540124281c41240340f9988001c00324010781d02c1040102102d03802c407002054110104900c941004001341c1a407040c10b0800c42c03540307030510407410003d002804034401ca039550121240030400003415514208589030040042d03c4800c0e50940100c40000d420030b040e1803080d001406071030f038812100b00c03400740507070081c0a200c29694a1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 221781339 1250 221780089 221780123
    0x7020a0302100e060a0917030309060105060309071806061e050f070c03080d090201021504030c03050a03021606060f080304181d01020304060506040b09040c03110f0d0507090605060304 81
    0x3010344800d006010000c6031620f41c111500c901c1e000e4400810992500b20300786003414260603180c503c904c07026060340d00620401002c490005112811901e0550741d00d07a8035225a81c000d401e120003904144415401804a003404440680c08907084425958921000007a1104001460350a184000e40024014482c44411104000007080c205201d410912802070b0b03259107180c1c0a4004582510786160f07140080402e658040c060040204041403040005140a0b035014042010b0000060b00304a804510911180e002c0d60455503045044003d0f00011a03880c07400c9406080c42c0d024808849000c031200240b001400010b980603520810001800d6400e8202da007802810f141c017040a002490299040109000f840118002d6000794004186442c1400911040e40d6132410030f01c0c00f80d104542000046403031a0024801e89600020381031003070a1100019402c4c92600342c0310750b80040c00c21600c0081150028000d422603540718014407015989108000e000d00003158003902c024440154025 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 221782589 1250 221781339 221781349
    0x312050a140a0e09040606090608060f0c0714060f0a1d03040b131d061c030807030c1e050304050c060405010c080702040f0906021305090c07060b0f090f01061407020a0302 75
    0x144140b0034580b030030054491000041040c0c0c800d54080c5c074951707520038052080c1c01d82c030300490000c0d014a100400803400e20007015426044001c088600600011842c88200311422030b2640040000074221241428100d602a80c041410b44501000c1480c04100380442d5080654001403103080801031424907152540d20001c981c055141c1d000440030789000407c03861f03442c480200842880e4040a01c0f80d290031020321811540a0011000d00e01682c0100c0b40080d50068005500c44980c0c81c01141c0e0000b49036040d1941c0981040002c081d60507a180700301c0041d44180070354481e50150301250000250070040c0103070b9100b140a078038000380400c40030402250390340008103230b450701c060000985411a001018102c412a400c1201d0260700002d2482408040c0708101c00500000c0b00e0a000c10704140764022901e103d296002440c140d124405080030b0f640d01a02240d00440c003074444001803402c43d0007522048424003034007000c21080d490702074008050000740e80c40241c0c064035104d002815a02004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 221783839 1250 221782589 221782597
    0xd0207060c1a0f01030507120b04020f04091e02040b0a031a040c0f061d010f120e011103161e05030f090307050a050d0e180a0b18100312050a14 63
    0x550601030b4103403400d015000c06088144190001c0c0c450181c1541145003032410a0415480030400c802e1a901132000f0480d405040d541055041700d0400d2a0850900420041d00310044040c1c40401c00709824052400c00060300003c45200711001c02050b210501040740781c01c82404040e1408244115681944c040d01c003106400c60b00401103484415a5801c040c006000290040c0000070419030f001403103011a410100c0802d0303403d092080702c3c0d0100780401041c80001d40003c906284d12600140a210405c2d40311800c115107001072295070f1720306129030520b80c035442d243c8840000c01403044c10340000042940740402c0356056842c0c610b107444083e108058144040e00c0c49420b40010001e10740080e06c2000b003030000030b201c0d40103424022040c4001600004402480368040c0a100600b95040700440c1c011681c01001801c0015051b8008404501c0b501e07083d520310040f00444000703109007580c4591001c01101c0c8250a040d0748401c0c08030007241d15000c0c013105000480d007450f08003920100c2d80d601070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 221785089 1250 221783839 221783843
    0x102030c07060c170910060602060708070e010e0d0605040b0609090a020907030608060a0f0c0f12020c16030b1b090609041109030d11010515030712062c0d020d0207060c 74
    0x200070b4810680004c0d0030076100a0768130401c60340c030800a814043c0b10b18050a001058140042d20803854072030f00241c1140c000a000c8010040d1008090840340c0c01405014003484014010700c0403803096190180017030000307444c02c2d03400440c0b44000a4152418026103481140440d01400240100c0e40c240305034a20098400801c4c10b8540001080d03010b410070a541c402d008103000400e1810f00428044210390060803501c08006821b0040c0510ba41c0080e01c041079103039520001a076586610424601302041840340c0c000403c2c2405000061055022045001e044d01490f441e030368801c400300d10383c00380c49a8200150404000d0241c19220b207415442008902c100d524664504441000000d0529560071600400310f56020510040355109101d041d0703101c0900070100840c10404000659201c207d8440c1800d18107101054404118294000043c200c00c0c88600c0c0c0412180e0705140090441b140c1001d0041c0d1150001028210b880090080000d0380c41d5000740075101d0412030102c408a55102c02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 221786339 1250 221785089 221785097
    0x70b04050312090a0c0603150e04060b0a03030215070206060f060a0e041b08010e0906040b0a06080a0305070201180f090c0203070f1a010902030f0a05090c09010b04050109080102030c07060c 83
    0x42215244402d060288900c0070400903000c034500c3e92038030701c00c825916003080c0d00305403601e90700540d00070381c0c4c0c01d0100c2990381880c4001d03800c1d5260315113080a45604007480f0f800c2101600000700705900001d82030140b000320321071040c4d965103c0c40201e940742d1046480b29440400f44038581090b003000300003424082d4003460010f480b41c0b15440441c058030022029940020102c60013081025405407126000d0416010603460741d09011644580d54000600080d107887d0310f0030085101409141d2040009058003400d80d4240811402c1c0908660400c807010780c0801d50b00410759007200070001d80601600c00d01d40030000e00604080c202c10040404c03d024005500c410448070010821002c44580034a1203014150105054000316000c1c0040c1a40301e050030705c0c014801c0c86800f040000e0190390000210720b00042e81c1e51014121454100e202e0240c3d500505000008104c0245c3d10006000365242a01c810003516a01c0800c1c4c4e00705d100444904480100900c035030400203e00f500f03c030801c5901850 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 221787589 1250 221786339 221786347
    0x301050a091b0e0438011b022e0207060e0306040210110106050d0b0a06120302070303080c160c0501140c031606140f06010e040905060601080c0c2508010e03070b040503 74
    0x81c08440e101700c0000e011002c40d2480040800d01020605081d8082072810302c540307002101800c042c0c0c0c0d42e4030704000c1c80750102000e420000119000c0c8903140403140b1091003091010150003a46030b0b0700034000d210004034903550a01d000c0c100012054022075015205411911140c001203d07494050003d5040355500c60300c000956035145805440018010546251141004a0500c0440306627038031100342c0082c108501d80101e070300442c40c40c041300d07010706004d081c6982e9501306802c940304020701140d80d40c110a51030b60900c02107002200a4960a0300c402202c002c03401912240c6000300d01d203030340490b401005a034441c2c0c10070303002c141e28040c840e420102c0c0c3e01d41c1c0c1800b04d10741d850303049030600c040d00f201c10300308800740d030b0300026541050000341c038104401202d40c4c4034584c07500d00080c21981840084404203c150307241400b200c200310b030124169240f45940c1c4070540e400002c2c17440000e030182c8400b180820400750600c01c0d440301c1c400010007103243c22855030301e125020000800543d4113000900c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 221788839 1250 221787589 221787611
    0x20108091e0312010618150309061103040512040510140421120810030201030c0210020a030e0c0603250201060e1611151504060510050301050a091b0e04 67
    0x201030620040d104006143c941081c00e52081a00310140d21110801c14600038604002943d802d5070415516801e89005121040000030f5005e810f202c100288043d01d4020015075a400000145019611030400e44021034a84001c03090a8002c7e03010396507004406800603500c2c54002e1003604c1c05c0240d9000304a08140d6206200d01d181c0090380c1d680380740c201f00070285408024004204d04004002811310b03004a05110b03500a1003001c0900009050598585c131000c0320500800004003c04510b000c1595a1511500010003400c40704101d110a0300c50313030400078510b240900540c0c0c0300b000c035064100308a020303412f9061511842d1083e650103655a4050110b6402e140e01d4503544568a0b0349200e0045d00ca40d02d50044c40300410142200d0140c000c480c000c411038004102a0740c00424425a003491001544c0c0044c000f450113504ca558082034081c03d00441c039800174041e5040700d80403141200069907501c1641d080d1051003040c03400d80d4a281080281c0c00d4020700701c0380341104001e04000b403000790b98 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 221790089 1250 221788839 221788873
    0x60402090a03050f0303040c0909080403170d05180c0d0b04020d0215130e16080402010815060304050109030305060a06020606060a0c0506070905030d02010b0319111503040519020105030402010809 86
    0x8004c120340260030010070001889074950328a03004002008080110481d140c0310085203001d503000c02060028014511090070318400c00380e40000c2c0c00c0110420960130549181c03c02070401405c1c1d041d1500400700f04448903d0102d44804075950000e00110090b6211703803c0001d04001a0400c0303130b11450605141d6075040d8060041d10306180814404c4280130304017a610001d040c0000c0851050420111011280307a03804641150820341c2820594165160704100e400801c407401c0314160820004400c1100380a015000320351003a009440401442c0c417160301b4000c00b400c0314000c0d1000f40c5e203d4008030343c16082c0900144000f40185c40c0c2110190095620349007420010744200000a200840601003450140044c100c404000c0c0004c10910384d000307001c02e45425a510b4240b0300410007010550031700c0f1562038105865980200f40002d034500b01240d6000c2034006540507203040c801c0618141c0c0c415541d1101c5450076070143c40d8581035a0b155401180c11410040c500465400ba10b81110800801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 221791339 1250 221790089 221790103
    0xa02120114010203211f18050c0c03070303050103291303050d0501030b04050606061e0706020c0304030326040b0105100915020a2006032a0d021b0c09060402090a0305 73
    0x80c12101d01d40310305113851b403c188a6113201615201d0103840408020200e43d404400581442030700380814540d8801300090703814061103034045198000042d01a04042d03040d031246d4107891152803c1c0404004100c0548480d00440207606140200752012540c00c49504110071140ca100c6d141c11032810359001ca101013519000e038411504501d9020601c000c00a0622140d940084161680c0d0b081920178100da86c00b0500705221f00e95410400120b80d01802441c3d01100e400c02d682508880d996640ca14006281e04106070480d800c48281c1d052406004405440950203141c001da50b0002c641d003810304005940b00c0803039000701070020083e4001596087c0380c44e0840c00e0074460b00903205100e00c90070200c498003841091401442c1466101c420250b80306000c1d6600081c8400a1301c0d80102540c0040c03611a81c188910790003101e022840e241c00442c24ac00a140e11803055030880d4011003a07841e6151703640f09e42500150700c8550300c0c000551504042d40074042c3c000d4002c004072030195882d1292401c2540b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 221792589 1250 221791339 221791387
    0x200a21020f07260d0e070b04140907090e0c0d150f1508040209070813060e030d0c0305190f0603061107020306062e0306081b010201050a02120114010203 67
    0x3401107486001d01070015180780d41460740c0504020001c2e040e03841092644600e00002d4801e170f03a04c0c02a41824a0100090806000c80740340d082d990350707214100c3e8400d00811602c141d2254a00200048001e03202d406414102c0e4601c0188144540310021031040a41040007000840ca80d14094858000c003011000d000070080040041c1c4884c0c01c26180a003062030120015003400100f50511005881d42102207501c01e0715440d000f80c0640791900c07600c002411041c00074012a060925096010300b001c0001e110024440d40f04200e40c490004094043d2001268541d4000b0140081d8a101c020b140e040481c5200302c8890008038541c90b41d6a80c022614200402c1010400201d00c3c5001c41c20301f0003009400480072140511340e60f201454518500021202010203102070021031880c0600940019003d0100201581d40c884200001e8a215420040c0324500541c280f00106101181034401c58142e002801c40310341c0140e080c040104030060328280c00070b0452008002d0ac461000d042044491084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 221793839 1250 221792589 221792617
    0x50a020913060312030204080303010506030c07140705090f010602101109040207050a060b040501030816110a0303020d0210050633040605031f1d1b130801200a2102 72
    0x3a055041c183c00104d403041c455002d15104001c10700c0481c0000040d24116202210107c0c2d40f5503940440311142d001c0c4290081154400811602000c0c0300480c051081d600c040c0d40611140d620003514108004083c800c0b10701503000b045640c07003003079120380201d108003502d000030b64075045180002c1401c0740c0c00344600f03503001e0300202520310400c0306500a1000c1e440084405015550650300c82100e240704492801d0a5401521180001c120904030203400005c0004c021441856403810082d44813924543e00c00014040d01c1810708a060503441401d01420024200744144424449020000c1030403022206611034840c02c0d921000c042c060092024090b243d40b12034490038404684401000c1540c1c800081401d9000c00340311100b2100169405c0c03240841404c0c12a40f508590aa00742c088404028070324100080c2c00280724500142c0d1401f281d07070b030400030880050488002140e019420102c0c00b02d10404200510051f0b104d205011300011340180d009514909a1209004980c48089009104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 221795089 1250 221793839 221793851
    0x41a09091611070f06031a01020d0f0c020a0e040203060f10060e01021005010801090201090605030603060403080a0b0a08061e01030b04060c0513091508031e1c0914010b0d0c09050a020913 82
    0xa5140c0031f0140102010172044210070603c00011b9254401c1c29801c000308030f0307800748655030f06214400d4031418036005800201d5041e1212907158090004940c164040d201c0d010101d203d603c40c0f5460b0760300c100100c4100500840c10042c04903007901d01c003400c8904604c6035000c144408401032049500a24002000007213001d454400500100b005071700c040140324080c003c1203190344000c210198895031600d00301034941d54035140f10008106106041d0742000c41d40401140240c800203c480c0140158151500c10361503580031918005024000100612405400701d800924150480c0140307420900700305007400e0079200201001e140c40e600c1a00602c1e202c84642c6a4182c0345000c0710080c01c0d4000255141500222809000307201c219224403c4070400078400c9140454603e88011188040f10305008400050400030100000c2498002c165480c103100c0c04207901e8501032000109900101009495140581210080c0402060f07994450340070400c080743c603580e40300e0b45150a00075000000711 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 221796339 1250 221795089 221795099
    0x2a070302030d09030507050103020706020409091a06060c0309060d020405090903071506080a0f050705150d0b010c02030a0609021507031d0102010608070e0a020f0c03041a09091611070f 81
    0x90109190841010f02c1211501400844d9000c20068159002801e0240e0f5a8007546030032802482240d01113054030303152211510070040105041082100404451740103501c401c0c042102500c1031007080300c1e00364010003004803281404006032a0f100c0d84903c00600341640c5602003400c02d20211034600e1950800242e43c4104040e0907082c2004140024040088905003040255500c00d015005000841d21414540c00c1250410444000e484054080b0380000742308071003107a098119040c005109400c000b0036402652194480c04045600100180110203c586840b0001c0140e810160782060079041da80100050000041c9080f07446543e0b0a8049140c50646400d100716441100341164107008040050080010304a0203885c1d02c0340310f0740036548074106400020300c074440450642140201d000000008044040c000701c421201071940c074609503250100880c410703a080c417903200e0b44940c04202e5100f04401c50384032000c0c0500f00062807a80080702c00d8a0b1041c5944030a46c0c0702c00f00441440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 221797589 1250 221796339 221796343
    0x6050403061802010806010e0d0c06090f0b0903061801020f071208090f0d050d2909100302011d03010f15060201061d01031202071a0d06060c02152a07030203 69
    0x1600d6a02e6003041d001501c07240d40028042200500901d040004003030f0b00c0301d0103540f03040c0e00301070007584101014a296960b13400078200040506c5822840741c500300000a8100c0c0c001c0c100d441c40000280585080c0c1c3e2000700308095400702400c3c502c040d640c00d100c0302c0f080107400c400410085014580080d040702c00c0e41401001840e00501311045508110381810310300000203444003803846d460400c0c2d51520020b44440e00200b028030b031061032000741c50a100b65080315265801e010103105450044140d42d0300807070700481c0c00d01440000e0007d80d040048200c80d02e03c0180d04148464020300104590407503a059030241d03004600c4c6118150201c0400700115602403141e40002d10b143d050a070050761a800916401d0304051201401d05643d910800460510a00c07001c801342414584a1110140024080501c3e410038205640034030301d05a00403690034090f000803d01103500400010711031a034041c040740a0f801180d12111060122501100b02541c4e02c4001c501c0d044803000140700c0e45142d401014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 221798839 1250 221797589 221797601
    0x60908131413110c06130302010c0513030312090206030403030f0f06140d02181e0c04150f0e0418050715090e0c070c0303110601051e011412010605040306 68
    0x1040003820728080414988451402400410a8a90000e4206408030303001c411031103030006030704280c019481000b204895451032011514080d50007000a80b1000704103880900c251003403041445c00380c42e41000024480c2c0703600428404444404907040d05a580420166081600c04402207500c1e0030303a803040c03000c0910481c10403121000c0244856890070040b2201503c031070344d115000345140c8140e882592901001060540c4800c0b03507d102c41d14040ea000301640741e0b908000ca50f80c07020b20011030140e80c9110160390940c1c02c1e0b139000e0514413248140a4460320170742003c240610411a8218115680e20311842d0030301401c8004810150f020b03460b1050416891b40c001c07801d0615203528013031001c3e92010303a040c20f480101802694544441000682d203004805004005400300300010003010352000c81002c00d280715104235200b80e6203900c01c0000c8030182c0b13000c0c02111510b20050203a150f2092a46c041180b811714481ca107891588555020300f10f100340c1002d004103000203010003c21549200d80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 221800089 1250 221798839 221798849
    0x190203010615050a110c0a09050a020403080c061e01060801050607170309030703171b0a0302220306150e0a0209040e0d03020a02150114090403032a141207110a06090813 74
    0x544404036a10000400e00c0308680142d0340550b0f80c40d0002b030030301d179101d43c101c401450f0011030180c0c0700c251000a003999600308680c04241c2d8452051038640501800c034204e81030b501c1d540c1721001240e00306018000389030007880c41a603021407201c1c841e00d080800e2000843c066141400035541d50340550074060865070781354111014001800c0d041046620386002008030140015450591300d481d103c40c00ca0103401601314090742889e10f20088201e440703040c52000c003240d12800050001084889441c4040d804c1c52080c60b101348280701c0040c80d521400e50080401d058020310020b540b0794110001d40c5010700c16440d00c2c1c0400c0c0e001940301141d036010449031408a6191003481410b40c1041811a0800f0800520a01401c0301c803010030704150180c0c001001c804c8400c40c00000413080e520708055141100c0c25110080380350b0940d03540352800d9002c21075403405560142c40c5900c0e10b402000b01c54000010a907110603020b44803030361000a07424013502102c07a00407450280c480043d910001402e144640c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 221801339 1250 221800089 221800093
    0x90609080a1719090e0703020705060a05062103030103050f0a0312050a1806060f080a080417030f0301090e0c0105160605060f0607140d030c02190203010615050a11 72
    0x108000c20040000c020300200e5104282d42e44030100e00601c000d072805915000c281c4032044a071802207880d4040052003c4034182c8024a0381c3da02c0f10b0005a08034810040082c255822200000303041000b10707086a0b0b04a1009403104460400c0e20892064401046d090480039800c000010402d01c0030403c050b001d10b6201c040035140041940d58080c2c47d504da01c0078400481901c503c00200c0101c015071010030b150f050340076040c910713071250301e007580081516000c0c0f18980e4010304008148200005441c52906a0003401c2c9841c0a0601d01c80d007408510080e045400c0740300810070a40f280941c0c0d00994000c120901c00032a044000c41c000509050f442d0420702d04000f81402044035820100c94142c15140d0044070004183c2c8801c0040345081a5088541c0e130000310000e4220b003000140080030000701c01c0c0c00240d84140e101c0e0340081741a1350480b011040142c0c00500b40844600600a541120304d200900020340d89036203105a84429200c1a07184d8040f174000b1500d9010150046410940c680140c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 221802589 1250 221801339 221801357
    0xd03021206091315021207020d0206011e09020f070f0f050708030a0f0e0f03190209010905041a0703020c010c0905030d0c0b0c07020414011203090909081213210906 72
    0x1c3c585a41031600001070104402c10b4014000c00c1460350440780b036a20900a8001140341104003e569500a21901e4006206000001450b00e0459228125694164803000011440c048040300a50411604c103038800008020038000201c43c942182900740c4241c140102104172410a5401c0c040079034030a60158004010105d4525445044014041241d0605007a10700b2100040b808800c0013072905034140c494080b98141240d40c040103924007030b10803282850030342e0321550004203540342960000d128004215251490b20804c11400e40d10031603500e401410310604080b01800d6507180030103000822503059080c4014107090010750f040c844541022a83d113220782d50b41e42800c601c010b082100c01400840d440d0215030b240c1e00218601009101030701107550315104000c0000312182000c9010501140c0c0c0000e405c2c0c200d00441c11030540201c2040c0c02d0403140308072007445071030082c27441642d91240c05000f800030702644101c07100041000002100c550f0b00038070151100e6000d80100050082c594 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 221803839 1250 221802589 221802601
    0xc03121602030432091812040807031e0807080307091e260703050303070f090e04120302040506070b061203090d1103030c0708011a04090f140f0d0302120609 69
    0x41ca945000a02e101d84c0c0c0f58088514414603030f0701445491106078002000402c1c841c00000900c9032426040d004010755580c1c007240b00c0a5142840f035071180000c01d80281c05c04002140820444202c007076104010a8443c40c566501e10802d03a10469040350044000f00500003820303405848400078100c501c6103844403810602072010404054800c0d1079450185000c2000287c808064441011200f41c0c112686a902c80c0340030342c0c0301d8104a4801d00000c08a42c1f0207454148500061b4040310000e10401e030403500c0740d4031025625101d1001200501d6001c020007e06900e52900400c8003a00821141c031542c180b010800080b64404060b2082aa100748401000c0f90303500b0003c043d1081c0c0c4214250021004100420704600440540c610300b07018444000034a00010b4201c0003400303003004c0ca0449050400e00070881190124400982029000b06041c000214282501e0200758031410440300003141c42d20700c2c0d0745007103800e0701e400c0b00283c2c0120701007240300707511140303150070031000c5031900010310340a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 221805089 1250 221803839 221803859
    0x41b06020d03061a0d0e030d0c080618010b07030e010903150b03010b011e0521010303090807050a03120503100b0d09021306080303062101090308240303030703020901050c031216020304 81
    0x40b92a40c82c40d280c2d100060b46d0707011410400c44144201d038800c18440040582406050280100d9240740070b20f03046207a010b1200d0354121704a040e00c00d014402c9043c21001c0d00d04440d00100c1002c2c41d814418208404404a0740d03100b4132414003c2096004211041c1c4103090500f034801d600e61a81c10b226040000d1080580940d401d190180c20516000e80c0329108020782111510301d5a0101c141410224004814194401d0040c0e003524403407400c079614196200d05012207040644009080070040c81d003c107120034480d03c0190b80182000c4915100d444d181c59510a6a62100c031036190300d5541c1d607280004604003170744072017102e000d4101c0400070070745400c03c403980368400180f406100700100c1044001012a40380000c4540241c24000c01505036035180140050400b6240758030011103814401207a0001c02c1c2d6480c840702409009941142c0351550160040d4100914142c18013005001e01c040c181800c20203002c10000d06079641400c1d0402481c0701e16423910794001c200441d0800c010901c042000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 221806339 1250 221805089 221805097
    0xd061502010b01022808030903042c070c02060c060108031b030f3007020732060906251209140d0204020c0105041b21060203041b06020d03061a 63
    0x8101c01035030345e9035800e902c40021003000c5180142112004018050368031800006001556050348141140c50441c0360011884180114a042c201000000054890307202d074080c200d5407407010b00413038244003070785c10000c1c01e0990907000b48140341e10210b20408608400d410401a01510301f001d1450517082c0341012140340b095508031000001d03160450340303008400050300540710303039089079684107401d040d03400075141c0d80c15100d40c24201c510fa400040600154800c0100aa02d0100051203034600c948280507054002a141580c00708088c00264440249104502c844078100e0b071940342c0d010541e141c072910b0782d040b4521400412024032400e100046c0008002200c0314011503a21821a00502c00100684110300d88021103509240521080000d045106110040100300c040c00c03050303c1d02d00000300102d1160409901040c240d0341c800100c1c103903034002c540003400b5035a8405146006014844c0e5003601e40e120710016071000d00031042d01075040c41001c001e40f070040328880c00d6141c51a104181805 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 221807589 1250 221806339 221806363
    0x190c0c0b04060b0109082e2304030e0303041d010602010501031a060a031509020a08010213260f060403120b100302091201050c120906071b0c03080d061502010b0102 72
    0x150f203c200001d207a00400307100005020a10443e00504503480c9145c203048401c4410080c004511f0540301c6079203109004041c0848101c1c90707144034440b4005195203040a01400540c1403044880981049440910040c0041c01d0214500e030004008900a000f108005911110031a40340400600c00140c48028400303580300300d4445850a40c8490000903039071000c41d0710042072280440d850b031000c80704603001000d48600071104c0405d502d070341e40d440d1801d0380704e400b68240040000c00390602615100900c0694039000721410186500000e83e10356181107207034440303228240d002100300000c00d9801a4400c5d00600390304410700c8513015100c081640010800303948400d05402113540c481c80c0c0c1b02c1202c0c14100b04c001d58024050384c14000c6d42d0104a034850380041840c08019000112100000245a8001e9419a5891003030341440030f6402d4034810250300466030040103180c000007081001000c0c00c0040860316001844a1901001104264405ea405825a4100214500741d42c0c0c0104141031700103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 221808839 1250 221807589 221807591
    0xc0308090309090103061406030a0809212b020304060f0e060c070609080c09040803011e090207030f031d0a060f06171b01080123040b0405190c0c0b0406 67
    0x103151916640d0841c00340e0030406800100700c2c0000000c0c05000c0d013046102e40080034418800f92110814107880388600540030b03207003001c20002003009050002c0032290642e0440c2d00c40482048401c04181410503801c80089103000e40c05540481b413041c1401c01d0002031003400114502494000f0290004006001840c20320440c121030458a441d054201e602c421000b10541710001c2d00c84601411110090080e45802c1c8901000700006051442c40117000719001000c0c141140c3c07130540c40034511032008440c01c89115198000003107050f007600142501c10301c00d8441302980d04188800070100e032426980300100500e4016016480d20340410a00c8001c0d800c01c00202c0c181d0401040c0002410712a1710406c031204080c2e000e14034424021400514403000c42c01d00f1100c6420500046031150002e000300e615601c4490524411000c0880a40320011405030010070000d20200005040303540032902d02c50403154076914801004580d01c144424441c060603e9400f600c1e442d01c0322200404010700c002c19103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 221810089 1250 221808839 221808841
    0x60408061b07021c0510021201050d0c03140307170412020d020f030a030c140303070207290d05041208070e130b0303031602010c09050d03210203010906030b060306070c0308 76
    0x2180300c903080b2010039401622509000d074004580660810102d1400d0b2120b000741406030b100c22105000b15002c141010b9036614583e42020208060502d000f2002c982409030440d0020010f241072514040640202c4040d503180c104038201420129940342c0740c0001071008010038440040701d51404c2c9192030b019500c100e00380889101196079084503103a00ea9040c81500445410154001610050070b440394420100e440403c044050742e0380070036950701002d41c00c40303001030000070040e4400824900c0244010029107010094200c5194050341c14a00d05548400400080c0003601c588810003d0b03061034003904d540390181008209002c404e16040c491540560011565611604020f0000c60028290307a680d081c41c42c449022900c400d5031490140d400d0105804001d4000c94145040311030181c4661a0321600c0e5508540c0089001d041c250081c1141242c2c044076907451000d1070103040034a40001d00c1500b5030901c4040240e0042c044c1e4801d500400400c52450fa01c14205e2543e035078107081c80121 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 221811339 1250 221810089 221810131
    0x5060d020a0c1502040503120903060708040303060306050709060f170106051315020a02240316030e0f0d02070503031806031b13050a140907110a080d05010501090506040806 76
    0xb40c1c41d00000c002d001c908a00c0c103104020f5030154004c0089400440c200c03042c69004110a090a002c1c0c000c00315815000f07500090075150007400002da025120749130005100d622a611941152000c1d20b411000903c4410b007803080d0303500543c1301085281e5500305003e0791107036500d03003111003101401030390108040856014014040007050714040e068030f8180304e442002409009540340c6180038260f108581075400406046004490444016080c121043c510703070310003518442c0c0d080046200c5e400c15640d400c074048064030a000c000070044501c4080e0010740700182c0c0080c642700303050300310901c66002080052400c2e00040c103803071040070060340c0f00c079165038074110081c0b8106a00210f203607844500207100a003504030100550f055034811901455400c0c0ca98515035041600c29604542160b90080883ca001d03005000703a080c007421100440c2c013080560354032010141c0012980c500202e449500521940d81c2041002c0080c0405451543c10310340b0b4460344680d40d4502520119800c99400750183c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 221812589 1250 221811339 221811347
    0x1005060a0909020705010218240918040b011e26011121071403070c0521030103050c100903030302250f0b06100c060e1006080d020d0905060d020a 64
    0x207100b03078001103460b9200d60400f280031350710502980c254030950064611040c0341c0440380c0c007c02c41d10001240450290300c54a81801d900c103a45c3e0580c051024900a0070b80c0c052003201c1c130300c40c5204e03441c205525450481900381c0c1089010400d551100701072414081d1807070403425460858008040030f0702c003101c1784804074014403041d03030f05070345c0f40c40001401e2841d4444c000402030104040c0340c003000c8d9641d4460046849480c8480050040482000403a070782d24456500111014020001e45a0408042000980c20403004400c0b6100400c0400104248071080c000c2201d040d9051b42e40100310030000c1001003040701c2c0343c0402014940c0c04281102485000c46042d036561001e890060122a0141412510341700340000859156440c0c2c000248941806020016555801e0702c550201c280e05a0716600980761406440e403852181c900303583c001922034007880000742140700180c003540c50701c4280207080001c0c40515009202d003500d401c12454462200302e0703120214003d40143c60358900c0d07900f1a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 221813839 1250 221812589 221812607
    0xc040801020408030703090f0303050307030e150a1e0615230a031a010207050a050d0501020705030a05121005090703020a270602100b0907031119030b0a0e1005060a 72
    0x241266202040100b00300d14000000c04040d0b011344c4499007401d50352400403c803060680030040000744c0a101041c1070718043c0d0449140840d40005507102111f03000c100c04c82d00b1404803a9110310036201d04194999181066041199640c020701c28845141050554540c0201c445042c10802c011100195043c039481c454a00025060550355541c440f20810010058140c00441460001c507004503800b281d8000283c40c412200e018103614003151600003040310200c00000d0a5509540030070083e4000358007070000705401c0c505034a03056110800b81c9070389415000b000340300c01031b40c0f120701005201c15941d880c1d0050f0321441c58035015945448450302100d84a66442c100c2240840119484041600310500001520919801c54914107946400e41d01914640204c03590813010f90800300c1e450520a800c055640e02035010700c6458000340d82c0200d8447e1007204140b2001a03684c0101c4101c030300e0907880e1407005280f5001c440c492410403601c1825807070018030841c0d20034500010145078150040c407001e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 221815089 1250 221813839 221813849
    0x15050108130b010f05090106081614040305060a0f05010f0303020327100801150c02010e13110f0a080117032b140901060b1306030513060501080307020112051b030c04 73
    0x950340c01c3d65520030300700442c111070242c148a0060040041074280c40303845400c0c450012180c2101c0804a10002910191010a202d0715260320811001c404114100702090141c41c1c000300000d4020716100012084680c11382201c01d180ca00c01c0c0040010990000940c0c0c17110301d000340b961001c0c408240d5808641d0000104c072541010b0603144101800d03400034101d074106d4451100e00203a90170100e0089070900712010000380400c1e003034584c0c0606410020150700040442e030704005641c0100c00c039140b00c40e0b001030380c080524040c001044070a940d40f24280302d00501e0035004030205000c403651200c0d00d9000d45808032030900e1a11303586162600c0c41848400c0d200610b003508100d4a40c007400e58003c2003108880ca01c11941c20b01200007404036901c0304031944031145410002060341413120490107480080c1aa124081d4117800003400310301c252286500a048000003075960340b07110300c00034001200001d400c1c0412890401008261948140320b01c0415060004155895a88000040650095801c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 221816339 1250 221815089 221815103
    0x60e01090f11040515060409020c03090607050d1404030f060c030f0507020c181e100504020f070b060103050912070f06141b031023120c040e011505010813 68
    0x510911841214550b51440203690030300c244d6468452000b5100304001a164100f6020441008102110380c003904950b6640c00c00d0740e00e0160a400000c0441e00a03620981d1a9040901e82d81031117904070072a045c8808a44000038201841c6403030f10015041038000140c507550321041c502035182e100760321101c0c001c0034100c810042ca00740709d0b60082d5104150091a0300070b50004074521001c0c100c20301943c0c840c01300e00103003442604030b09024026209000e01007646480c04607002107400d039914005086c0c014410840203031602e115040056040102900c8241890302d440d041c4070040c14007080c00081803205010746555010301e0701c0c0c009049800c40d500a03000d1480c20406241075101c036003030303107002e4801c860510303403e504520000101484186d601094030b4480500420000b00351840950202003000601419240d960011640ca4004a55030402c0c6070801e549000309440c0600c1030f81c06044080c0d000700030507440c10500202042139070142505004800c0c0005984540c1560f02c0c0750940c2e0710141d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 221817589 1250 221816339 221816363
    0x301060c051011090f0901050d0f031403040503030a0b09072007030206030c0c070b0c030a1412090d0315080a02090c0913090201030506120a111f0e1002010216060e0109 74
    0x10700202980010400b10321840801c8902d201c607180c903440e507034140d0300018221454003820b99556080cac000280c0003141030110090000184c00320040145203d14001c001440d92840c10708103107070844448c4240f803403140f00c528082c8402294410040b440ca40380c041c6031600500d031100b10301490444c841c0d00c02540080000104200101c1082c06001d80203010011110a25200d4003149868094881c5100303495000703015500141e48584160080e440c1e000106030701c2c20082d0350031403600c1071007150120301550004503004112039061003070421210045514020042c1803140240d00c400117098040e00c508524008903214600c0c000071035804440040c540b03141030341c0cc03400c5040503181c2410140d01192a0400140181c242400139082011130314010b052256900e6840c07046034803038490754541110645c1c1c070203052400100d00b88280840580c8030a000c818901080140d010210401e00d02103900500c80569002d0165807465400c40e4410004a18205280380017070043c035036403002503c0c10680130 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 221818839 1250 221817589 221817611
    0xc050613030507080309060d0209060412050a03081812130503010204121e0c0b03070c05060a0e1603081b0a1a061806060306040c0507060507020d020f010507050301060c0510 76
    0x18800340c044900c200165554541c1d5203800507168020405041d030070003000c003c501d120030310710b5000700310503040108001c2c105911030050400b00106040116102d90000f0801d40c1819000a4002e601400d00e64003000c0b40b014450490340c0304c6419621841c070050001c18a10010840c000c541c0d0044e0401400854840d0358940454a016607400429601054411010f01c501c01c103500f48000115041101c1c810864605850f00d4403a42c002080c91041210300f0f0340407000603001340070781401a04d0103076010800c41001d0041c5820450320080c1d03120001200842000000c070aa800d940b070405924280c0049180e01d08000342c10031420610050051031040d41c042c0307581025400140c020101074940c03056900192907201c509201c1580c21a03131040003800001c0c2d5915141d00011618940c903d0414200503050703880f0010348205998110243c0c012900b008540c1d0b40c10001c102140d0348200091050341001000a4080c0c44180070743c104200c0200009014000208064141c8245801081208013499 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 221820089 1250 221818839 221818867
    0x90d031d060405070e07050711100c0f0804090b06090d02010e011101020705030d050105061204150f0218090f0403090e0a020c0d090f050d15021303050604080a081b0d090c0506 77
    0x500a020050000345c002c034480c2031040b41546e110540c04912002c2c1c0d800700c0010400c00d00140b0720003500300014105502d00284101c280400c580340b040100a44407400e2031641c100b40d07900164501d0250a0078802c9014541d42c1446d50f000c1e054080c00d143d04048072050049460382d078095000d035820b42c00050310008200b07001005084210075a031080026980340e504000441c41a0040c00503a200502e004c1004900104000b002901e003c840001b4091030310f00700903050340c11004403407940e02c51003048509542840d821255210461000030806460030790703805861181d40b40203041a9003a41000603500c00306e2a0b04480f15100c1040850300d28041642d401403480c0800c0c000c004207121644c10004035070400c0d884004d00140c0c0440c550135074030708448a08000390010409024400b000d003c0001c0414000d00844e070185010321040c40e518400190042c1070300c84040c080d10065003030180d200c000700130132606a902c810016840801d0203045410301c984007014640100340c1c000c80c0040c00143e44008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 221821339 1250 221820089 221820103
    0x2070504140105220209030703030801080c0409080313020102010908040e100501030606120902130203240a030c0e0a06031205070b010816030210031401180e06090d031d060405 77
    0x10459050003206800150400034000070b10946030003403103804142139229040d60008049040307400e0014148040c0c00002498041d00c0d138000c1d00030902510061000d4941400700c2210300c0c0c2c0c180c909000c0e0400e150340f0002c0ba480014680e92444110041407011680300b034011070f01854002a02a0b107030380d120104424446002e44504c01c1c070044000000030154080c0c0100c0b022100789441347c0711000c1805400c0c0c405000d00030350480e80700d0b04000c031007603c60310a417000e5805903041c44030400b0b6403081401083c03c002c07620700b9004d101d84000801000010761720f030100800c1d44c60a000c001916250200d545001d400b0300c0d003000345104010881a090f4560000280000034041e03c0c020070a40d0744c03800983d88941d4600140e092580781c1c0c040038400f605080e90b142824007107510300014203d40c8924400a00071007a0000045080040d1081c00504580d006907288600ba0300007401c050301740415003903070700c255402c4600240747d124180030314543c000100e44030f5160041403d450007840c185c03500c1512201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 221822589 1250 221821339 221821349
    0x312040819030b0a09090c0f09020c1905060106120e06090105090c0a08070b030403020703200a0b0310051207031502090306010e090a1b09020a020f0105070512040b13050303070207 79
    0x1500c51000c020280c828019150740c183c001c1c3c800451341d4200f840c6600649010681500d0380748a4640004440034101d0700c0000a04401200586039440303200032170f05011000d80d941b08000c10000f03845c00814008114581184c4950424411000c0e094a03180043c00d10580c208156000e10010044441410b40199200300900001c2d502540100b40411544040d24000e22010b64080d03042880054880c200541e003080c000e0045916a90380c940d0380d4a5801d84a21100c102044594403203150750500802984c043c01c01144524150710701740340d200c820300559203d4144507400e034100e0071800351300c1440789070050340d00301d00303510f00b0700b144e110225000e540400c0381a8080c0c410f102c0006241018040c650f4001c0c20710402500307810001d51241c0b2401c82c0741050300c03582e0b03014100002a1810b60341c03004100300034058020300088201820090b0031208018581418880100030410f00c100c281c20041e540190701042070140c1d40c4032400c881d81c044840140042451000106012445030002441e8040711 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 221823839 1250 221822589 221822617
    0xe01060602010f1509050a0e0f010614010c050d0e060d020a050301030c08010e070b0306040f0923030a02071809060c050c0c040b0904262b05040f031103120408 70
    0x205181d81c3c08003280d2800c840c0010940940e00280000390b116001560003a660000205008070341550342400c000c1100790020050303654031400c01c032004100300b1940000d817007400c103a003c0801c13645a4503128030918000303200704103094500c41c0d280e6a494069424a01c0480000c640728000408060010340c020b000540b80502541d1000034410b030140500503002c42002c0c003920503903190001c111803e4002510043d030040d140d0601403203590052103841829406003001300a250f00d80000710812601d03d20b4102c00e180c000701700c0100301a8000864204a03840040ca00c0c481c0414249820300400d07040c40300400d000e081c9208840e002e43e025000d0300e1103034000303000d441c0300c450800200812940700c48030341508a590900000c0c0401c1142480010310140c01011840486d100c0c0d850701c1c0503521200d00c49040c6000c6c0c102c1c6804480007646064616450070004007c10b0819485074099415110780080400410000d444d01e0f24600f030003030312554902c81d00a40320504052405400f150000c8103451010303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 221825089 1250 221823839 221823851
    0x2a0f0503160c0c151107030c030213060806070806100809120a03020d0c080621150a090203010603080315030c0609060a140301080703060f05070c060c170a0204090c02070b040b1602040e0106060201 86
    0xd4002084690807a41d006200c107080d68692b5091180044501034488540c690f2028006101030091000a11070740c0955520000e6103020303020044240500d017002410000b000040080c00440062141c080480b9000100d8807030304111421000381c890034003c4107860b800c0070148000c0a03000710308103001c3d07003044403600038092030000b051405100340d0841c000254058030007450b01c240c0c003040d5160010308410000c0340c9043c40c0e80100e800d40b8055032003183d842c40e0010400c003e6481381c1c0c0700d5120800045019125441650f40000c6040c041da101e075a105100001e003001d135450045c881c64552017039607000b4036240d6945041068035a8040e1200b43e81780c6d4200034074503005070407034468107100e45019280c2e101002d4050320784000400001e0226420f002d0380c207d0710101030070100510b0b41320399000c641c0980c0d90f034148107410081e500c10f1034a0704103641c008541802545215002d4038280c8510350401074940d83c900c0701d00c0403021341c10380f00a900070346400b14511001c10107400880585106030000d00907 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 221826339 1250 221825089 221825117
    0xf15150305240907050d0816050c04050a020a0801090203100e09030c0d090e15040204080a0b040c0503060919020a0b040602010e12040503150603010f2a0f0503160c0c15 74
    0xd05142100c0503d031a400540c0c05110503d044001c1072807032030068100505150300c407980190007018400e03040c2d4043c0c0c03102070f8104031440e0030302a680d84200c2e0301d5801c1d03080610b80040580b0051040c080c0d0742601e0b0700132001036220b000d10509400144602d003401d040b541401c600c0b290f00ea81c4000449402c1e400b85128000c00103006585141c07c0740c1e40c002c4640000c0e580d01007842d0078a150101d00c00c1e0b0061b020800090951403c2160528a0340503c0c46a0050b0078589040c5240300903d41c082d50081c1c1000081000040b0080b4101700c2c03283c151840707450b034031800d440040c1c50861642c00c141200d51001c00d0100700254154404105181038204803102d504410307560601c7c600441c800e2503890f6002036225142d000140705516004034025001040c0110140e04810a440c05220624046083c44001101d03a0041c0f02402c040710256051003140501e074007800424510004060101c00042d01802c011041c1c4290100c3d16900c0e000300303200c000c1985070080180c402d501c41004000040b410704418503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 221827589 1250 221826339 221826403
    0x4080408060a021908090a05030f04080f01050106090b0c0a0c030605180a12050c1513020a0603060303050f03150d060b1503360f010b0109120f15150305 67
    0x305012542a00000300360780b84c0c000c44000c0c0005004e40c241e8002d0188480000780200091b15800d06008010303501ca5040881e11072034181c213142003000b1a8180001000b20641022103002590411003d00c1d40d0744030040d404a14144640c070f002010840c5010001041c4155507121074003401000348103400f17244a00940b10f585400000c070180104070510b40800907140160001c0110213418800c0e030726036500705003070b912004074101c40780c5410303000012002c4118a006000280540076604040194070304544005040b801195004220a07000002191000769a001c182c048560010014a81030a2038038100019003108084640142002c80c8280309988006084d03130b01c41d600001c40503107068110309034200b90103649100202040644000000e010200b0700009072442400000410141c42c100c000410003034450780074051080050b0641400200b030542c004030082d030041809200c00f14412440c40c014021f1482c02c0c141c00034100000802c12401040c61072071054400c18041c41c10006030344040c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 221828839 1250 221827589 221827597
    0x81b0706030e1c08090a020d12090b03152403070903050c06071a100503061e0a110702010311091210140702061317040e10060302090a051c0b04080408060a02 69
    0x710f124060000601c90071348110400d40d4050296000c6030140401a00821369201e1178100503561100c65441c1400880d0300b200c0d01500416280403c0c6140d45841d17030880801804400f0407071f02c01c0d0f0907420708107907a080032445240c0c031506034003c0942c3d034140b40710302410301d003001d201c100c645005d0310803101c41c21301d41002610691074010034800380601002101694100c0000c201d003000c01c2c600708010a140d201005403070310840308010041036002c1d1094914500c010003c14900b015420301e041c50030b618449805403032845034282004a10340c001025161120700071264540d811680781040361105440c001002919801d920300c0802404000480002c10100c04958400240c0c0c059408220001580c42d0100140c81c041c40b2140080484000c002e0703002c0c2d202e6400412a4401c0e9414407401110310410140100503a0408600c1d129042c00420443d0b40c052190a10603c02d0548280300340b5500218101c88a900080c3c08409260600c4e05581c55005406a243d69109000005882215501c00c032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 221830089 1250 221828839 221828863
    0xb160b2a040b0a08060607050a0f03080f010609030b070210150303110606060304021903020402030c09010e0f0306150d0606030515010e010b1b0309030f060619150309081b0706030e 79
    0x510b10f012000101596580c50140900345c2243c410082180032500070700444401c64411281071300511242d0a0003071030124068240035046492100410120342c2244110040b01da00a00100e00303503681c0c010a034148070044000228050070f01c20003014003143d24003100240e0340300391540800c1700050840241c0c1c84208454641c2c200780104045801341c80c0c14900300d003d524100d0301c850100e54890340070401f0b07604151034080e51000045250380d62980c2254491424050030b460310401c0c0c0c25a030000aa81b400e0280c0b040e05c1d40558030709207036215140c1c10360b0111080e820050511006960703240c00c1d641c1e55283c40998408410190010400c0c03900380145904840030301d401c890900c0788003103d94903240031811504042e840200014200c50318203010440c0743c41c1d0200050149460840280040c8031308640c45624000c03480103081c4a1070f051100710707501c1d6521504d000070301d00c26a0f00c0e21010a100d9038091428510803e031a040c4c1c0568006131400948003643d42c01e01210400c5010349a44d903441d1401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 221831339 1250 221830089 221830109
    0x1502060c0702040938010803091302090307050319050c011e030506012a020306060607050604060b0a120b01090b011e0c080f04030b0a050709030302070b160b2a04 71
    0x1801c409464260007412a180c05403001101540104084801c281c490440840c2400c070074070040d00f072441c030f14010310f4010204003014501d0960301c8400500c2d00414070391081d0303200d54041035050864400f00010000b82c90081e04032081c1800004c1103161203043e181080340d41d8416103c580940794840d440e82070041907141204400004010402e4001d000001c100030b0420a200300c42c40e078904100c8031900060803615103e02c04d01c44a5005040c00c108004100c180104001c0003c0c10000d100003074401e600035006000040e807041240c0004018945a508c6409c9242c040304c2100700b403010a0005504840314442c00b00a1000e002005407110701c0d02450180340382103003240b0003064074040c1b250011428829010249440c42d40407001442e60400d80040d5040100c00042000003100c5200e499048861428a13501c11440c42d9402036071100b00d070007240024032020643c15000701090403107640a0303500c0302654800345400019101480600021000103410380d00e0403c09042d8488203c07425a209641 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 221832589 1250 221831339 221831347
    0x120f0903050a051c2a0306230f090702101407141c060f0306060b09100f0e0306040b040201020c040507020c040903020f06040b010618050604060e281502060c 69
    0x307001e80c3c49802030500d580d03c8081c204131020303c0221600c2200205d10f0301100c4244807985940c03034402000d582160140c00c0c9490100f00788102000120007000919030044514040306080010036085d10b14106080d41200807182808203d5070086140441911800010030000300142c100324a005030540c3c0302c4004c101100606442010030704010241c0c0b19181c203031401002c2e01d10701b602080701c1d00c076441745051a035643c2e001c2c020441c55004050061840c003038501d0901c040c640c0015030310102e0011107000d004130011003103411b6004c0c9094401c0018003d054554501e030904201e802100115400c038010302600c0c01c10055841d141c890140a0f50441d4010b200b11207089061200408804400f82c0c01d40c4144585030880f180c04005086c0300b40d1288448107425490400050423003280c5c1c04d44020100c4060400b400a9101d107030581d41118030500c3c00000c2a40b1080102c0d058298101120301c03a404a40d030003400700c0d180f0b41107840844441040c5e40325510419181243c40344419514110398403400c02c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 221833839 1250 221832589 221832607
    0x9010e040b04140405010c020f07050a090b0a09060f18020a0207031709040f1409120702040504110603070305010e101d0c190815010804050303130501110a120f090305 73
    0xc0d00c0324140700e0740030b040061100d14440c03101206100c219030880b4241c0d100c603801158942e0522a020b0305894030b40c000c0c142103007088002000c0c04524001c1e151125610314a14466944800051008020040301000090744885032a110006540254656010300004151b40650b00b40300310b42c0542002c0c0c0c05070103540d096603101c03c0c45000c42c0002c0d480504e01445804215901d0b81b0410480c4207401c01d00040b0b40010f1101008044d000600400030742e00140388111070071010b4411248070f640c0c1201d00181a544604d480308941072181d41f8150440000f00401030000c0e015404227043c0c0d07804000028455850566100c0034203664010048008160011419000d141030744003a00603031203c424600700024084940300d51a002c40c81c402c0010000d0003800030341f138031440c8501035210003883c00c1d007035038903040d21055039a22000d42040c980c48100c1c02c208007405401c0d1f004400700c140070340590fa901d10300c3c030300020080b0000300045c401003880c10f60161100e1401c0e1154054055041e02d038035051610503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 221835089 1250 221833839 221833841
    0x618050f0f0103020405031501080f0c060a081314031309020c1f0b09100608060102010c1b0c03050601080a0b0114010c021c170703030e1615020c0a060305061509010e04 74
    0x4501c4980c10326400303010114069a0600c014549004081a01100d540c50a10150302c2c2200c1401c44081d9a080320160030f40e01e8031040c1c12a8034034101fa04181103c1c4d190010301c1c0383d1090a006000e00040c0210b101a039911001200800b40311407880710b403c03403180c1c6500000d0100d1150540b002c0c1190b10a0300450a803a030007480e010b980145d8000005040a150701c040780901004880010fa181d80350401803000036081601c9a0b0401401e10081240780362264014003e00c0c031200040341c03807080e02d042c1203080200103083c00c2c0103581d01c01d042c3c5a141d40d45a250030b0341c401d00d009007120300715107201c004650418080c030105002d090580d500d110b600c0c800e4003484040c4030714100e500c07009195001e003040072035000301d0b810340e4400680c41c81a82d03078011401c00400f120201030f041c9056401000004507880d0810201005542a03500d191605131000b030003c0c0d2603d0302402c0d000d80c0141150800244243d01540814420300c0161205d018001d45081d224030340c3c1c0b05010300c490110b2040d00354582c05040c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 221836339 1250 221835089 221835109
    0x5010e01030605180105150f040501030513060606090f080f07060c0f0501090b07030f0203060102071e09050a090314030c03071404081c020d03060305030306090405250618050f 77
    0x604002820030f0b2107801103003804e401e0340148645555001c004100900705591290340f520488819182410b814014566003849184101c1d81010b45420114284500b9107840441c7d940d809281000b1882d550800507080c0801449401000d04c24141700140403000416030f240251800b101400160b81000000d58107800380c21130681d070b920040591100010320910500300d195000b0404085a40b03051100241034607000419081501e0040c1309108150360001070840a680d1503411020811100ba0880103140115074080304101e030405061100d001101c1d4040e02c4424000d546048400224808425207031009075500c001c000b07002c2000415540c4500155000c03038000d960700520341a904c0b485a0725020007540f90300c581031100c401d001001a0100070314090b15440707040030b0140c1403540d101d0503280d01000700258040c50784640007a08100040c4040d041008100014a0304810f117501c071601804c0031402a80e000c6030407601900f000081003010310088600040001c0c0c070441c096001d001480745 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 221837589 1250 221836339 221836367
    0x3090a031b0b070f120e0d0609410102031611030415170a110406051303020a080d1106010b0906070f0206031f0b0a021c0207030f03081905010b040501 66
    0x40490404100c00d240742c802401a0b5005081e2032109034401c2c10b1040c29402c04038810f00074001c041e2101c5600e80c90f5034100740400c603003041000803a02d01c01d00309a0303d400c0680010004480008408503400e1040d030103295400a0300700c0485034100706040d141400c030704c010b45001454544104003c48002c0c821514001140ea0bd08180d030f00300703541c0d215040000c00e415440d08010500014a00302c90180307041c0c9140e4000c0c7c5640083c45426000108003020b44038900840d0200040015442c4080c607503515070100455024141c41200e5aa40415a40310301031541e48a00180403030308918034581000a0240c140c134071680c400c038a001801410843c003136005000403600c040c810201580580c2d45e60004d1446401000d944a0700d100c5c004009160880050300200b060f06804c0c031500302c440340e0006902411820301201902160010740d01a45098542d81c070080c2803215000a060405610a1186009807269034250a203a140302c15900309441d400d0044040400c802d00c02000340798401c1342a020111 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 221838839 1250 221837589 221837633
    0x190503070b04080a110d0905040b0a150309120224180105070206010801110408030a0309020310090503070605060f1003020f13031412120a02030604020c010507031b0203090a03 77
    0xd0803569074180c8014121001e60b5032010100b44031400a8202d0811031760303010004040c1208085101d40607140030104e01810b801543e42d5a0104281c2d180c4c012100040d09000300e400034400041100103001c0c01000004484845140e081c40c03042a0002690124680a20f9640d203c103000240044481107002000c1925107403aaa500240c0c5110030b03c6001c0c02010141c1c09003070b01c0d6040040c19420b480740340300006000303401000b0401581c50080f041d00c0a002c828a80030454842c0c0b80000fa280c00082881c41c4040752a100e0100c0c00c02500100400c0d02c580714079003d00042ea921400c02c00b043d03000c2d100c1590416151404201458801e40c02080392000c070f00c0710581080042440f50071070744040d4100f1203190708901c43c14095030204000c0c012801b0815002c0300d18103ea04094069070000c0079045c40c0080c4c3e00880444d40070354941d010384400641c0c0714020411484d1000d0024081c144000f01900c02380c4105200b066040d2000c0100c074400e0b04007900c0c2104d03980c50350740c9071040d0305d00c16600c0e00f8041d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 221840089 1250 221838839 221838847
    0x4030e0105120a1512080909070c080307020303060a050901061d1f02060901050c0405010f0e010c080a120507030c021906090f0302030a030b0118090f061e060e090405190503 76
    0x48040303907040340d028043c042c8001441e01100800d080e0740c0940da82140107418210308002000681060886244200580d55405981c441c0c1005540300c000184000f00342d48808820030440c1d0303034004091441542c0481e4072210b210342d50710900c04d054800380200c03c0010500c0484402d81c16800e100e4003039480001d8120080507000711001a1262156290040141c2140d010311842c0300c400d000d5507070000c00901482d45424508400a41088595111141407007903030b082c2044682c1c018005a100351b0340145049980c0c83c1c40b0741c801071503002c3e0340c0307601c40d001c80c81e00001c02c03c03540c400d01c11a1940d0403160004e000c0c1d40145101c4400280900300201d80f100c0d16045c1c3d10001803254050061101c0c8a034004548901c100325003c3c0588038111200b60410a0010300004d402940c0304200c8100c5171a40e000144000c050080c52010700000d42282e48490f6801c928070182c5072034450710300201e40e400d07518003105078900d00030000f05c514141d6003d08a41c2c044003c1499a441c0350783c1c01d0344054410f100712468 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 221841339 1250 221840089 221840107
    0x3061c0803070903110303030709030f2109080d02070e0c092202091309080702090705090a0305030d150e15030321240d0b130c03050c03010b011704030e0105 69
    0x554402c5540400040c1825010010440c1101d404112201c084000c1c508510301407400a058020520015080762900c440410510005880200300c0026400042080c80d14010340a49910090b10461311a40b2031b864076034007030f907201142003030561340c500d0b400300c5281d1141c40c07d02e44560030595000c0e82c03041401d03455040c0319080314640110300044100158540419500f041241040328800000481c04c0c0f00c0c0c100e0001e09050125241c075503049520400396141c91404482e50b0150b14011504022446400b206004000001d0300340c55807002d07814080b14131008002d000f020a1441054170405c00030021400c1c0b9264482c01400f0200301408132406c00442c0c83c440704000340c98002030303200d84403001c041c000081c1c4208c0d00c2000000110800c9aa9030080c84007082c0402c0301401c015066002800210308185288404070401e95000306d90041f081d5203a082013a15100c0919900d44a98a80110000d82c0d5002c0d005901c800c200f41443c28030941d03915181a00c040c0fa1480c00d017070400104100c0090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 221842589 1250 221841339 221841353
    0x30f030f0b041a0f0904150203040f0506090c10050a020604020402090102010b2e03060b0a0c0519080d050901050c18130603120e0916180b0406020f010b010c02010503061c 75
    0x500741994104640410103e010701043c90701d00810140645182000c20022580b00c180710004c16400000040c2d40e6651810400850341141c00002c09502440d0700b405030038100001c1d6504030007422901c00c950034040781002d41d2a40326000446008d0381103400010f015180581c0039010619060001103400b1a5180016081d411440e941a840400a8414448514100c44041680701841c14208110360034440400c096000c0e034807441003004100c00c2e04404000081c40b00c81c410092006080c05c1081c864a4010302c140c1100d4580c0c141c01745800009014010140502400341130101619441d12aa54110022100d80324611581203100d04000046005c1203115000085010b80500c3c0018490041d0007456500031900c00c900c01d050760400d002c6484a80c80b9043c0d0304650070305142111140c0008030b24682c0c0c0e00c941c404030b905180070900040c020303000b04103440d4581441c4020000320550344c0043d5211046508061700241d404d1000030030390f08060b40b4010660301e9640c40203035040a6039481072 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 221843839 1250 221842589 221842601
    0x314070b0903040f06090b07060e0109060f022203030c0b100b1b01050a06060504091d030d0501050102070b070308040b0702010f11090a050109080a2301020301030606060e0607030f030f0b04 83
    0x700071a800014104041002005600d015105501d40494036034a03001030314055002d0508040d100076030750754003540d4010302507008012195000c1014048041c100144400940000075081075070029400c80d10900b0652210107000c0c0d81d81030303c641d0500e008076100c1c2c085860380103010b80307103680d0103820108480b05090080d1484458001d541583d10340070a11031404d540307015008850b01d9040c14003d00466402c0310603102522110b800c0000c0540d44c0040301d851406095030290341c0e5010016015400c3c40740303034210364183c62080e001c8a8000d0341d80c00080030b4610442c440078000494607030206000812640d240380e040b401c10710000c1400d01c00e918182c011540c04115071141060b000403c11181e08100941c01c1c010182400c0030340c9c049141c05205500d4007490303403008064000d17045481c100581c5880c070507406211010000c41d180e40e101c0c945680103001c64010030340407400900356400c2d9454010f0031188500d030b055450144000501400b68081d000d4500d02043e95601c40300003507404c3d282c5102300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 221845089 1250 221843839 221843851
    0x13090509032512022b0203070804090e010c0807051c140702010e060606040819050a0804030803010306060b03070f0e030c03010e061f030803070503060609101106150d0314070b 77
    0xd440298003d24265070380c43d049100a4080d9048062014001e01c09030000c014000d0058203816032010412030101e0452003400c1004004510100c0d020030b080000c3d0b0300030a01070701140004c00138020300c01016514054115029070001d6010050200a42d518080c00341c00c00c4214071021440c11a010f140000c0c0c00c0d811222078005039960f03040a40034603400c000b0240c1002d01a10440d217054106480030303031a200c441404001c403c069803010320800104100130b1880541103100e043d210340d02c914003c6e019034030038401941c4030750820301c1c04600801142d0480c2c0c0603946640b10900c181d00c8000c0306440400c0e401703030400d42c1406881c02e2507109880c01c1c021240800c2407400603201c2440c046a420010560b4928078040310320f1118002e00002d120343d030840780c0160560900c241c8035614600010458400c41680d190026280d11513040040d811003034401c00c217400e810a6410984c0c6100c044441c4042c882403895004040a0061003c01c0c041c40040e00f07d10508100e152528485444424016000750380d2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 221846339 1250 221845089 221845147
    0x70f06021c0c030903030c080108030a0503040c0b0714161809020102010e1b0108091504140703060f0204060e040e031b010209120c031e0d0f02010207120f090b1309050903 75
    0x52081010707854441c08414144c1030070b208c401541072002647e074074000c0340940d034217006000011600384403c08100c0703c0113107003140342035503640c00c90b00e03010641c0f075000001e0385890b101d541420034040f1003030f1007080c05489240c1c100010f1110b488500301c0c054001c07608140d041d075583e5030078030220100500407450140b202081d01c1250104450004050840c010321180103600810401c0c2c2100119001072a003181d000045031110b01d021f1a01242440d64960000304000c0c5403005040d00d000c584c0d005402140c5d020380340d030f8508000762014042924522481140c03290410405a2610003190b101e4004a00800d03000605110610700807500d456100d580110142c4e00c407100c10005841c1c20000451700025103500d1402c801042e4071304907682c1c0c0f401d0121009002c02605100f141501c01d6040e00d41c05030b0400c081c0d6220303420098011b4440b0011000000000e2010361010070584020000c50340b1550110101124061070128240c00400f005840d030329642c0070411000e1103025115100c51001400450307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 221847589 1250 221846339 221846351
    0xa20040c051905090f01230c06040c05100c021c06091b1508070c1e03030608010605040b060409050c120c040602011b0e010e0a090204121205070f06021c0c03 69
    0x6071886004268020381009403c0140022940f2414500d00307080b0400c0c203058000440110b0503125a401c146480000c07e80d011414140c000c0c0300180c83c40c007643c003903c0303142030460300e8009101d4645070340495240400c0d001170b511001410b0034020312a081c4211550b8142580650381d818082c0c1d00450800e50b540e00d000c00404d000c0d07000d5404014014056901d481180d16050700c409003000c94001c000c4000d2181090302c20003032040040c3d00c449002d615800c0305080045515010740240001d0041000561a03c071000c1002e0809200b181d4403044010032403030a0074600744070300001e44001040851000b8052001401c650040b4512034000d400e013007072542e140da04054000b821603c604040c070051079910007a41103042d03045852018580c90030300c1c1c4022145014401b2905008c10b503070240c03c2c11440001e000075541c403c2c0544c4030803544925419901188001400c0301c03280501c100240404065501d50400149698010300c440c0c034031050781700040070f0204942011140641490008692102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 221848839 1250 221847589 221847607
    0x130b181608180706051b1906090203011b031b0f1d0f1c060c030908090603090f07080708240112030e030a150e0a030905060a030603020d082a0a20040c05 67
    0x9032000b130203010000018000c0c0c142c50207031147d403040c0101d40a0441550f503481d50080d9282900103100030200003ea070001104140b80c02401007500ca03000c40020760300d010707081c0c0c0c509100348600076038050b069a41024170031250f60348880c840030303160328158092071400f0802403a4980c0d180e411300b403e41d0303281800c071036440605050065958149008042621b024691000034010909641000d402541c031941c803980c642070800e02c3c00c0000107000398140301303400c4d000440050000e0903074260b9201000b6034608580000312021100451068401c01e1354503d4014460035901e001034094582c0a841d00804210003400804d0900340325040a0328040428010200d60041030300401114020300c03801480400c200303480c002c04002a5000340f81c8550400030b8034607042407103900480f01844d0000c1c21741007181101e251003031a0742c3c00501400414003000c00302e502040441080780d125400300380050040b00d1407598820142034202203600f0111113031121108640d031150b1282101808040e00c800b03544000d09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 221850089 1250 221848839 221848867
    0x19032003220206190e2805010c0b010623030411011b0b0a0515040e010c03050c0310062d03090309090c0203120411130b18160818070605 60
    0x10501080719454203100c0010b8807448120f4160500a809104d0b0140b07010342c0c211104c01c02c20081c01d500ca040e10358110250b5142075203a04403219422082c00710950340e03400543e01703500c2d40480603199403906d200422060b4060900303c42c111641210703403e0280ca992180132103d4005440c1590365159001441d441d950304040d442c00030004e041c203035141554695071485200e0100821580d4a1358a031350108010310404036150103c034400400c2800070100246025001384009010072002a003054046903040b05940c00312402001d03040181102e0a003404020f9507001d500190781010394801c40178490f40d4081503a40c0c14203514856601007010041400c0c01803800174590404803c5500d0030107004003103900003084030203800c01c41c03003407025070765981c103041f110b6021060286401c840b0300c030403410408101c0d90120380c03048000c83d034907080e055028900040105086400a440d4465504000701c2d0a00441c0d42a0740808044200c5440d110060f050906092007a8496000709034041001c503182080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 221851339 1250 221850089 221850121
    0x310120c1d0906150307050406170c040b1008040807021c03140c100b03030408150103140109030c08070501062d090e030f0d090210050c010e0105060619032003 70
    0x107510055000c50070010449521000090700e100d03a031105142c50990251004d010410081100030000c00060342d039030b42d0074411010040070784280c0d0300070304400c05800e140c140f0408401c000c0c050003400510352604000e45580401030400e0300da09005000640042c1e8a1200c50000740c4012151924003004610b00a00011040006400c5850701845180190300340000d400780d6410007008042230000030000402d0445c07051ba0000102400b82112600b045c20f100f240543c101ca1044034481962040580d500d42280e8840c54010001110002c2503008540c1c0e19010b00b00c100d00810001490942c0c031140a5050724003240d5080f42a81a030400c19041c0302500080340062154500600c0a6090354444a0300d03489008c4098440e9100401c0f05262405a03034032076441c066026003101c0d1b00c200903a60282c01e9802c9041841069800e08081c5000d009040c0186802640007810503800e190840e14140041224142064201655190a04801c0d0021241030380b8111074024129968140140640343c4c41079 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 221852589 1250 221851339 221851379
    0x4030b310803071404090906060e090706090b03070e0306010e07200601051002033c091e040b090f071806090b0d0e010c020f0606040908030402060310120c 68
    0xa1809510081072020040320780c401c00034600248040c6542028102d1401240c00c00402549440d13826002c105895004405444405024018507591403540b513036152924090384001030121282081001c0c544000b030764010f0b409040c8802c00c801480d003c24a802c20076802204801035801c00d200420780c1203016071005240c001400c0c130300c40c0700610005d5640e10041c411240650342102c040e843c61413007402035490801c1e42d9030600e07000c000200030820510482c800c0714580a0990760761070701811010f0045a8011070050900c1001440c0c000c445d01c0d840d0900c00845030840d444445c854100e549060016101c3d00206200100c0c5041c501c00041440c42601074143c446020800140300306e6070012640710454402c1e2518580d91102903141d94050230182c0e0041c01c0315801c29503040d68030340c2c001c55840255040071007140c1d119900e0200b0481990300040b0701800301903040002c1009424220006c50788001d111048000656a4100c401070101d40814107803914840c0b80d070b090049200014207090701c08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 221853839 1250 221852589 221852671
    0xc0a24060e0103080306040e07081605060a0e040902040605040e0a140105071b051006030b040b07020304050f1320070b01060507020609060c0a020319110406080c0d05010204030b 78
    0x41c01c010107440010720600000e001c1c0302011000581c01d07039884e0040d4040c42079000c10b03100b032550f4800380c05039510150342c040c0680000719080401c145c240700381a144903049681c0c0741002450340720140401400c100100f40e8106456010119464840d4000d0101078400c560052000e91054285111002c140f10850f10300340c1d050800f40504103500590b069008070941c40d15102c40b103000d02d0090724200030400130001850502d04004140544c0c0c83d41039120b94091000104180d81d17501381281c40c1c0c420341c0542c551040b0703181641c0c070f09030604070074000d103612454078001010502001803030982261138120781001c02c40012031208208001c1d030100c0c014010b6062a03420503007981e0010304039000d01100503000c1c003c04a40091107200c2000341c4201543c018050745c0d80030381e10381c0070f510358400310110550b001104e905080d581402d20380b05010032180050003400002000c3d40030041220307400e21080e500356400307200100101310150b0707449015001c210300060444003018101000c0402e00c040104000e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 221855089 1250 221853839 221853851
    0x2120f0c06071a0a1b030614100801061803050f01050105031606020a0f020303090405010801020a0e0d0206121806130209010914040b0604060305010e031e04060f03050c0c0a24 77
    0xc103800c9012441c210f5120011100e5640d05481d100200010044801d4441c0e0207446541003c4e010340c4001d05a400000045980d291007109000400410407141000a4100001003203c0c03841850002000c070984048180000c2d540d860700e0345001540e0790302d5040ea95440004216030300d0104816150003e20100001c00d503890030070069103e00900b0300c040d108880d2030381d40c5400c44d6000d0040700c008450041c800c001c0c070f58603076561900079003201aa03a808202e42010705c12480ca0140103880341150b000f400b561600f1044140c550b96200042c0074440e10101c40c41140d446040107010340d500c520b40e8a6543e101c44102e50040010004040e4041035803545006c04511074110324000980e40107412401d07469181c2c0b59a0042402071403140c1c4054490351a20b400000c50f62408001081020364610b444070600752001c540d40441e00c960300c580404101d000905803031060086e0400b5030301050080300c103030800d0051941c8504000904d20304079001451400103e1420380c0000c054000303031800401c20820 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 221856339 1250 221855089 221855093
    0x10f0503060c091003020f0a021015080309040e010204030b04080a0305160c17040f091d12030a15050d0605041a0112260c060403030c021b040e0a02120f0c0607 70
    0x80c603c10146a03074011900f002210040c2406a0101d444e51294628050303541c0342c5c1d0319002034541d00f030000b00f0308101d81065086000751a08001c510203440009015500c2e299140c030400c402004928203c1a05540174032000002c03451849103a0310540c01340c80b406035542034890004007159001851b54200c00c04183c00120490390140440d0b4000d540400c5200c0b820035030856000181c001c41d480408101110500891144500d4000070b030075010f01e001041300860302d1180310303860368800c504130000204140300003075140300203400000c1d00c0d000c40d4162105158490001c5104040607050039912903484101f88410000300e070508184008000c0d020520300d504107107014080d00c0d0015806864149800407141d445100303035200b080704464580d891a640c0310f000300314031b86503c42124140d011a00e13003d42c01316000e0020400240c0844000c040c180044c46060402004000b040c0c080940d5120302000b01c401600c61028006480e0607003401031901c100e20074213a901d04042c0c0c0071800e000d10b100f8012400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 221857589 1250 221856339 221856361
    0x5040f0311162c060108072a061a03010621140f0c1005070209010b18030105090c040b030f0a061806020708120a1b050c0a1505010f050306 61
    0x14899040c80c00800c00584100150315289141503030001d440e241d0040000c8000e00c658000302400f9402030a00810b015191240141000c100d800602064200c000100010f2003480d5038407040d803141e01200c3c2e54645a058402c00c3c2c2d080c0003c00c58070386540d516403060b403451295502036440340880091048609203041080090345440c16044001605010b2804010300044000c58002140302100d051581d8001c500340d44134080c081c003030300440d120303001512214071902c2122000c9401404064559103000715080056003d07203070b800406e00103a4503a503a80d980a020700340c02846503000412050103070001704800c03694061400c034030903131100340c42c1011010049034502105030000c4000403d1170b01d4240180000021400003800b0328400183e00003045040d00290440b0554044c01c00840e0381c4000f5a1401c44040f8680c00c84a00041031020a440744100020b081c60414034044e01e262a25a540d004560031201c0402110075032901c006102d50310a081d07030500103000c00c9004140710b081ca61803a072 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 221858839 1250 221857589 221857613
    0x1209030509041b0f0509030a02090f06011107060c030507030e040f090c050d0b13020d0209040c06030f05011202040f1509050105030105060105270102070317030609100612050a0e030408070e0a0504 86
    0xf4410081b8184403581c0d014062416017035000780c5404076a1074486007001502070200c41071070100300f4a4480c80520800060660142d81c013584400ca107240030f070f45041e511500542c1c01102001060f030301082c82e68a071406440c210540c000c402081170f42c102d150403040760303405130050b41c01002441020400700d60b0b001050b903005000b0b00c4100c4207060090000c02c894101c100300181d0010800001d000c20003806031013802c100d40c020b40e010049600500c1ea1201683e00a118540d44004c0601814000d40b0f0103501c0302c01690420b050010322050100c450b5000c44a180c2d2101c1d403c150b6420040000e0f050030301400d42c5c0444246081c5140c1038141c11003460084940e03070118100d50100900703507000d03402041a900950b400c65091140701d16400041045940304403400c9006a01d002c000c00c0c00c2c2c82d03a4118480c141c8400751a004074865000c003076580202801072020905c40c1e1a00080440400c0600062014103100006041c84604010150080c21000f4001c0040390340361108100c0490f0711a0000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 221860089 1250 221858839 221858867
    0xe061005010c141507020c0d081902010b0907030605030120030126060c0910090501020601090b1504060e18090303010b0f07230f0f0c010309031209030509041b 70
    0x8810b601070030b41085265251407800c40d49252080404440407200f521145621500499003120300ca43c404805000c966400144010300c501d000b84107080402c440c070b02105d0b000b03001e24400060110901c07000034041d240181d61641c082076407000b040c8100d0a080c011701c0440d42c6c0c0c124420040861181c040340f00c92005118102d440804500d54403030800240c180c4030070070b2150a046507580c1c2000701c2141c02c9684114200b900c100980c912038180b050107041403908565050300030b401240c3c40c1102d50701c082c0c410610815031000100011035401d01c54400034201074081555050340c20300454040c003020507444100000800e20f008100102c4640000440341551692001d603501d440c05146056a140101000140790101182c107407144698648172207269880b00008035403042410006641d243d0b0190f840c4184181c01c030304660300c182d5005c0d41044115510a14040c1303402c045e0701400000710740750507404900007080012003410501d0580604a01040e09c0003848070120a01e102c0608070704c41c61000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 221861339 1250 221860089 221860097
    0xf090c050a0f0b040603111903020909010905070c08030907081002030108060c03010b04060507030c02090a27030507110604030c0b0c010605060f1207030f020a0504090c0c1a3301030e06100501 84
    0x10f9007854400201c02c0c0c40c0e404148000c4608d0b4403030000c41c0a0301a400c40001580100c0081000040340180c0b4080c0e14003d140d00c0d01e52040f801340c02d0300c0340034940d800200300040510841d4000560f2260802a4500b04130350364000680701c0d41070100300b5080c0303080649080009001800140403c8a22204490885141c2c0c20700c03543e40e00e0146015034a01e014044060b500c85100010015210000d2700408180b600015103080c0c41e01911402103481c07007158038042c00141e02400208009200c0075140c4503e008002c0c44d40b400d081d580d6031441141c02c11501301003000c400104206070383d144240905000f402c000c40b000d078144500e4000a050500520003914102c00e180800304a90358000e0740109800e5000080c15561244814005406076000d841001842ca151100820b1540e00c10034030480306560146a010201d0b0401c00c40d001c540102030280c82d2007406281032000c0588084401401406403015981076481c030900015003110410740040030107030010300c10880e190342c0100c85002a1031090074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 221862589 1250 221861339 221861351
    0xc05150a0c061103130b09240a14090f0111070206070b06010e060f040501020601090207050601060c1b120506090d0503060607060b120102040315020f040504020d0f090c050a0f0b040603 81
    0x6128000d40080c22890601e0b9000001340110301c103071103c4001045d405400d28041c10f46950ba1402e517590190f03d00e641e01e079082c080b54a04610522440a038010152010209035134145d4510110f00e4002514107004540c44010001138684080c00b9041e010003410a1880c20178400d50081406449403803002452110700070300240051b8025615001c1590020300426200c400803030344d50000b58818099180584112000007a41a51600132527451603802400782950b40d18140f01134508a2001c0002c403480510f4592041400a00c00e14400007003900e403a0b01149000c081c18070074200040130f0400c51813500810b90080c81c0b40d4100c402c0f2504100140c408598618050405d07800910854026a501c1102c486020034604815000f03002540c0c01044540608030310766400304100d01c10400c0018200d20180002c01603490103a000e0700c92404154004180d640ca021040e80480d07451500072910700802a200b40501e0031f2041100c806003203a91910200740d0b042001c0d4007080e010b94400c079010542c40300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 221863839 1250 221862589 221862593
    0x120e03104d04050f0f2107180e030a0302090a0b2212020307063501060212040e0f1312030c02012318030c031813050403120509031e070c05150a0c 64
    0x319030399090301d4083c441041c81c8112116065250351441c4230300f9076514002540040c80511611034940f9014210f0019860140207a0b41900650020a41c031640300f480341800080c030382071040c018412141f82e0800480c940200d1a601e020b81c4003280c120841036141d8111441c016200014840700391440c03805c01c40e00040040c404039408010060f07203460014a214510700744e03800100307510750590764030742c09072a00500d01c0904001a801644074003078a018441303010920317404114901039007142000048100408043e262100195040181c20700003a607540350043e181942071003245004600d410700c00c1130b5101d507542c218842c80e02c040c1c001c0d140c0d42d42609410805d013004204858110300c0c00b00a03030303855007899031504601a01485840e0300416074402c07410030035036007807150310b01c51541500d800d503004e10551a48002003800500d0003040b44000c000c8609910742c0a00c80071103c0c02c0f50b000340f0b40e407202185410300180003103910682c02920912110501ea140b00d906545d00c0b02850701d41403400a51074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 221865089 1250 221863839 221863849
    0x909091207050c2e05030703110408031305120a03120b0406030b070f1403180a0b0a0b190501021c2a120e03104d04050f0f 54
    0x404088661200081d010007080008150640460012901a0840700c1000c591502034805041d1400b01040c02292503c10540204d01854200c2c0c0f0b0b03841c00045010f0a4111011964019004108150703c00b01d6100704042846410714054641543c4c00c05950400e0519071b5607130000720100030103100003003506c144030f4180c9a0014454110003001030000c0380d500e040511540d00305031143d50000340b0b0031807164181d17030203a0034100c40c00c482a84441c3c590f98a02c43c4201401d003104200d11002c2c010700010300c0102d18098501c500072400c807180051403c1d11201000311540380c03a000c248054502d0707001045681c1e00807034000c001c41251784440c4a030901c03a200403681031500c410010480f80d121206e1100b07440035003110302240c45c46080c403031903014981503041e540c05640040455150b4000d0020590290040e0080045441036004040315800541064107035508070800d40b249223004e098203aa0504103c04180d80040c02801d115860142000301040040c0080350540f07014000c01001c92925031a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 221866339 1250 221865089 221865103
    0xe09121e07061112010801020a020a170c0a050c01030e160911160303051518010308090d052b050703020304030f0f021314090d080103021512010b120a020906090909 72
    0x8003110801002002e0705a10000360131070b04a901070011180000b140800051088682d10941c2c0e4000780488591540c40b0811000001d41049400710f003482685015003080108052942c8502d000d01070702550f040005044030740c1e103403880f0f05a5103e050b007900c03a141c48894440c01e4a02071200400c803003401c0d80010f0100d00c1a00002c1c9040070002580340203043d410350055002d0a10704901a1441071003a040100d10700c203e0a00312141d400304c100400004482000405600d0030203449035004d00880d03100c1034200001c1c20715840320354007070015502c2c240e800c40d8040449284541096800d02c921074800a40d2400349000c0200a698154242002d0103560f840c01004541d008085464440d14500001c01512045212050b0340c1501c0c00400c180c07540110300c0e041001490360ba00710140c0c0c615000c10004942c0031158507034000003000381020081c0c0d1001c1c001c1c0601441880140e036894054800852088024080d5414601c18800500e9070380d2a0401c44103828003c460070005501e418440714203000c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 221867589 1250 221866339 221866343
    0x1a2107031d030703090f080303060d030311040807030b070309050714150406030f050c0301081b06120c04030c0801050f1302010e031f060e280e060109060e09121e07 72
    0x10700e00010308550400080180201442035503500d04907556070003030910303008842c02540b203c0d40003880020840e080c520405888903000e840c010030b6450022024071030302d40c00f6030860505900407007801c0c424400080103180d000360f1a4501000341c40829240c00c8e894028034001d654407405040b02c0031206580380556494104044115203980f1951500301030000c1800101510300f480c10140002d954070400c50a4170f0403a00b551000e4090b0301e00940c0c598214410003904564030410912000c44a5481104198490144002c00c19680c2d411400c14200344911544005210f81c1040c0c20041c0d4071603440002ca41102094441080d40c0c400b92005030b40407601000002d401d1320a000792090782d2400c2546000c0c0c0d031800041e00f0003202e611400214981c880486420351f001340c40700b80606201c200e6011016103504207140008410300d2500c91380c4e0400b042070780020400744d210301003031040820701400340380c1160b20344004114281031070001d03906600405041101c1d8104001d80000706031403110407038032010717 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 221868839 1250 221867589 221867621
    0x80f090604022815081302060901032316080901050702070302060306010c0b0a150b07120e0a0b190807030b21070b071208090a111c0b040605011a210703 67
    0x9902d07807409400b22040814400001171a48022407041c0724608140444180c002e8481031402c440d87c001540030b8543c0621201c088070080801c9412741e01c214030070300d001c0c1510138108100e4002c94807000f0400e02e8080c050402a0345000c6c184201180c001400c0c50840c0c3d41690825165a552801a503007068242c0010300040b0048081240100d101c4e0b104d0080c6110160392041c105071145130380d80250040800c020800080c0100b11084903009003c1c071100140e00528451541d0f864000c41665500310300b49804102c00c00041090070241c1000145521200d03a2408002052202c40014400071603815000040b100f8807803805a02e180510420016028601d041d540d11203640c41c0001180b00c4103018100002d40138070100b00611408100406c8164104400c0c3c0c10301e0306090100035002203128943c0100006801006002404d030b0300100d4400c600078800000d996142040303e40c10741003450038010380100e041006843c0888500e41c1d14079441c1e02c00502514030741d074440041d030050001c061a0307041c1d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 221870089 1250 221868839 221868919
    0x6061a0322080c0105180d09170705032515050a080402010302090d050c12070509071409040504030e030c030c1809010e03040b0706060504020f190c020a090c080f09060402 75
    0x3c28415008980120641440c514403901d11282c1e403034032110482c1101001826210080200001b6101840c01000010702580c0029a48900091400e4541d50600d0f01d40c682e145401e032000c8268030f40700c0006007505000040d4400c0c2d00b150003880d40c0724a01e0f401040c00f1000000c5800d691090341078904075800544000d61200841c10074503035a18071034103424451420700040202041d00884c50b9001c8440182c100c0c4819294820140ca00d80c1d4010240280d40c14180202c0300c856172036001c1e0500581c003a80312034130a14285420f050a2803842c1e0311490080e4007504442c500d6445803d480d400380b0b8020b820303c10043d03c4040722300e030241c0b511840040070f52002040124580c4141c2c40108241c40c440c035004c0050301d070b9800522059001c1c002504c07901c0b84041c0000d144016201c00942c040092615090307442540c1580003a0681c0d078290440c14100359034101502c809500000425013060514184c0360b120b281101840395a0080100000e00461140c10180a0340403010304081002c8034250301e0b0400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 221871339 1250 221870089 221870107
    0x210106050c01291203070c0b0301090b040c0e0402160b010905060909010c0f03020a050903010501150212130909140109030c0b01050910091104030f0c0306061a032208 73
    0x319000102800e5003940391110ba40003120b10108180308400300c0d07441c1150240711481c104403003110781c1d061190640c0010030202001032010726014020300380c40686c00d07440b0750500454030109c1d405070f50a18065450078825190042e00205200f015102c111005030743d503070010000c03410403000310030010201c5420780d0010403040c00301d0f00424401c60040d103070900e44c1c0e40c030042214280d941d03070640032002c2020842c000c030304c070742c1701f42c00411002c8000d090241c642909100400c0c21624264001c49a03000401e10900d1415418441840100104284c540c10b10704224102119001030384600f22540356602c1c030b00c4042200c08102c440901c2c620318004c208485487c18041d0105901484c00c550360f80d0084008141440c01c003010354062000803040b0444241400315490041c10811001445490140400000a0803d61b0800143c51080c02c111603868034502e49901035525940040d80344921b014101062186200103580c2d0021104220040302c144000d1440d045031411003019003c072000040c0c1c880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 221872589 1250 221871339 221871347
    0x1b1309050102091503040305030417041508010e0106091a0a090b03040605061306030503030f04110a060201140f0105010c03050f040513050610181e080307051f060e0c210106 76
    0xd02c00d50680e6004500c9030710345101044e40c40304a8006003c9a01400883e001ca82c656512505c0d4441e14514949001e40320144a8249400742c0c400d0b00c001000640140301002440e850700d801400700d82000040141400c80110790b2020b0100361394003691000c15548140e030f11855131100103160303141c101c03070b039034103042c04c0c001c02401d02240c080d0f00400f5048008803014426115082c12250040065410350f29000020120400c002c0c10654422040203003442c510f9540c100c066006001c039400005a888541060701041b200003040c070312404405030300400841c0d802042084516515181c4107540380014911220a4010b940006800040154517044032803081c1d401103025013030445447c1140c01040030101c8103020300034070381c68005544840c10060404021002d0002c43e1340e41b0700084006c0e4445034078500d941c001e801c05840703d902c01c15010321680c10024001c5150b841c6602c0500c1500c1c2001c0301e40d051600060214004100e001400d10504640700c40d00c4001e041e2820010040b07540d440000030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 221873839 1250 221872589 221872597
    0x603060612051c0801030305030912031e061002070b07050f1002090f030a03050d09020f040213030c060806030604030f030b0d0b1905010f05060c1f0504140607021b1309050102 77
    0x310340c0c0c07041030808030740c245444200c0d07009041c4654882130141c0c00c0d545d04580d6038001819032443c6109001c00c0d400b4000003000514462005c410b41c1c0c1d01c10345080409420500809000d860103030407910b0074250340f03650100300c00042c2c0300c0040c2071942c4c52020380380ca40c0c6800200c1641c207486003d45400040114616002001d5a50b0200c0e140501149000304040c2ca52100d800000e021070b1042100030350426040d00585000c900061034803561424a0010800b03a0740145091543c10344d540f40240108000400e803071014040500d010801c07031038440d02084d81c801004c3d2000c0c0034031108001c001c103001d00c0303a0004002440050a4410005a5880c1141445505641c0000c044000002006880c071891042c28102ea00d4114010000d616020070312149a1141740c0e516a01d018600140110818110303098100410b49003000850380b905040c442d0b5011041510315269402c804184101d940d400640d0b035030495200f40b00071581507884400501c668011a400c655105e080905050502c03c2c194054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 221875089 1250 221873839 221873843
    0x506070201181e150e041d060f01031b030b0a18080a08090105010503010b0d1217150a060305040308040611130602070f06030207030206040f03030f050a0b01110c0f0f03010603060612 80
    0xf4119203a1030f074a07808905804001e08100140c04041600740518140c0c000404801c9010450f24150507190340d400c1c05c09008039001d04118000340d00404c1001207041c0416200c070404120007280c0341c10740d61a4801c000c005007400380d91076240e021640d1300f14151103042c0300c90380d805091550343780149a0084c1100c01d04a4420410f135103040b000181c41e00f4103026501110380002c2040580c06515a11090080b0404a0400400060202c00c07411850320300714003406080883d19141484800b4402c10021110f550003036006c040c105400e000000780c1099181c0d030080c2c1e00080218100c030303c00f00c41040c24040c000d4149076501c018040044c0a94000c210902960010f4002c9400c082d1140403d500ba071240c10700082c0160302490000c1c010810358480118064032070b1801080303041d81d01c0d2410090340d0060355085840c81c1d44041440f0382e903800910b8180c15501041c06400200c1882000a01c130b204c02d0700e40301e40115158042a2869a001e500c4070001d1680294104600b0740c035070f10008468052a00e003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 221876339 1250 221875089 221875139
    0x402040507030e07090e030c010903090e0601090b0403020f0310022101050d03020a030f0302040b040e06180603100b0414130b0a060b0f0c0a05070612060902030907050607020118 78
    0x104007a039101e40a030b001882c0c1c500004103916840e06025000402e10520000c94501040c048134111351428002c159009009a13140007150b42001e0244802002c0901040d041c800d017080104540c158200546040f80c0e01140e0038180e41c458030b40424204001d89015507002c074400030f103125075402c440c45468094082d854200300035a88500911210704809031001d80503902040404000a1040c24180c9254003149009410a40c0ea505c1c081e4441c0c02c25006014a000b005013049080d041400f801c43c0c06001c0c0d000ea108240c01c001d80402e446100c1448004281c1e501c031001003030291030b203400880c2c0b101107402240e02c0a1914074881d40412400c160210303201c000010116185a106006100a5403010328055290208003c2e04100e1a44456543c9406010b01611500450300c2070184c0d1000340810303100c0303818110707500020001b01c0d0030507080780d203c0a1042c000e100080b54002a0300e4265181a154195070307030543d00050303800701c10a400702c4421640384840420384a10101c0071303041a0004101c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 221877589 1250 221876339 221876341
    0xc050c01151a04030b040f0c12260310090507020c0621010503060412030c0c0b04120201050601110a0209071806050d0525142a121312022704020405 65
    0x2c0c1030568400c500c4090700c120081c40108010071215030300d1401507441008401903007591b400c0c140101c4000104103a460300d07804408071010400d1400d80905070084143c4080c91498503000601003200c41d0302070103c0f00c60761900040c201500800c084d011035040203004640711030a0112100d03d8404032855441058003503000010310307050001d8024011039118050030010100030750210002c01000b5800d4080140004041010030301e00c0c0d08250150340100e440c4405c0300750018010b03003942d40c060884c034100450245082610800030030714140803075040f52020744a0b200c0d074008483c07424503641c1d00d40f003401443d080011341c00c2e00803004181e00701c0e43c41e000380141d5880182e547c1c503140b0791642058002c45032a001954451003040c02c010307103c171052040c80c10304175140745844800301c0b0140031600400006c0203540b00060100000c21078601261307500b61038228030f01000011811244a801d0f81c01d654262510308554880c0611800c0143e12408074500b0207512a00da94198410394059000382d00e400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 221878839 1250 221877589 221877629
    0x9231911090a120807110d06051f08070b040902090402091203030702010f110409020313080c070503070b03071403040609050a11040e070305030301060e030c1005070507080712060c050c0115 83
    0x4500791070901d4001c15140d04217001501c1c2c8404000d0060b18169001e034040c1c0540c00019910b1203010b020300c0d0905d2034600d4200f00e500c950500501d541e005201030351700c5110b04004804002c4215011f0703440044000d80c91360000f40114010380500c0070415031041e40d407400b0452510001020354421201640203000042406030101e0031034030740050008080000308014000d031003442c2c000399081502070a00f030b020a102c1f030700d484e02c0700d41000c0c00c2c6900071b40203100104031901c2c04018940103400908941440c500f020f50003c1c00d03900c1c035500c100c2d0100c0d8000c17000809106141c0d07c01e41409401ca4140d89100c0542c1c036120180d000c2c869900ea10903407502c0840d51811b580010443e09490b4044003c51440c0d08004054824464504041c0c1e031612419a0101c01500d80070241e000846c0c040c1c841c1900c031003051401d6402c0c4000358001814031342c0102d0b410404102609103d180786600190002400b05440380116418800d0320007880b159800e240240c0c448141c05c055210443d0101101e420980c5040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 221880089 1250 221878839 221878859
    0x3020a1b050a030f050a060603150c020f07090507230d0e0d020a110a05120105011a0a091404111206010f020a02010203040308030603010b0a0801050901050109231911090a 75
    0x600a840c0c01031030040b0288001182525050326690041d411281c5c1145d1543d64003090b10b01d00d4008403489803900c50b05600c1c0c82540e002d210906015400640204204600d40380d41da15020320031004025101c034045041c05018030092404504103010501c6c000c4218512980560301041c05014940c3c43c0030140d089901000c2943cbc1c0c8060682c0d4003070010b143d07242e1151400380142c010300d41c2e8455444000054540c0d250368641c90342e943c0b1000049525803405c240c00c030b0200c09c00038821101d010200803ea40c0107500c21004000d5500700725500c1240410310300428024100ca5014600c03080001603202c0160400c0034075144200401d170b8688a0340080040204c2e26a083d000000740964001c1c0418400030308078801841c2d010b40c005c1c00010748207480800107414102141c0c0425050395444040c840200428010140903111800c1e0a100303028802003070304034100102e0b0b076034540e0b1200d01c8041550307a055174400e561001c10b0703400b051001060a4481080c2070344180100391064140039400651b031100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 221881339 1250 221880089 221880143
    0x91003051504030f0e01260f060901050a060503040503161a070908030409090503070c06080106031b0f0f030f06060504080708060c1b010b0405040303020720101b0206030403020a 78
    0x715a55480058026a50036034010200c1c5c3c554038140300e60484101c0c03c125191400305265401002c500d0403604100e802c072002010042c2c1542d020368480c2c001803040e0b40707032041c3c41c404131f4405180031503881c0e485042007411800f52410780c0c0503011300c100707986040c0400c0c85140064024600d40004c455140e41c141a12059180d1281002c2c1c5d400601040101442070f0380200103860184080d41c0c5409403540d248a015605900908081062500103100d0141e2520a8500c404075000c4062141040342c98064040003401103c20200b100740514040032038400d0700705000d481004030080c01100e0300c51001a2854106010380b43c890300c1100c8000524031000143c1601400006401c54a001c9588541d1000e05840c54140d000d02d41d00d5004101480c2c5036449154070079400780e98016260480c603e040360220b01406880c4072030300301080c981c0c0040d80c0e48001ca0780d1080d0542c100a4914185401d03044c8000540d0700700a548a00088200001d154000c10283d41d01849130080700245810000c2410407124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 221882589 1250 221881339 221881343
    0x305190c0504151502030c1c08040f1103060403030e010e0615060703110f010501061d030d0810030b0903090a05090c070f08040b0c0a020a05010306030b06041505091003051504 77
    0x46681010001800c02d940251450b0001e0191080d446464800c0040140092086080141e03c002504131004000f8400780b5580d203600510742ca4202d0703030b90000811800c006803000d030801300c0161000d001c1041e01c0e40010260360340a03040d00c0c854134043c00c01500410341c40484c410194280188240039090201d41075120b5002454417072155140b0303c0c1446410740200a0440501065410104801d50100701220600c038821001140d10743c144030000782100c0c9004c0541010000414a120742640d0200d43c0d105c06c1c15451600348210760366100d5249203481503510291440700c90005100020b440440140190741c2c1c02c1e03d0f2038003120365540c01d12962442c01c41e0480b0444d0400e1200c0c00c0004c41000391001124010301645091540307403120310600c1e900c640c0507800550b006040860850501c100801e008100900b01081850703d59210541c04540040945d4842c41d951055120590300b07000700c5002505003d01000e10a207001400171840701c00d68082550a8410019080403a41d040070005108503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 221883839 1250 221882589 221882603
    0x30d030615090f090b03030c060f04030e040204150c020f040f02030406050f09060a0e0703140a050f0c01050715060308040e0f060420030a0905030d0c0e0d02010f0c05071e030519 78
    0x1910f882004d00040030078402050385808100a03400015034208084d600404072400380030ba09040c1450b001e00f50322240759840f4011801030104000e14040c5a92460041010303041042810003940700145200c1045120141d2062070080006d041c81c4040d40510320a501c036a00400680c0c41d404001140c19008581c2c00000383d2140d07001906070340f55500320040c074200c00c00403540516100d81d2500b51500c0d00ca000380f60280c1c030000840042c8442004120f504822900182c1009540213000034007912503500c9c003a102000403508400c48280f164885002581c001992940712030310340c4034841010f0f0060380d00f010090010404101185086c0c881e1403499400c01d80c1400001d0540180c0344501d400082140d042c65944440280204000348010140071010b010002141d401140000d8040301041c9a818080c3c0c0c0b10820150041c0d800c030403100d20382201401c2480c0300a54600d017191520b5103582042000100c43c8040c000b80311829018013054910413400c0da00110302004a95041c00d081440c050804 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 221885089 1250 221883839 221883869
    0x1101061d0c0721051c090501050a0b031908220f09050105091308070209040809010201060806010b0304171b0c1f090314010e0312010e07020d1403070905030d03061509 73
    0x4203901240c075541c0c100c0b40c2070841c141410b80d420080d00e1105c1c100181d1440703881e00000300401100b8801c450340800e0304002000380000390400b09682d0741650800c0c03811040e00840d81400d003da41e9007030b5020340c200200d850300f078010400000c2e11b10905611030742108000340000030a542d82c050058078140e03000a0664030340703643c1e9413840386014124100c1c00e840a1408012000c05038551f10b542510850146034019540c03ea0350000a0840c2d01d254000c40040d0805001032040000300341c1260b81054000a5001c414650381c0d100404c28429800740c0158185640c501c0060b0f003c2c085044440340e03400b00d8001c426104202c1c071510140038190f00c0840090401c46060001070061015800301040400c0006200c6945070b40107469603003c41403001d00c074203420f401005400300c060406544003509101134903004080f00350180103080d014850704401d100200c00141c2043c070580d069030003003500508440b0019444d100c00b134014841805100561108804556a00d074005c0305400121003c1c08852206 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 221886339 1250 221885089 221885123
    0x60708060d030c05031204020a092c01060e0f0109050703060b191206060507050606010c031e0e0604090e1501050f040203100f0b1305100c0201030c1101061d0c07 71
    0x80250200e0480a120074000200b0200d002040600b8500c42c4040c1c40b0109820280108127214000c0d40c40001500e0414100095042c4a0800404400712500100303412406281025001d000180c0001082d800d441d0204103000c00101c600f030b4100da040c0c143c10003040d01d503c1d0088050310501d0256a00c402d00411000e002180e16088007103001c0e8140c98142c80820a6000600640b051540180001040803030f800050140500203030340c0210b401d0a0040c07400c140d65030090040701041d04007800d809a9408401111405003440da805980003c1c45c5680c4d80303480d440188010303c4032040709142807080d1400b10b0040c60701c1c1c1040d0b0781030310002414040c00c2400c0000b000044d5200401840f101e0000110020b407590707007168450090501035509684550040070180c49054981e4440c920984000d00d203e20113903044039180e01010740a19000c2500d90124800340c4400540301c511151039807034a0400a80c0e0326041101101503c0120314681c89030319840d0200d5040c0c0030741c84020300021082e98034101d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 221887589 1250 221886339 221886349
    0x2030f0a0e0c0a1e08010f090303180b06061b030a111005060a15030b03030403050309010f091211010509100519082e030c030305030109050a020c060402150f16020f0306070806 77
    0x260b001c2e0200d11380b0342e85494402e02c3c3c4c2950160304240c10b145864250030020103405024621312016082c0003480c103a2601d4a0744865100080c203814080c400000c0c0900310310169004040c203941102044075560200940001c0c00032101900e0410107002d80d88028520f16043d006880c0100381c02042c080c800c03401e10403550044409940c2070f60605035207180d07984840c2c030240b014100440c040c07070245848034920000981984404180f000c200030140c50240003010208960b001d500d40c0002020030003d04080040c0c40e5880785c212800c0d03005400a800b4a5010341c014001c1c954403c0350450704110159a41e01521781c2c440a4030000f542c42603e4944480c1545403c0307105240104c03210302c1c282829070702d485040c03d90a803908182c0000708004014414200540210703508016031000c01c62601501c420078036100d10014100174070480032420f41c5891003505000f03485052500c0800c8035642c140d500d114514280c0e1201e4120300550300e2850000c010714004c01c00ca0311036a4136454031100c90b624502008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 221888839 1250 221887589 221887619
    0x1115040305030c07021903021819020a1413140109080a0f030c17040e0c03041113021b01060302030607081003030e0a0b04150e1002071809020402030f0a0e0c0a 70
    0x20150406020100240e905c40210b10007210007003c1c1b030222641103005000500800550b0303492048035030014000c0321514400180c1007070003040070043e151040380408460204607040f0041050300f020031514015040c100030b5600701e420410401c01840820001540c1c0980c00e44951001e40c0c00030150740780402c002c14012125544285030184103031016690320074180b41c422600e000d0301e0b07102241c02e02012400d40001d5810201200e00355042d4a0700342c0e542e030240d040d511112401081400001c200034510b640690743d03048422132011341e1440e00900c03032900038180341c40f09900c2071152202051403d8084c54807107000d0414549010170300c50454030300391980940c0707100036908503004036000075190a4100141018044040458411011813000200303424017003030a5601c56405640003840c0141c000a598040715410128401c0004901205600030120302710003a402900000410607003068100f186845050020010000401c041044607a9250703001005604620001800d00021403080540307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 221890089 1250 221888839 221888851
    0xa0605090a0803070b040c0518010909030306180906180f1202120307050307020f0f06240604080c01021213031509060c030b0f01020307150203090a0507030503030106111504030503 79
    0x400c07080d680b66032103032030355000311410b440b403442070801e00c8104510302111b1401458212401caa80303000240b088544101c040c482c0c101c0c1d03560b4942000c01054040e42000008280703c001444c080565146d00307501400840c8001c0b0b0700c66160844501100801940c15203046800a40d586002c8840d65228040c00c044800407205500c2500c40352260011680000d500c52a500d90b10642c5904000303001a14185080c980081150040402480c41140000b20241c0c4181100300800c4050b00780300c2c240c408121040e00d06500704c9000180460404070008020840c090700fa400c41e00c40c18000442c0c004580206140c0507d480c1001c8820008030f180c002c1a901c80c002188000903c54001d5614042118034503100035001c01d03126006100c40b803030800f05c014090707082030002d1450080c03a682e541d0034403011600f101c0d0000e81c2c04400305040440420030600c0d4541c2c840304861f80036407282010343e5250800d204100024844510485183c1c4e4049032014290748001c010741c42a450b16582960260401011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 221891339 1250 221890089 221890099
    0xa110a060c0e0907300605060d020c121306051e070c090506300a0c0305010b031002040b0307031e060b0d0f140f06040213060305070f0207050a060509 66
    0x1110208a0522030030076800295103881c02000e003010b081c0011010001d0404080c44001108410b9001003c52034140303050283c906010041c0001c1105002055640c00040d001140482d6003414100180d005010b1a07030750b88102e9400c1507000c1486011032040c2040448005070038441001054050b20180030400b402211110788075003028110340d240e8104001c250b4201e8560b1f4010401c503003844c4282c80e0006001c0e40e100594011421004400d0300c00310075940300302d240701c41d00d0034140082802070004050344034074404a05990b80c00c099010308100551030340709018202d09103a0710385151007118111800f000a035801d642e100081036004102580710300300c1c01800e91b49282030700708040c869078002d000c41c0b10b5800d80340d030144000310044410071209030421600d0448a552a00100000d095005144402024840d07542c04081006406140c045180c82020044049203154050704418414099030780d0340c0c1d903504299002240c0c0c4c0e801600c60310750048541c050903c0322905c980300504c0507850140c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 221892589 1250 221891339 221891353
    0xe010305150a0f020a020c0a0b03070c0f11030a0515010e07120e0f030d09030201110304050307021302121006170f06010c0501090f0309061d030d0309020f2e05030c0a11 74
    0x14100050345c1c09405810016004548000c1ca03920b4425030500292105811050444c98524070107000da02c42c0c204007905484005420b41c0030881c481e03a0a402c0b40c01c1c09001c2c0d032902229850a1030b41d4242c400f080020002c036010000c0380f60115907100f10301c11103072555840892421840442e00410000106051b60f01178000300d00e000d40c42c108014040e000d04171900007090049410b000742114040868001410380070801d00000c102d002091f141032580455131900110340b40e0701042c0080c403c105c0f01c1e8140d03183d0201000240001c4041003011684552105900c5480c5130380c04840e84942107a000d80204c58280220b80c2c5540315050306034199106000014081105403155010003000135802c80000da0b090030203000403a844440c0d421000b01e01504000d04004400c00652122900e00c100c00405540d00007110a43d5035003040701041500140c0408034180c040c0442e409400609815043e0007080c140070440c20502c10307070803288160143c00b00b240c1800700c0d04008544005412001200d00d00c038841d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 221893839 1250 221892589 221892611
    0xe040b0a0602061501180b22140a2123010501080102090f01050705071406090d032a05060c0a0309080a1d0402070b0411060408010c050d060e010305150a 67
    0x40c403944090700789034006101502d094008540380180742010903042000000c2d1004002049180c0346003035400852a943c2c0b104a105103c030104220004032002000703a4150001c3d01d40c0700041c204030ba2030b50907290000c0c20b41c3c171581120380391070400464205c0c131a116500030020660410015003a286070103400150241e28040903030a44000380c100039450f950026201145150108140080380401e0030910306114840e200c80d5102c004900c2800c0780e15200203103510340d07980c441c0200c0303180160003006008180c4450a0082156041c82d2048020308079606218030a60f00c10049500d6031075000005140c0d95039850003c0505402900078070080c1920307103444500103200100604604200c1d03640d48030403801c0c80703025146545034249001d40a0751041200c6000714010070403030350f07029030800f40d03416000b4030b5800400c21500c116031003164503502c3c0c2040094450b611000400e540d0035000000e109107615440c000c811030304c1c00c5c030004185500c071511900b183c1e0341240380158800460900000c03107200b02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 221895089 1250 221893839 221893849
    0x70803070c0807050909061b040306020a030902010201060b0f070f02060d18111e0f010e10020a0323070314040503010c0e0112050c0301050111240f070f020d0e040b 72
    0x40411181c000159034180008403003002454028081182c014001d030424400780342c1c0320f01019000303602c040412809000342c050450304850003954040c07002c40d60b8480c0300320000c0040c06401e134103d005508107440001d070f0306503020075940c91001004185207041c4569507030f5110300021280498114200f445036030440000d52143c1c4002148423100400015801c1c03810004c102c0b45614054032400d01d00300c030040840c60203039110350321344026188100100041c0d401a11581c1075582080d502080c203034844281e0030703030204030801000d10a8441c4102c402034010345144401604003a00c840100c10b10100001c02e10907201400705400385002145010385481c0441d080d01e1041428001007106891803016a580c04880c00034488070080d41040503042542100c4064031041c8280c5040000d0102c00c0b07000743c4800c0c0b101074001e8404d08618007001440700b8401c900300804555404403002440e0000c1d0140b8044e120a00188503954040d1420700040c4c08150350300140383c111650041ea44141062040c1c4407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 221896339 1250 221895089 221895097
    0x406050406082407020c10050702040c021e030c0a0201140d0509060f090607020717010212160f02190f1505090c040b040b060702040207030201021303120e010e0105030f04020102070803 81
    0x1558019103428a945444080f500f80b0001c9050b0819020004000e000d507130115074000d000170100c5108580f01082e5404403142e005030700c80a90f106143c00d06052042ea00003945c0180e00044000794034110100c85555030301c0b80121401056540c106c80e0805005611540d64520845c60014080c1d042803000c28500303088032030841d00c11407558080402d01040f01c1c007003d5110342c00a19640142914130309444000d440d80200e21407041109002d50002001c2c20086d01613420f03030141c25a1604007451300500c0000c1900200c00004e0200f190580d2000c08584089104c600c005099690006860f00580d40c41c0e0860701d00240a40340300d0010090b0340d07043c02142c095035000d80030302d00090a000820390104411110b4071112184140c2c80d202011486ea21881c050360703069901250300603210f078007909060b8060302c00d078068a54541c0b5100008410000742240701d240341020b681ea09850700c4088070041da0b820036080811404100d040c4006203500c9900048264454410320544d12a25941c40c00c40e46180c00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 221897589 1250 221896339 221896349
    0xf03050703020f09090d08060402270a082e02070602030108061008010b01120504061506020a120302310305010f0609150b03191404120e121b0406050406 67
    0x310034030030025440c00d000d90620307901d4120b40124880c109140710545d2403e003968218240035018001400a45c1c5686c141e070401c1c4514181c20300d1078080d4000c209444a0780f982401d106000c070b10f0b004a5a0000020004034203030640c8a506030703250542d01c840d550b800311540c03085215a02048400e0002e00340c0d001039402410050020042824051039911800c10580c0000c07589a14020307004e80c45030f0f132051040f00c004940788000552900c0310b0507d00c014182100c0320316039041ca4044002002e50b070000f01c03120254000c4050b43ca41d688141011400d91054580c0030070414124510076048400c01d40c0355582142104c1d03020010305a40b80d8409003901ca02d11803008846a9403841006859a980541d4a9214003001c15070307021801c0c1450f0381d0450001801501e9212807064268406105641c441e1840810701c0c1003002c050b1030245001d0586440700180b0138001980321040000300c0c107101203140c80c0d003034940000d0401c0c0801110420300c0d400791004401d51190b01c8600004050b295481000e020348 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 221898839 1250 221897589 221897593
    0x6081302040f0c11150c090a0f0e1e06030c1201020c1002090f0619081902030901090309080a03090614090a08010204030b06031b100306051e030118150c090f0305 71
    0x5440008080c241d20300550f013046a68000b60410356401e9207035520a40c1c0000300d03081e0192280703540d1012555145444d0002c2e88003900e0024041603000780e4107882413144900300e807070b85552100180e05503050761003524051b030103034007001b0f140c031052505e103c081c0202c000001c001070801d00d01241c243c0c50420903019510000d64002215000d40c1000b040c07071b1045141c190354191500c0400c284803210300310001e840c00200700502011071510842501100c010020500c0c06644a042c0201840d00900581c80102c0100e02d0340d040c0081c3c00b041c04128aa2809e8240d1503000c0d81c82c1c5044001d0300c0030545a013030074182100c1000620200c2e40c41120301c001030301d200c0000686903400d500e8040b8151101400c80b5120307601c0300f040d851502d580301c0107040d41c125051b64070f8220305082a0069001d0300c0d881e0080f40e4000220080d480001156520140007220100c0c000e201f007a14901850220445001c0c0161030f85400d90700600e461000758100035104a0103207020115a9074a0007a0005184990811101a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 221900089 1250 221898839 221898851
    0xb090d1220071a0304060e1c03320703150e01360207050a08160b010608060d0201051608030106170708011212121e05010801020306030706081302040f 66
    0x80e40715044007500014082000300341a07828000c0001000c26161490700160100200003010080103410445c1240164411a2005218120100c6103016000452000030b0f01d0014204102c9401000282154680c0ea078201039030b00c01c1e001c440c0c09284000f0f000c6000d140e00d81e81c1414007040400000002031a11034107880d0154100402052071100011101c8410031190400d062400c203440054012840204401079881403107250131400e042c00220094400c030070210710081300900007403128000612030500b103015070303172621400d0f13481c004169003942d00140301c10a44001540940000d00d40310461a2444000c0261a40ea50341107030310980203030340014020000c01c01170014110a6503000403450618464941c10601a90030203036205e80054000500c520b0444030b264010075200c1c2040081c060b0501050083c0c58400032843d4100000036889441e000c000142e943e010300c262409144010054001c0074a400800c56140704090062002210000f4448006a0b968032400400c1e0710204804524 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 221901339 1250 221900089 221900117
    0x7020303012c0112020f1e120d080105010c21050a0f21091109040f0c0f03020d080a1e02010e0d090b0f09060f03040302010603111002070315020d1a0301061a040b090d12 74
    0x90103c09103e942c0589d84200b040c44401c0e500720018906648007032901142070340312070401416100e080c006407020650707400a00070130396030300400412206506448590849042c850115000418000c1d9031841e174181c185000c240d0035007034001d40700d9140601d456503807180c114000076500c00f5058804072480a1701c003010004004941d90403000610000204820329881d64010448070003140c5801444c850000400c00da406e8003071640f266490004c2100080380d10042003010303008101c164200c00d0b603407103103c2d40d030b08034140301d24203600a6400365402c1604040703250700e805600780c1100819a601803010311680241204c0b00018611543c026400450402c3c80e508040082c0303105d0a503071b81e024508162208484540001d205800c0300c2d0f1020909901c1e00c90100850700a0140d80b0441800c01d040c4030884c0d6003400e0b002c8071950002400c800030041d01e5a42e016244881c4400d00c168520355000340310410a50040c00081c00b86000c0140007540240e65650314a2041e154801a036000305080820200d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 221902589 1250 221901339 221901349
    0xc35030307090f0e01060f110d020c0102011b02100209010903020d062304020f011112070b040b070306061b0201031409060a11160605130b07020303012c0112020f1e 72
    0x40100b80620441d004241004220544c01078140603240a10040c05419290719100b002103030900000402640c80d18040824020b4841e010942c00600642c00d18042600550000d00c07071410641564000780600300301c0003840c40c042d400003c1c5960500120850010142e280e140c1c100d0b42081c410100010105030f102450b410020100c45881c0d00c0c0000c2d5400c000050b02d1351468034640203800d0030000c011200d11081c16180119047c40b980c0300c0903000c6041c10401c1100b40038240039034801c0000340c4030303a03517690000c8041760150311034000090090044061104142960031880701c0c0103140103c1d80650062401080e00350550741032401c0d50008081100142080c420a900c541990251902c3c200000c0c101a4680d00190317006043d0faa5141c010592044403003254002c41030340b15040d0b908615100071b01940340e420034411400c41e000b159510421100440700b482c0800c0810000150f8aa42003038040f05c5480c2c00c00004036004481145079a050381d4032400c603184403c0383c1e90242c603182100901801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 221903839 1250 221902589 221902607
    0x303040b0f0417070501171305030d09110f060306060307110105070e030c180109020c0f0d09030507060507050a061a03070902040f0b0304020906060f07060609060f050108040c35030307 81
    0x40540c00c80f038028452030385e0102c240303060340c9820034001c181f64880501c881c807200b08502d0f006246100026000c032400120340c00c154201402994050404100700040c054006001c100ca240d01c64003c00000d021840d02501440d0480c0c10b41c50410134010f022032030182125401d46a080c041034080c00c4072501440c08114400c82807001740d030310000312216084084000070042c0140c8034265008266000d10f001e080040280c03020a400840300c0c16090b081f40a840d040315400143c406004001020070414000c1080300e600301e520000803e0900280c2e150b40f0002c000082038186400d140d29136070b0280f5501041140d01600d80c2080040c0c5d82d40c40c1911500b013804540d84004401c107030510410000d41c0d03030584000c1d4880c10070b0b01d540782e446803200810000c6206210005004502e00140495003e80179840b40050340c02684400c0c4000743c641c00151800d8200b1074000f001c500400006200c25010b0032480d920950110312126110260b08010349503858412108802c107a1002c0100201268051001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 221905089 1250 221903839 221903879
    0x6040606150c02210a0b0103060e07080c0d0309181b020705010c020f030a0206070501050118020f0304031413080105091c0203070611250210090f03020904020303040b0f04 75
    0x5070000014450007030125201c01c0e0000c1d11441e031180c100c0ca0480c2039401c0d00e0a8030f04100c0d090320070544451400080921081c0420399602d0329180d84a020a940000c600080e50782400040c059001c1a0301040030366100c00d64100c040014081c00095440d00001030f80b1010984058042041c100c1400900c119540c0503440744110344c000d200402c4681d8001000c01d21487e01039444000303070143d400c0464a031103aa0784c0029048080050018107100e0194030260580b0301d1030030f00071110401781e101031050780240c1c0710200b003020b010008200000d024011904181038070045542c00d040302020503411b195120340c0301c0c0030300b0303511001044200d1406106014001c40003d0303e00d580b000060354025a00d0090f01c0c00100541e41d500160368071000b265054488140181d1030401c3d000c4880a81141101d9031440700f240111208840e074003850740944808400e1320300b44010380c2003903440d41d000c220303040ca0050f0050341c060208110210740910184000d10300f002e44020003503902ca02d424405030821500c8000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 221906339 1250 221905089 221905109
    0x5070f08160e041515051b032a01090b090703020a0b340f1a0a0b090a20030f070906080405120309010e060709061403010509010614070b040506040606 66
    0x81104107a80140310b106542c1c2c1d06850001e501405801e00204084064100c440341404841320003603203079803100c01404182203400701c4400c0380e800b9022440e96401039041c500a8030b0280c0f81c1482180242d04a464000040c0c2400410200384985812003080c000b655002d0540e0401c400c00e00660600b06c0c40e14000b4800a0780e0340d4600000346006180078420300102ca040105400b44aa038010716407003060172599000301034074040b11040c0c03030140d04018031001c00e07004000a038000a1106080b6218480d40040007428540c01513880d259104010041034a103802010100160400c449034154007440c851b8502c001c4280280c00c203c6000350565145500074010000180104400904041165020856111f20680d200d448400045002d8100004100e506124480c204804030380e00c000850f049034035588400b0604008520038500c40c6c8401d000b1182c010324644010080b0600c641c4801c0084c1c83c0c042c0070301c1c2c1000308582d030f0000ca05c0001d40e000d403200ea00070310502044c010365101d1003008000380e40b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 221907589 1250 221906339 221906371
    0x1c0609060e150c090f0a0312080a060b09011e02010f0203240d0812061309120e040903080105091803030103080a080601032307020f0f010911040204060516110405070f08 74
    0x14000c1c014812189618003d08118040c070a01d5112640c134540035650004c2032400423984188020031210f0101c441214042c01e00d40009040084e07074003101c02c0d10310f0694421504002c1442c00c8107030b119528a00d04110365136414080310303480310703480070310300550341c0c0003942d000030503280d81610070314045202031031080710090f00200003d401074080300c6a61702c980c010301d00c25a482100003103d8805a1071101c820ba424086031004200c001c3c2822450130f0303120f0300c80c40e90500b107100910085030080e5000902041048005000718941030001e00e031300c500200a03001441d030300c0300009401d41d042030b4030407541c5440100b40c1043c0e154000c001030390310207000c0ca401c0001000303030103004046007441d07100b0303c0030b200204011901c1540f0a01035012003482034402c07120702c40d4500862038000c0240ca901554204400c1d900304242d071070540200c90803100c5a5541c01e0409402c1005451440c0402408940440e03101d91220400d480354021103110b403c054440c01c0d140230000304060484540186a0014111084 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 221908839 1250 221907589 221907601
    0x140307120605070512070807020f0c1e06070804080d0306050103090b0105010518030d0207080c06030c0906030901090b010e0402091029040e010f0303200303061c0609060e15 76
    0xd80280c0c65250010004541d40c1c03503240c0f00341d4940c4920100c40c1e8403150a0010000762641040400b80940e20644c22104400001683c0a49a1400180055000222030788892240280030070003100d8001c02020140f80c1041907540380090740c8a80e000300c1e41d981046400078500381c1c040c416031004010a080c20b003d0451913540390510114140100d038103200000ca403c200c800d07844640300240f00d902504540242200590283d55000240f10f040c401c0c0c8181244110f0900340001900d018050180d40d072401d0020450400c2031030780008207219901e6684034019000714000c02d48107802824040c06c50200c6003002c0c01802201c402c014100c56445948410810049021420401e260720543d1807260f000300095034001c81d50710981d4840c48402e0154000450080014010001200d10130349a001c1c0c40e145181e800032001c045103e250ac0540c0050000407600d0904031030103034110485082d0420f814003240d441d101101c1d48550180c4a044e99040501c0c1d10361005c002e2040e5401c000840000c0310302e001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 221910089 1250 221908839 221908859
    0x1203110a020a090c2304080c01031a010804051903032715020f090301020f040815010f0b0d020705061602010b0114070f021203031e070e030d030e030405130204140307 73
    0x181c402c019a065503004404d070254070418503445050450401c1420f56030f48000b8954841d0811b004d4400c0e103001e180c080c0300040d8040d100d100c1c505090440d0340328490502c00c00640d080c3e007004109807014001c80940607a000c444030740700c00c20139101c0d46002840001d0000021780b01d450403041c164154800780c00d41000314150400c08184003040c0b0300003513596410510840e02d50300840c400b40e40c0541c0007003140060402d03100c01070416100c04c401210060302c42d0700340c4030450000c20b02c02c8100320000140140140d521070300c014000658200400f601d04060340d5a40380c5014801c0318800c09103141003c02c441c54690a000d4a64401400d10b00401c1c14107074000020960700c640c0780001d00340500c141030701045444450a6020360700604003941d40300c0c40c0c4443c120503884501c284e101142c1c45064001404180038048051100c1c9029008244800442c2d00940003015002080c07026072000b8800007400343c1e07c2101c1180f0940f01ca85015131030300d18054020340e2003c03800d4942c9110340c1200340240034030821 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 221911339 1250 221910089 221910109
    0x1409010803191101090b0a0b0108190c0c080403060c080903180609030f1c030f0203010b0d0c0c021203091801061e0504050913120201050405060c0d060803041203110a02 74
    0x160760b49080714102d0070015a8022403440407100d03194200103c0409000f80d594080b0301c503480348502400304081c60340045030215804c40c0e900070b114500c031000c640c2c0d103403c139401189018200e00704405120341b136488010306508194000c90340261101160140207601403202608030722004029802d0601d500202c0c04450007642c0090b010303d1011410084680d420004085000610070a5030617044501c1240d03540b009005560301e020034144442c2503484103030f1344202c138100e50b0726545d00c0d400d000c1c52545400c050203001980038104455217010401507580e44c000d801040d01044011903943c48148288007d02d840c1030813003ca45c0086000402c8030980040c6206184801c98150303002171652140259a68015900083d412108082c01c1110b004400c4280030034050040c1550f010000421908900740d8074101e4000f1300030340180000c503050501d44400b0300340503a00160082000c2c0e0b00c5207012851a009544202900a0013821420a254000b40c44a10b04c80300d0300c000d0020b0f015960082400041c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 221912589 1250 221911339 221911357
    0x180c03110a030c090906030c080609150609180601180f02090d03110a0c06030603140307030e09090a1e0605090604050c0105133c050108060909070e09071409010803 72
    0x2458108007440c1c144240c9504020703085d600e008104ca07a4030b03424080009038803802915003504c601c0b00404d00d01140050b0072003a920820002149603560a0127000e00380c0300141400d03550311b107520381080502d0010700c0300303e01034240400040009200100740c0002d4171411044040c003d48100901c80441d00d40412100c4c03a2a01810300e10a5420074188803480c0c003a040b040500510000c030700216505501d60480e40417240690a92001c40034a202c640340c40f4801c485005001c034200140ca084c440c02c10582c074991124030081503441d0100a5101c041312088080d203411010288412110708003c3c2d50301c60303245c000221800410340761505650301951045a824114107201c40414941140341400d0540000f4140b49951a034031001d94064005001c1c0540c54003212500c415065440070790782c0b081c41c4008a4805071765a442c0c81c0c680000f031101804014100392424021401c02060200f10409094010f005103401005454030340441d03080b01e50081aa103d201c0c010320801040700302000001d9030700c540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 221913839 1250 221912589 221912591
    0x1020c040605130e1504061401050411030a0b0118120b10030b070309020f04091a0c030c16081201120c0501030506010804080a0c0b0a0e100b0303070f150501180c03110a03 75
    0x806024130042c940b1103824101c81c0d540098604220801980384c21403c2c19000500500030b2590300c40b401c100903a04032019080a245060001600204d41500141b07017034034060602e6145170642d0340d140c030b00c0382c54140c002e104007000c4442a0410850300313040302e40e4407264542000c0402400c685c0e03101c81c440380182c040010103480e40110000d65844207009240d6400040041080d400f59251015404030480d0142d148041004000f4000c1840f800460344104100c049583c5011903c4803070010890403420180c0d14141d041c00f05000d0383c0c54013901b440c080e020440f04814091003a140810010403142c00c080e04140c1000184012641c12410700b507040f9508c80b010302e0700e03084240320403038041c11200c802501c5d1a4000c0280b0003000c40c40d42c0700d0312000d00202c2c1510b00341300b0344200207415145203040d401e030598010018500400e8603541000c0982d4410b12080e046014404151820fa58007a00106049014105440720881d0184030b01e00107a0700380d081c10302000c1e8064800845900078079017004181 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 221915089 1250 221913839 221913851
    0x105040302150d09030e09070309052805070e040c0f0501020307110f0406090209130509060c07030908011b0909050417030606040902030f010503070e25030605040e06040201020c04060513 82
    0x84000b0300341d450801651804020ba00388500b030040480342c29400e043d0160608001242100d407290052000564002c4000d05161fa55868502c0d500021a00780c0c00024444584080010300c0610500c40203004604400a5509003030909005000307040d80302d032540b05036441c010092030f40c021090700c01181d00042190507100c00200825800b040075825203500c10b01d419000300340550a5409007400003402c0d0390780000002e0307650350b44040f960243c07603051955021800040700c8036441002000341900c00d1400d030030740300e43d104910303070960b01d1070248484131100402c050b03c805603203c07040310000d21070000700f400300303051079150903c0c0c10f40503807030f000c030020380000005101e5190b41c41160002d0520742c1003159a81b070448600d08980f602030090f80e03c00d000b107160008008402007070b40e07405075229804c014a0b248075a42c8003650443c0c00e284490901d51203c3e4005110b1b580c5228002404001d04c01400091519200090822680d80c2d0202e1041c1e1520000740310300c1d115182c080249020020b000161 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 221916339 1250 221915089 221915119
    0x509010302040506160b0105030f1002090109120c030209070e0d02040c1e0503150a061202030a150806150105030705070803040213180302190f0605130c0b0406110c0105040302 77
    0x10b88036a40040e5040303000001c9140d03602c1c168124000300d0f0f50040811541a036201c900f016240d80d4808001d4961b9880700301c803000602040e50060201c2d00e4141000148155201501600340305400c40507110b4900ba00b10401c10b50074401d540607031048240c0b03400e018690700b8070000380103965100b00c00f0380590b85d20020301c0d4a1900070344c404028041800800c40070b0f00c0300390348014810751040b20307043e944003282d4203a16403605214003d04203480d0f141e1076141559100c88043c0b002504018800e154442d00c4000700c01e01c0c8501d0102c204040d01e03000018045070f1501c94090100c900c04034403028100142001000300c0694410241c500c06a8489005607030b0741c842d07000190f80998001d145810740c500d04441c140065050002e410b40144c4240c0a868058503048101c44000086000c0501900310380040400003566542c021688800c1c5005045004a0591130b61070101d5640c0d0048200350300000740c2130000700c0e0001c00c150b0080d990500100801890345c4002803c40c00b483c44002c0c01079612043c0b00c26 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 221917589 1250 221916339 221916341
    0x11120705070309091d0c0d03080402060309120706021209060601120f32010602030403080d05070507050a0506180c0a03110310020a020703110f101202130e0403020d0c050d05090103 79
    0xc0204807204050240c03840010300c5d00f12244001c2518010b901c1505c284240c1800c1c10701c030104206816499448965540d6001c0c0301007503000521404c000d001720b4015030a54910f10707000d841d045019010068454004d8604a039030800302408a21055001404004940c0c1e8130010200100e05110408240d400b003841c4154081c00c00c6490556200241c8901c2218440c0351a0400f8050344007401083c0050743d0b01d160a90700c91086000203011108200034511004801e42c0000d6005801c525009140110342c0e03e90301d04120725040102c419402c04c4c4244668603018200002c504032595014003600400c140c002480c14409100041507409030740580c401c269070520920004903c540b005541d41c0044610003522a241400215025404c15041701c0d56403d01483c400c1c034142010b000d02000040c4508244c1e0144a0100543c8038181c00700001805001d10083c42c400074034030796458101c5801c1c10320b030207414412454204020400316044034804a030001643c4500401141000766451078221b004038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 221918839 1250 221917589 221917607
    0x2090d02060904021e0d050c0a020a0615080a03080f09010614040b12030c060a060b07022206090e0106170c06120405070f15030b1005090f0616030f03111207050703 72
    0x304071954080381185c50071100020654550002010019985e4000007000e207400741d038501d08010b17071200790b101000882a07031203250000c00d06401800d009686000c0d0703d2808052110440000f00d010040c0500110310580650704030341560028881141800d419040850031024080e01c00c5455010b40b19003502c4403880842c40d0f8810700241c07562004184041580c5040550f03803a110b9902d80440000c1c07000c680001d44400541c018200302c880000b5000008a5600d2111400b400d2640e403c0c001846802038031907020211200000414101d2504015003500c0f1400c1c440c00c0c01c0c1d900712031080e50300c03569440100d4440c1c05070044550f94984071404c100d454100310f6000303403848008110000c0303400c2d15222014141c5039200e40d0107201c00c001c5170085c003101428000103c004074800b40503482183c50421001e200720140030340400d082491000041d00c815003200c6080d00441c0345010311340c40040c1c4c14019001402528507009240416900d94001d0040c4003c0c11203040000110702042010701c200c001c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 221920089 1250 221918839 221918857
    0xe06011d1b121504050f0a050907090501062d0c02060705030904020f07050c0f030d0e040e0d0e0a0e0402090402040c02030c01140907050102010501081903050c0a030207090e0102090d0206090402 85
    0x840d441c0c10100b003410710a99401d9030007440010300d40c42801e02c00e1030240a440e00c0b403420442103001684403a60407001401010b000d8040c0e502441c07001091481c210306c034903402001c9541d00c0c0e21000d036035010580113940d92540c4040c0130700b28242500d0441c6402140d441045a41510140da80d00110308025003103000d416500c40c0d00c10300000c2c0c40d10410b04810082c1c40000d026006440064140804000203882c1100f00c82c0c0d0150000b03102c0c907401e24050300740c0900d154000b0f0408903a07083d1400d42c0300d081c90303285045000820080c912900560a0030441d41e17000c0c1c0f2640e00d980e1031b00d017002c0c0c00040c2620401000240729907150100480740b0f601c01d106813140408000024090203805000307030901000200c035800800e00c10007000040542c414001d01e412502150090300518000860001c0321502d13000f41039061000400a41d5064902040141312160195005d040030b28107041c161010b6480801140000d40c0c01406000e549958000c03003540d07110381c102c0d01256914141800300707019004600e21 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 221921339 1250 221920089 221920141
    0x5060913020409090606051f030c1106010b0301030614070c061a0913020f03010b091501090302090a060e0105010c050c0d1707050c1813081309020a020a060e06011d 72
    0x800521052180c0180c0b84545c851541032051a031210288501c0e004160000210400408980c0640c940280d111110070040b40c42c14110604501d04101c1c5003040a074050082c03908000010010302155200e40344140e81041410314040c00d00c2da03401003412408040140071550340b0789000900c205084840d021965001d05911a1460100e024100313660f407044041e4000c90b1003203809112032a06101303804148800404408171500c0d07102d80300016400404806040c0b0004010101c0540c0d00d040300680704590a00c0042003407410240031000c08401030b0701c0303e811302c4460460720001500108018080000590700c580700141d4034104241d44c20081c0035405803040340028004140b080c00305920f001d00034140c42174042c1551801c840c0c5d001000071500031400301c8907884008009110500102100b0590340140700840d500c0b0404901207034801d600c5400541e115803010401c1103100c2c000c0124421111024040780e43c500040e03603511081075030390308507400d0302500051814800c02c04080a88101202 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 221922589 1250 221921339 221921347
    0xf03030f0203041a221a0d02041e080c10050f0901031e14010f05181803040f0311010f02030406140c0609061008030a0c08070f0b0c03101703040506091302 68
    0x10021641758001c0b180080d000894000e9010201400304002c02140c02d00d01c4183c200056040c0d40c480705401c2110342241c2d484d02000005003148010b00d6040c0000003400c4800b81d03252928046526140b0040f083d58024030086200651090304003080d80c044480004145035030301700d1000100d0041903114044080c0d0781d1b003c00680c0342c0c0034599000c03501503600103503850300c1a40ca650104e070900e4581c0c4147e60340300c4d034180384400088201149680d0401d1079603082130a5032401d61116811a0802d400045421500d41c1040040c4240040c1001e00040c0c21300300440b2003420048000e489105600406051100841c1d4503c030380d41c509011280541002c6080e40d0315030420b01d24071510303101c06032018083c00c100c3c0d0002090500010040382c4202c0119101c84071804041e43d1145525081010140d60884255400101143c100000782d0321500f000707c0d0341980e900e8105034001c8204100e0300030350202d604500801440240000455090f10b004491190302c40180741c000517a81d8200308008100c580c0042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 221923839 1250 221922589 221922629
    0x30905070603020d0c020c030a08071a010e0601140c06040b15030a060203010801061509050907030212070f08180a35090102010605060702010f0e03120714060a060f03030f020304 78
    0x260141c0048104d0000c140920703800000100da840e540d9441c920f92541007000c56900160001006241c01e0344a210b002e1086100068181c8203480240c0c0181e004000740010403415680c82040d100115002c4c02220381800400d6002d55500c0200410050580100354042880c4d007000c58640c840080d070040840d09101d90034034224010350020300c6400c01c07560034050013003041d03d84641c0f041c0300c034100d42c2e48201d4210b20b017000b00304074038001614000c18140d08000c20040c21803800b82041c031469994646008142800130300a02401004111381c01c0c0781c3e106010340122080108681c00c6d601d4011403815003145030040440a8444036400128201a07201801d0201300d110001400455409030020061680c1e00c0c02440052712544500038006215a1160365026004080305410031001400b1100500c1d51540d40e551181d00c0607100750744105008000a0b104d100070000b0f150300040d0110244000c03441d140074000581d0305400003d00340003c03d11003130f1195200700191002418500d400d0316010b40c01c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 221925089 1250 221923839 221923841
    0x2280f0311101a101e03200901020c060306030706110c03010c09061b0b0f0a14151207060903080c030d1508060709050a06030b010c080d050610020606030d03020703030905070603 78
    0x160581c0d01e82e0b400c00e0084500c04e1074407900e50400c8603481e0700c80b20703540251510303d8045103682581da8420715564a20354403414030002210202000c00301407540c1d80c0c10045c400a03240ca440318501500ca08001c20401a07c1d48001c0391000072a04281072140c42c43c60800310160a003d03803c0b1f105901980303480040c4400582c01582001100d415031203000880c2c280b404100d03508608181c0141000e00c8010104050300101c0042660007008890001800140710358500c0c4007520a0302ca00c810aa600070409100d880c1045070184c00d119014000c2121928012020780354001c10b1001030030400c070100b50549000d0083c0200c603107500300e410003001045140302440c60203482501552141d4171458000502c01c0e80907202c45d2080d80c00c000c1818000b10325000044014214105510f41000002c8451074005111100500051411000040381f140b40c803400703002a66240114071400c55101000380b054546002c10400c90383e1038180740140e665001403c0540c040c01034132200801620443c113000a00c150302d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 221926339 1250 221925089 221925101
    0x9151707030308010603050903070209040213050f0601030e030702090c070807060e07150f090521010509010504050c0d030e06091203030a15060f0206010504150506071202280f031110 80
    0x310f03403a2080c060b6202c107011800c80d002159450b400368000c00416015141c810350003548144000e000344084000c0302001402d554058803010026054103080c07004540c0c0501600402c82508002541082600e1300050540300d000341c55509445c0f4009040c10500400030704544152780c20003024010404403000e0246e41e880a4491b60a20382204001421100c0c0308048500d4800403d985603081c8504050800c64000c40098144000d12030010b00004080d10a004032889030500c000005010700e014144282003000c02c48880380700785c41c07826800740080d0300a4803100030039009403001c83e21011100e0100b03d082c26803103d0070101c0d100100400940e1403c5401540040c814071454071286540c075642078508148a080c144d016800000c01402542042d074007052515482040d240b0100380d442010903110791020806840a4051113541c0c4000760b01040380c84800860f008166844418030300120360142408074004082c1c040703030072003c01407522400c00c0d2007a6900d481e060f20500c403815000103004041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 221927589 1250 221926339 221926343
    0x30c060f04051503011410020c1009030b0604060803030703020903240420030a0803190603080c010e070f12020f03031308070b0909041211030d0203010603150308040915170703 77
    0x900242001403083c03600080c0c034103d41e400c2503001403102d046400c100960070140c0e42c41d401c40c82102c10020156468002c110f60314180c549507506524110306040c071030060000c0019004a06100040015603400800c40303900078028580140c9400070301c40080c1c00d00408031a030b1308001a4405e4a18080b40d258164a401544607840840d003c420303504064034602c010454056240d000b0100b01404900c411005681c00f2801c4400020000215800c0404070f40c0c4a80050b10350031000725009840d80c500344140d2103a151f44800034481c051404080711190300c0a40148a500e08d4074003e54011900d4542c1c0c0300194540040030b481d22031964080443d5115228401c21511344079043c00007800740411011200c516030054201400d942d1140c5880070856060400c1000304603460b10070a1b4135200902c05820920726a00001d6907075403504d24000d003580c0d022032034003641d401d25a004000054000046400302e4110070000b0440001040308402ca5401e20b6204c903030802e81d80300174040c0020020540c2810b8078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 221928839 1250 221927589 221927599
    0x60b13121e1a100b03060f01030e060906040b0a050f130201051e0c161520010e030304060c0806012709050901060504180b01050d060609020c210a0206040b06030c060f0405 75
    0x41c3d524184044901d0b402e2182d042100c80420110300e042c24940e0300300309801c00604011545500d0034070001d141c948101ea1210140e04118207010070018125030060b00001d25000c2400141042c030340c960500d040180c16500b090030345105050459003e4800e0390550401c0170003036210120030700c5041c0f01a61103894410003e000301000c55108203c89410b00041d42c441060b2654900c102a4040d203428540070400740001068000156800009000f0220804000b1015584a0038145030000550303c88041d0441403140010410030203913845488003000040402a910b410100703514074403a40401c541180c00454100f40c2040041c5905420800445600f940c0c104840e09a000303144181c03005181004080780b1210f801084940707090522003419a008102c000b50240c1d03102e0003902264450b10b444007403a01301c60040a422030003003a0f001c8805e000034103010300d05003900e10029255000104014a40c841c42e0020034010b071000c0004080224004e001e41c1d6071144c00f000b6440c03c03a085486001d1180c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 221930089 1250 221928839 221928841
    0x30b091302090a020a050d09030e03030d02040306050a060e060d020a1a0909070e0a0303030f020d020d0e0c0604080c011b0c080a05060703060311040507030b04021c060b13121e1a 78
    0xc045540700b103441844171940d480e41403107008080800036001284040c0c3c20003400d0525402c26030740610040a082c1e02c48a4016a20392940c82e0060035100001c0c00c10032040d2804501700150240300d1040d80d4026401c0f10300a100b0012880003400005681d0007080f02030180c0f409044510109074010300d00c03940102c504d443d0603910094100c030740b034141a001c1504020045020000a80650070825140101d517402506114039144000120780040904a160a45445005443c40f0090210b074990350019070f515480c0c2814139081641ea45190404141000940c0c4c40c0d581c1200c000d4403081c0c402c0e5500c11849694280d483c0709590340c07134001c24010741d514010320020900f418000d100b04c4d01104d0f4400c400c410300700032140400005200052a103400d2640f04d8881310b40e540d40e5032004019034100784200c280d4148140a10804654668004c114080000c020070720001d050650f41400311003005400881d000750b98a01028075000010600d43d2054002c9052001c00401840c3c02c801c0340342609174480b103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 221931339 1250 221930089 221930101
    0x1050604091112011428110301140307090218181003060c1106190c02012c0703080703030c0e09040f06020c01020906071203140f0703020307030b09130209 68
    0x88902050004201050946110100f41031000070822245a4070b00002600c500c20740104105aa049511b1414896180f06000a40d40c1c00c0400074002e8262010401003d04408100d1400d4401801401049603282d0b5090129035030401c900b0015021595040d922465681000403402e11141c64042c8103c100d403c14075012000c3c1808107100c1c440f1018141040b600d1030716094028101000b40d48200018030701c0003170300c940041101901803000c010515001200c103002c90400c440031642641d0843e4100501803070b040300d045805d05c1070100400c17140980700d80a815014607100c0d9503800140b0911002c2348160a1503050b500024119416444e00b602a034510420442c00010441e0000d0068560000c00c5001c80c603d07501414000085100041ca00714403080004d07000d802900c001c4412144050300545d10301d5140c041c1804030403100305004040e003080c214892140303500130020802c16a0200006224030b02c0307600010000740703010382400701600345214440782c2c0807190300c4181d015890070404981 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 221932589 1250 221931339 221931341
    0xe0102090a170d030902040207061a1003020c03180123120106030203090a0b07091205060108011104030c09020d060e0c13080d02030d0b030304030204050907090b060901050702010302070314030c0c01050604 90
    0x46401d40c00b4040c10720714035030b884103070018400184140d80040e400d002ca4000a0800e01c50145c009000b114620f80118032402080345036030452042108050050056442124000042e00c6a01c9510041c03124140300c00d1004036500010609205002001400e8000c410b00c0f010004141e00341c00484e680000342c0e20b81030705405034802503800701d883c1d074010102d401c04187d001c86441c0d04a0507515116600070b940304012824002c60f1103060310150410001081441402d1180c000850004041c0a0801e40b070340c0c5136400000380c1e82c4100c1104503000900c003200007080d68055030240c00c042c1c04240715410030190f24031049d004000c041e403071100e61290108605e07500083c15880800303140d00851820180f21407081c040d0903020051a098070081c040480146c0d25802032510074a484401020794514120162080d0380c81e400c8a0f034082d44040000c54100c1c3d80c40b030115280e154082c00c01590381c07003080c82c1c1281d0000c2d0074549a41560000b00c24400040e032a4402000e62840403802801030307413a02c0003004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 221933839 1250 221932589 221932619
    0x510020f07050115180e0114150a080c0904030804110d030509011701030b01170a050118171903110d0f0204050a05190e0c07081201150c1101080606040503010e0102090a 74
    0x40f20804040c0c0c00903022805c5070040007000d00c2030b41c0089484109225152004c0c1010f4403001441056600c03200703000e0034010401e800804581008000f142c4440c00442e08000340a0005070030081c0710b10000701030040f0a59501c10340d050180c00d2008006180c24000e006030040c62a5030700150f0900f840b00b80c07074480c3c1c07103005059903003041c0b8000d0b15900e0710b48000c41403001c0311404016400746090101c08900280720b07820901d4540440b041001c01c0310f10780b03400e030403035038012003010300300144040c0c0d112002d0b004181c1c6030f403881410002455059501e80300400d008440c115800b00342051684503000131950054800c644054a4544000380c072801003280307182007440100301c201c80c02e4004110764680c4074040c03030300b05d44d06007035184c501050350302d0b1001c880d4080c01e60340002020010040149614070459071150800614040f5940019541c4600102c001c4016003410001c0ca00007055440d41c2d50310456000302801402080086109507680d4040d4104401c1c051140c214024005034402c6240465 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 221935089 1250 221933839 221933849
    0x1101110c010207090b01032004080705062503110a0c080d05092d19050901051f0309030504050a061d0f0303030406181a1807120206070510020f07050115 67
    0xd80401410050300c00c0040040240d0349040503103500c494081c01c1888030100d107154081108c69585d0f503043c038226a203003402941c852070281c9010000003000c2e1074100d101107450074844002d03000080007030404503050f41c44510700c58014065105403a0401824113040411a400003040e50083d500f03900081c1c642c1c1c014216140d8224401900c0c0303400305810b5464085910301c0c42030041e85031110201c0442c89100e1420101e518076020008140114a8a2403481d40103003c1120340b600400d028200d0303030b80f40551400f4400c05154981c43d0060130035005405a402400d00541a0703502c8682e906030042c001e401b129074018401443d01240300f12410881c03414202c0c0000a002903165440380c1d5a08070082c40c10100c1c08a061290400c050b000520345450f1600281c000d06680708181844604010068412050256290300900301017000d041c5c40035a84a1480d0112406900e419032410458103240468044c03030000fa2001444c07504500003c4003422130f05004100030480402440f030317640c0c0c000105d4011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 221936339 1250 221935089 221935093
    0x2060403020f060126100e0708070b0a053010050108180d051305030319022a10030905010212071413051201230105010e0a050d06020c07030f1101110c0102 68
    0x450700345c2c0200065001c0c0440c841c20448801c040007009002c22580e10100c03210b03540e0032650702001074030b0302000703000041d1019900f403915200d04010080c0c201d2051103c0345285000c00840100c1401020a4001104e00810011101c918020101400e04e00c0a40075a501280205010070707109084070040130720000d010402800e9980b00b0110540e91500000c000717101c0c0e034040282c0480e894a0520242c80704c0086003482400c070301040d80002e401c120b03001c10745811940350354072060702511008a0b00d864541082e160500340ca40c081404074003801c1c01c01d81c06000c6600000380703400b2214044040d01e201d440031390358441144d24620001030340b41c441c1e00440c240c000c03800d2106003c0b81c640a401c910a074280d51000044920909202681e152403c02590001600e104010015542c0064044418010441d40780010904202c00140c80e0300c0b01d04005060300c3c0d80800d281c00c02c001d041105a0283d5000b240d041c0c0c41c21424030301401800203640d021400260180d0040d0840c1c500025074150940050700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 221937589 1250 221936339 221936369
    0x4020d062702041d10080d0503010e060904050c040b030a140c0406150f031812030b01030c0207030309030803040f0203120901030b09010302090613020f040902040906060207150305060402040b0a02060403020f0601 93
    0x188000e14184c02508031314000301d85c00000112880f080140c00c0d46403480d5140c45450b07600d880081460010010121030140c0c18410800c00040d03808a03400460000488001400e00c40c1c1700701281ca4089802402015941e103120060003a8030002000341e8400e0381201e0505c00740e1303214001d14100840030030b010004610754203001c0800340d000c0c2c0c1120340c9150844a0300b4145e80d03441d84511160614001342d003c0461b98a240301030781c55030b16024130400461980001e000783c515540c0d00404400726888090500c24000c00420204040b00400c0340d4040c1e0010216081e1381c0445010f14031540c4880176883c0840d14007148841e032030901e03100407412070341c00038000074a50f0343e03000c180400031101c0e00c40240d095908000100400040602030710282c24003031001600c45080c5035008040b643d464100e00d0035980709120800c00c1544801c0010300c0c08a0703500d000728142e00c0d400040703070290007140c00105c0605008034100c8501980025202e1255000b0b80c00c8590300d103204258907854500a019980d0000c2442d6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 221938839 1250 221937589 221937629
    0x90901090b0c03060105070819110c060703050c1c17130f0210030b1002070e090102070c120c030b19050f0606040918050604050d021b0109090b04020d06270204 70
    0x40e014562005060411500e05003281e230300c0144e00d5000208644000c0404805034192903030000807403106441d807000911400715144006400d500641c1802010400c00140b0f9080100301405403a40500280701c01d004180d00984000d0040c0e02c00c03050603480c00c20350500148660110801c0008819006040e802d0341041030b4080c015051041d4030078006154640141c0b4182303440c1c058850b130442079103130301800300603046c9200c84402e00e00c00f501da80080c1e801130254001041e513100e4003200b01d46170401c045990262501d00501141c40a0380b000d04407011810802102c00300c00e03911b0310001d401c2c03042d08109640c0d40da00c00c0b650428080e124107803c4a0188000e00c1686403a511800c0d41114003e264040c2d1006946c0e0035190440c22542111030307030000400d0b8007a5940400c0300c0c404409a44e44040c200954110000b041c102032841b0b034010590315034145050740d0f15280d044448085010740c09021058a403400320441c80c9408080d140481031554078000072040318800e441c103071613082c0d4103548503010301c13 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 221940089 1250 221938839 221938861
    0x815092a031501080705030c030a0b0112020d1b1412070302150903030315030d1d0105070606150804020a050402070b01050906150a0806130603081b0f0d020705090901090b 75
    0x10300305003500751180340d10508640300c2c1000010f00a041e500d0040030756034105014036003800c030862407941c0a984540c1c0e040c00010300c00d20866041d6680540110407007061400001c0d108400b50b0700c00780c003d044810840c00315520604291007501c6a610b03036841003e051005000c0308592800052a0305e0300701842c00d000502c0c161061811149112800c0b0307040101074800a030455005a84c441314101180b5800142c6060900c8011130251640c18142c0402e8044180c1d01c80c020a0816414104000020b01d5801c103c0a94484800741c07400a081600c0108442d17000341c103030041590103a1041d5080310b00018145424000c44031b0aa03803000c20061140d2074070062006416000d0002d0354070041800d244210045040003801d041002da5a85400a00b085018000a02d40181042400a0402c00d0500103e10088110b0f202000105106d1004110307a06280742444200b09a8480c24040c441000c201c2ca5800a036020598038219810085a11810380b11422100c8400c00245003c0c0154000307901300b004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 221941339 1250 221940089 221940163
    0x14030603060414031c0b090a0504080d1e0603050a0309290f0906070f0303060e01030f0201050a1e0e040509071a0a02030405100507050c030a051207020316081509 71
    0x3c19000c4904100240504000120072021002c0080c0e80e20340800c1c901d0300d001c80100750006d04c001030421840c01d040c1c4989010784180c182c115103a50320b851400c0103001c02038620400d0040c1c44403042004949a2511b00d403100c4200c0da081e000151510303000714080582803a01c00c407410b60956003000043d01802c0d410301582040310303107524a2000f4025010300c1d0b22070f18000c1000d24451103d0700180c1c111442e01804580c2c0b5a002140c84140d103030010300024421004600c126902400d01c3d03506d4100b4400d00b10780c43e22003041d924080b183e810340302d20319094001349800030f04e03c002c460a1155a070b030283c0d2503559200780c0c800c3c000713085e0503050310203038a2a47e180145201c200d11303c1940d24158584000c111080c0803e450803000450019005d0f007440800c0c02100e4a00f2803c07806413803010303100d462f410380e2017003100001c0c2403501e00014600d00f10f58080002140b19000d803a40300301140d0355160791a40310042e5411120070800040e00044101c0808501c0041c040d0451a14110b140e1003030f0200809111 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 221942446 1107 221941339 221941373
    0x90d030522060e012a12110606030c0f1f050301030614040201020a020114162d08030c0a170901090309081203011a070b0a050601140306030604 63
    0xa500044040d002c40e42441c280c1c40d000f03004a4030001882c00c200045c84801400b0404c14204800145007034010741c4241c9819035030403c100306150310358008940300f5505400c40d607440015803403d0903807860008006040400442c0c0e0315801021311030007021400c000300c1d801100410400006004540902080780d5543c3e2a5040550002c3d50360504034030000e05100032a100c2410040da03170829a844040241da102c0015102c500305507804040c0c20940400c3c01600000c400b124940ca02119003550340c7c003038019455a550086c41b81e665422030b0189400700a10619640b405025284040740101007035030000034800040d2601078012070007640300d440c10383c00c50600410701000d403205903411100c0341c401030848440c0004c00c0c03400601c210200104103003813200600c400caa825500c80c80c4510400c0e250404c040a0021506a2a01040704c140b03034951301403400034000846181c28450410 = true := by decide +kernel

theorem cover : BRFrame.Cov 221762589 221942446 := by
  have h0 := BRFrame.cov_init 221762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 221762589 ≤ n) (h2 : n < 221942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
