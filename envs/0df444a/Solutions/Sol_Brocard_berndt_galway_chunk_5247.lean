-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5247
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:14:04.758349+00:00
-- url     : https://prove2.me/submissions/f9c4e0f3-b0dd-49a0-b869-d8da060c3a54

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 943525179 ≤ n < 943705035 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 943526429 1250 943525179 943525181
    0x408010b0306011d070503130c0609060905090105031005041b0f090614010c14010b040203040804050315040809060a0c120201050a05010f030302150c0f0f0a030c14190e03010e0f01 79
    0x2004101000d0300f8050101e240700b081180d000010171090500c10084001003826014000340f100146d4410f00d032090032a22050003030468141801038400050741803501151509015400724180d40c1c000b00105040c0c501a030304074000c1d04008008480d140c0464034000079014001c16081301420714800561070460030f0910003400c5543c15408040510781817014040240d0700b101009030034030703002348000c50303080c15003a80c0601420300c3c001c040703400c00c0c80002000306002c0240040c01c00d0b650101d09991107610702c10602000900d09a60140680b003007000740d1030305440c0c400b0040c0410581810728040310810f5072940c4450014800342d00000d40d4481341001a08130641c82404e0143c6001064007445070700b0f45e03c00a44c0c416101da400016481355402048000640b207043d40d66008182261030b6540c48040340803500c40e0015040ca401082c14404021021400b4904208070b118410b00c2d518180700d40403400c04c2c004000a12103600344000c1d6408030360306440c280109818031010b2001420411a1085214 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 943527679 1250 943526429 943526431
    0xf020a05030615031c17062803151506030b0312030a0f1401150c15020c16080309010e0f010c06020c03070b060d030503011a040f0f0612140613020d020408010b0306 72
    0x460f1a0318201502408039003206d42c10303062204009004105a0314800403c1161400c030065244404205044100d4440b500c07114400b0349201305840d40c02c990303031054400f007079584056507003440c00480401400400d11030f41c0111046507000702102c103c0440201c00c46515401a20b82d0401706445084520041001d800f4841c00e00515074103c01e00d542c03501280e49000e0541c42e00c1081040303c01003141d014012307a0130515106d0b040b250303030031036451000210880d5190030424407101d90024100d400540000301009035070702c11006031100300e0702855020401003000691542281442554000000800d196101405020308088010f60fa80d101d0b50a00b5410741100600d168850302411070202c00196208043c0c2e411200c003401c02030b507044480d10741c0400350300640d000340013200b548070740001d4800030b4040003000710b814035103403c4109444460003000390362074074100038400c89404001c03400706c0c10700400030324490b081e0006c0142072000500e418401d0340d11070391000c07169a44580d81c04100740b600380445 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 943528929 1250 943527679 943527703
    0x120c0804140f0c0103020d0b0a120203071401020303040311150f01050f06160f14060c030a05060f03071809200a0501020a0f0f1104150602010e0102160f020a0503061503 74
    0x106920004a0100c41e070343c0d10040c600d5410540c0108000c245a800e0b40c00c1810752490041c02c0440c201d0b243d82104400c19030b0080168480e1141480000d1888040c50080440b4141a4050b501c2c540da640c40544020381a01304400b2b041c401c0306010070070a484503101d02e024003d420000c0d181545800b0401051b242d25010f0640b00703800c1007050321071403000401c122005940c404c01c40c0d4060303140760070b0a05180512030b038080b803240075600400c240c003c0e481c00194440c1081e030b40100320a48079101840825001888170980640c02600e090085500c0180d4000340106a890003181c0b5092964800d86400e04507103a03141200e90620b1494198900346141c1000b0345028401049418050b403100e2072074211404c0f010b0241c1d50500414418030290032030510040c507025000344520140c07085e001c6440082c52040c031005518140b03000c840380c4418000c0343c10000049070b201e01d84080300d4640354000400e0800032a0b201c00003030400a001d0310240b01080c070502d481d4820040800e40c0d0420715007890b40d0744403e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 943530179 1250 943528929 943528933
    0x50c010536060406030504031b030e0415090c05120109140c090402040b070b0406110c0a030311091906181a031305101e0204061e120c080414 62
    0x1026584014510308440d02034411040c07840d074010791000d001400000071504980000d800036002c2986905504a00d028a02c02d903107403003841c031404106080c0d08108290040c00101c43c09000442840c1c5038004004a80d20181031039603036550340e83e00c94115904561501c0204901145149805181c24049030040034406020700100e114411140059200104501840308010072464195221a070544e40a0140070800f241e0702d248030300b4942011941103a00300c2d0414145030040c06110340d0304055540c8501c0090080c60707010300030b6500f50701505500340002c0324001c051105050f15a2a8106096402c008012000b00541406001018602e0004280007500c036400020855210304c410700b00a000d01c1c80e690552a078840c0c00d0b03008180e00120f60b0241c00c51143c0c501c121242100d0b54480381c4081c500b81d0486500b242c6800d504001e80c09144101404945600c5980c0303800140c0100d4046040c111780ba1203084c0301041c2429070308a070070030401c02c00040d0500080004000010011800410480700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 943531429 1250 943530179 943530187
    0x31614130b03031603030603050a0b090105180c040f20041e0612050618040b0a0b120c0d020d0501020f0315040b090606160609050c01080c030103050607050304030c0b070c050c0105 79
    0xc00c0c0d4911441d07844000120044c40c0c5001498440e90141c40915445000d9407680100303030800454103401660300030705551038240400e4004110300710241051f40c1920140021040b000100801020f4000341003030126283e00c0d040d0004501c182c40509940c91b22880152104c0c02c08040c0070100b10060310024101d05848400e001003038208410450f42c3d503080001140d0f5a5420000c50082c904010341d22200380544014041000003107400140709448001c8100442d210341010050b000c030f480c0300c8030380301c64000f49501034050803c107998807011400a003510b0420040c0c0c1d5607403800ca0b84105646025008040184060010383e028484500300c0112801d101d018001d0b000224441400383c800383c402c0301b000880c03000e030035100400a00a140c102004000000860030038603101c070310b01107090340082ea512001a40302c0a201050781d040e0398000c001042d19545084c0262a1a0700290054041c0310f02c1caa24800051030141c24284241819607440000e1000b80c0f82c428501100140200e051003001e01c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 943532679 1250 943531429 943531451
    0x1e0309060c030207090c142802010209151b0d0210051e15010e030106080c19030503030a0209040b091f0801061d0a020408010c020a1104020405130b03161413 69
    0x164441a074852207000113000407030300d001fa1103100701d070380000c2a080004580e102d208445025104000300140400300f1034210f840c44120308030b1140b20402c5501148000c050000e50703041c7c070702401c6900c180e0b42050340001c3d54800f83c0f91910300303981c000d400180d128a451601840c0c01d8080d843c1c10904100c02a413001018101002d84244024040088076200c141203c0c0340d680f08004001904002030020441d1a032921440d40c0c46d034102e00754a90040c8080014012085514038290003140d405c180a141140c4494400c400654001195180d02030b4486048500039501d109521b4042c2104001c0d9200c4a5156421001004042e40c40315070540d01d4040c3c03c000e1203402d0000c002c440b00a10300c0351911590b0b401c001340002d00441d00025050344c0303025141440c594000480c80100c50280c6804100607070128100300a910990040b150020300b4481845c00c0c4042d95040340007900d03002420340b603a80d030351014030000350396156100c0b004001c40b07000c501c400c13420300c42a4601210f07840d40c010b2101e29246 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 943533929 1250 943532679 943532683
    0x3060f0207030f0e240a02150c1204060f02030c0d20090f0a03050102210109110d0c050904050403081608060906010e1809070f081c08131e0309060c0302 67
    0x901e00c40c106000d92250212166629080041610b00d4950030400005c84040e40814403900405250b03805489802c40d60303000000c28858442c4228500490b0740e19000e040c4030503c42c1e6100243c022901e40b40c44085455006c0075600107144030f00001941c0742c0d102c14030258118141ea5030714610442e609151007201134410300440031a1560300040c3d030345000c00c1220380f002c90422070080e4009041944040303201d07031702284200b001180c00c0501306000c1d4140e0341c84450360703803c4500c1c003d4010300300e1004121001105500390481c0c40e02c0109428440d084c007030071002080589a080714200c0c0060f944404015100403181c03c118451242850054031a10703140020911503c4040e02982c180091014a482c5d1075484d003503020b1032900c625904c03c000c1d042511019648030901e0181c0c83d900c0440e840041000707800041d4803d00e011202c00413948800c1209030941f90264040d20340010940da00e444627001c2071102c809407905002c5000e01d8019289a414000c090000603004242000f000c4800340c00443d0340 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 943535179 1250 943533929 943533947
    0x181a060f040216080304051e030a0207090513020607030201270503030c161e0c05010804051509010e0d0e0f0906130209010c0f030806011103030601050a03020705032203060f020703 79
    0x5403001039840512550850241c03c8208000b00781140010410040010200700c12401c0f1020810f907400881c41c0c0119a6220b00130054000c006070300441c0708111078452600500e4114039000c81c013900070320054020440d940e111160940142c0c0d118880d0003084074900d683c0329040342c012650600060155590151244400f401c0b06c80207600104400808848495810309603551001d00300703081041032000912120034182c0300366201078001000207040d5009070900307446594001c000c0c1c118001d0300501e401202102604010066595030224103c6004c02c02c03001403454059110901032010740400c0000c002c03031003200c4601130340d0003009102c0c041e241e03018400800c00c2a0b05002d600c41304007800403a000d1590703400242120a5907140039040c513400c0095030b8052142a40c07090707000792800d0460f560340d10065469a001035402c0091801d4944268007a104051040c004e580c64902c03144018290450100d0096801080180c410410003200340300e1442c5141203030724151300748035807514041c00c8008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 943536429 1250 943535179 943535209
    0x210e092d060f06071a0f040302010605151207120c020102090a05030706020d050a1716020c0307030308160918061502070f03060b0f03011b0f2a1401181a06 68
    0x10f40800d4a2080112550702034229080b58040d80d0381e03500d00798122810880b01910160055440c059021038681400e603001500c002200340058600a0054012a01f201c0010690810083e212114030410542c44c0500340380303404940d0001d80c59140c03c0c020042ea1a5055120500c207500c0844100702a54000c6020303140d08505080141d10384503041020341d400d900b4104203080f00b614140800c22951052044e54903940c110381c0c2103910342d803002000e01d070b03562201c1c0c080540840c0100001034948442c20540d00f880e5507803403900c1d01c0c4981c2c0d91803006400e418900010025030b40c42d844107024240e8040a0302803164a03a1004048591401d03000c0110700700701c2c1c0009498503803600d06250154032410a1454031010140c000c00c061882c1c404526021100191904001800d4503100d6207640c0c031503558541c01c283c2000c00d0155480a040c9a20409070803101c04407151817490049050070300081c4503c103003c0035894100c4403945264684039404502020f4819a400d419030284501510b034225501000c103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 943537679 1250 943536429 943536439
    0x405040b0d0b0c0a120e01060f0b160209091501080a110a0e0604111c090201030b03010b0105180406170f1515040905120f070c05010309210e092d060f 66
    0x40c2020310444286080a4400c0e15480c141b140d20150a00150301c40d4080f0f80009034410842c0392603283d034000c02c1c86251400c25400c0817111000c00036281c034840813034004020350100c5918603515445402100c00036403002409030071030144030090200010003000c1d2904201d40800855041043c401c40d1820b0207014a40251740e10000850160030b90030031202e4140200002054084009016801030001031074203e001a0500300142500e00301401030307030180c481c161102e43c10301d0700500001540480d10b5900641c01600ca00001403d07802c1504000c01c0b4240c160050705c220204c1c40382d16442d0030181e104440c005800c2c030301003100600b2240040c1010b07074011540447c50f1181030401da803404841c02d10368000c8400014101044519100c020300e0301d588102d0080c0102581c51300150200d524403000038002540490076211011350003076000320002050700300001d0307140403040400c0c6044c40845641d403807002e44101554098440c40c150080304d08400c44080840d10b0114040380c41e152419801500079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 943538929 1250 943537679 943537687
    0x30809010f02491b05100504110102071a040603051905010803040602060f01050109030b060d05030d0b01091508042604031505151c03050405030a05072d0b07080d0f020405040b0d0b0c 80
    0x448181b21700000c4400d9194107002030700349410080020401c0850490247c13041caa00082e558007450301c048d14440814000c40e080c00d151a03000c0d40031741001040c203c40c2c02c498100440101142d40b02e070501030700c1e1260042d44c032103051030300c00303454080081d21100540c0c94550040040d40c0e40400307040c0540740e000120002d1501d420003c9161044e003044010302c00e00000c207041105041c0c1e41e01030a01070501342e079165500e540d20303154000f0b030110018080c0005110400003c01248281e40f00300e00c4c000d13503590b024903000131100119610750015001143c460f04450720404400700c083c0680d50b00102400000c5ca0864120ae0005154061641c00f0000c0c0030078809a1200741401401583d0042c813000d01628030385c190314540b16490320390030f010b0301c2e4001d01c003010b01841120700130f03804c06224400c19178140d80e80c60a00b025410ba50300200307000c4580321800c0000303054110032030091a15000aa4801607140ca050804100984030001440c1c2e02903011213000201080740b44400a4018400360890740e51 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 943540179 1250 943538929 943538933
    0x7030e0105090307081c03051e1b0315040f1a090c0c01060803040906060810061b0f0f0b090d08040209040c0503033001030809010f02491b 61
    0x25070003151600c960500404c0c4001940d170001103207900c000040c4e40700c1502c07206861042982280d40c1560410001c00c0c0c8121920740690040c1000d980014138100004010098070400b4016030740b08a58140405087e50325651841c04c00f401920360380d411190b020700003040389220402c80512081c080750710601c2401c01080d040f0030300b481164000380d583c3c0000e00c804c0da200c1900c25643e900900c10713601c0341c074544100001d200388603121031801402180881c1801e14640304007100c05d20449101154242850391120000412201040d486c040c89012402403144007410134040090000f010201580c1114043d400f0031a4403a2946034007039030455809a540d1103c1c208090112100c0d003250340c040c070002414640307070280500740341d142010214008a92034044030303000c180c40c00c01b803000405004c42480fa106040d0302580d0141031040c4d403441207171042030302200b8000520f000719522a40501c0070180d1040912640c03011001d100d80d000d040c844544441c2180142604514081c010a0304003034011001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 943541429 1250 943540179 943540187
    0xf090402061e090306160f050901211a01031e020c07050406030f2006070206071a0a020d150f271109090601080702120f0403050712051b0607030e01 65
    0x581c0c0c10a0880e840c0b100480c2d012a80865403120a601c1d100748101d4002035210301e0402ca039001a20100c1c0d0301e030840b1070704051040e9915000382c0004d505004a031480c0105001090844102200031400c0c0403507402c42030400c4407085101030191904040c1809401e0204140c107191300c0d6440c19210800507a01d0940c0300e007003820100c65421840c4d00608048000043c00059024901e4081c0169014a031803050144040840d014a805154108400b802040302502d403000141039020f00404441840054030028003040c20400c840d101101a80850080700600582c410780340191901c0001581c203a09040501c91000050720400f18802000d40045104010010040030640081c000c1448080a01e00301500e0f5a0000103484d40034444d0000011200d600c80c49046006904c5a0080c107265441240c802070b0660001c001c441d038803041000000006082000a04000c0c10f140603030110380c1c42c00c0d140850030102044030b0341505000400c040c0f0f00541c0c0c1c520407662405e83c9410800380c001280001170b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 943542679 1250 943541429 943541437
    0x509190c0815190b0a050907030b040e0d02122503020a060204091b030b010c0818060403150501170709020d06122004020f09090402120703080a0f0e0f09040206 70
    0x20740c0c1d50090302d0a0000000518068030b0189100030115480d50b04030506100840f041d02d0007040d888542c0c014100143c3c1040c850443e002a600e01d40807031000c441401013020348204200606140d80703c142d0b1a49600e44c140a03580301c4030795003c64286031004010f418003803548000000c0002c1d00f061000401014002c1000200480d407190045d5200c9a440c82d2050041c400c21041540942c98810300c241070a210b480380ca009440141c40d254604019615010840d800400f5080e00d50265620402c100d907039500d000d4030065100e240150121800304d0220b601ba1241039002000c04841c00c0c20034180024003040394000d40d0b03010840161180c2511440001404140d8018121740740c074138010304140a61440200704000e944042131042215003410f10040340301e002d00302c02100c8000e011040d00b6141105102d600240020290700d1041c0810303040c030703060514a5000b00c2d9190000100300c40c1141e040000040c0d92191418090740811034030b80440c01c1804c12100c010700c03035609030001034110345e80c072003d0f2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 943543929 1250 943542679 943542689
    0xf0705102d0c15150b030403020d0c08090a0305031314010215100905090a0210091802070204111b0111070b0106080a09050106060e0f0a2106180b0610030509190c 71
    0x1072407403c050b02400e4401003a00040024090000360400b1034900208001c03240a0343d0305600818103203580c1c200859506607072440880c0d840300e04010441c0c190b5a40760011020b075000d2805503540308604804803100e40d00b03680c480302889007058a000410b070303000319200c2d502150081110a0680e03a0051844820203a074101016940c0b612040c41600c490005105d003081d4030a03a41216420700c2005c0503103100d00140302c2c181c0140b01c403c030000c0941d41d8523009802d500f4400361003c203c0743d14000480c15560403009000356052614403c1c00044842405401028114000402d00d400503586a051031500705008807420311101401240350b291082d8440c00040d070f0440000c208139174490710001c204101e04285244103074060f03c00c242c42c91910003038900c2191009000000b606401c0c00b206403001180e8071041c1c8000b5550007010040b180071461170401c0b1032040060b650be6203005402c100c03646c0034440351402010301e044100880d071000040d841c026501440131940030b444440c50482081070082d080 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 943545179 1250 943543929 943543943
    0x2030312071101060e060117010f140111030301092004030206030705030402220606020d02160303081911070201030f181b050d0b060301050c070c06050307050403050f0705102d0c 78
    0x4c0013505aa44030b03152030040d1401d0360344084e82c1c01d9404215024007000c3c0203a506000203210100900d41103941e821064800c1810b01c0c8c204070001d24001030071a0002da00228030a5144d41580505924210040c01c64450000185041c5030941c0c01159aa000c000c01c01c00034044000041019980d0710900039101030f01360030300c0784115220750603400040c008034460b18025208014545404500108407044806c4042804036891890b5840031940d01d1000b420b003101c00280d0004110001d1807500400e4882e02c2c484a009541e55500d100040403101d403e00c013003012624010380c416015a2020300602c045421448080704000040b0040034441d00039402a944100408400810001c03410802886014114001c210a82e60744444540070f110f80580103000d41c04403013091103014040c901a41d0060540d107840e50419840e03540707080c503080f0921550b5040e03034042e2000704240d1910000c0300002060501d42030408000102440d102007a580c0c10440709043c031700d1a403014880c400c800000f882608010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 943546429 1250 943545179 943545191
    0xb22020310082406010e0f190b0d020421031b0201050f07050a0506011725151805041803031109031606020d0804120509030c043602030312071101 64
    0x210350740c0c1c054550f8060007403014034840010b00b1580182080d015008028010840d8904107a0030800a080f07002c1801c1c034480c0703843c00d000c540481000007a1030703d4507094400590b0f85062200d0700000c1e4054041080801c01c114004c0c0d40041d62003440082210300c840b001c0740c1e04040d2440140d8040c01000300c0d01e90010fa010541c00180000020542000c0c0e000e40141c801c0390f40c85c1c0c0250150412030801c4000c0c1603000740d06116510343c02c045040c00c00e2025003020f449098540803a29003404124042000150300015a00902c134101181240204022031b02045400065290000c0300350407081c014051642d510017503441d01651500300c0380500d00080075510070b0b0340031000c2003044284c2401010018802d4013408190340340070b00081801a9000003d20707607440000441200d00fa441058840e4243c0201c101d41d5010f52200d001e050707102401031020013000e0b11502261411a5442e0400749078804c900c014410250b140441103a00341e00c2510b81c0b840407a5070f80082520b1104201e01c440b40190700c5d0038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 943547679 1250 943546429 943546453
    0x1202071802040509060405010302061c0e0312091c0909090303021b0303090f0a0c0302120f070b03090f120d1503080309070312231b0106180b2202031008 67
    0x40e0080040d9402201c4004485e100d910520040b0751090000942004007001503000605601c400080206001c8902080140e2110100c606542080100c86034024401052200c2440300344095028070207042548401d540400703100400c0d140d468403600071110790700c48000f0309140c40794040782d581d800885486040030796040c01c050b580364000c4502d104a4040c450b80b2007130009011402806054014001c040c7d02800c540810644100d0082203e416100c1e1845403091000706104400042a03080f10f80c0c0d84901d82080014142180c41c00c0d0a40c1c0d5421003000010003081a800380d80e042c0c41d076410000358501c000030000704d03807120a800140142c00c0100170060f04190004460f002d69104013078400480213904c4044d644c15040041ca03103c0c031070f0604c00c50300154005601a0600c035032140000c180403070b030300217809003120441d030010070350007441c5d55582c0f10142903800340d2104481c0644080e14042100c107444a80e60422403050702e1096000400b0490803040d02da140c01c082c15008081d2041c0035412 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 943548929 1250 943547679 943547681
    0xb0c0f0d050c090a060207060504090515090412080c07020108040b090a0f1b050405010e1308370504082e0c031a1c030c0f0f0b01240c12020718 63
    0x510f102610503480e94034003041e414070100d0b800c0c00f210480d0b11160304003418101000c020702401081110b2010100d21125071a070759011032240100d010704903c94480d1070103140200030910060440da01e483c0200310050041c0d9201c0d40d02503005801c400b940441e9140d5041442c2001111100640b420b450303081c03008107200c008210070906822040b4074902d040d64820910085c1c2e4000d118500c61070590030001042001d01c0c025900145100380e41d841d00c0c011042481c00d4040e044594801050b4602132000d4040402070400b03070310555003904050781041d11300380415030f5690500d44407003000103011200601480303440d144400384c0c0b10a00c0c0c0a010030607050100074014000f10b84404000c0c4502028041282850b1100b044c101a4002c0d41d0880610a61815283c90181020072600381104408034804a609a02c1ea05e518a06c01d007004405540742c5a46194a04404d8005c600c80024601c1512101908403944406141c2c2c81106001101807200042e03060114640c4400100700f0107000b120380081003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 943550179 1250 943548929 943548937
    0xe010618060306060c0f11040e0a03030b0f06090d030e0604150e0f0a060f0c0b0a09030f0806091521030a021b03030409021612030c0314040b0c0f0d050c 67
    0x40380340c60031a4581c0d541421000d85402d403080d000841e81000d514804512100351102c1e00600806082410426410100c4c080321001030b4115100d40042400303034101a490700810754a03080860b020701c1c0b03004c0e6080010f0010f110380d56072030784110b00c2900d0742d40405009007142660900020503943d101c1c1e030f503041e214000c800810000c400081c410500c07600c42d468013051170701e00c04101500300000b490405038140c803000340d8080000e050142d41c1c1300700800509500e1340e007440751700b4000011a94406900d03001d006203050340ea8034018002c20004200e111380340d03032a030142d125014000c1c00143d202d40380040340030900070b04038050040d03040d0300780c2c2c06d0340110001c01014002841c1d8222560040c1c035841890351040418000c1d41c2c141c008010400900500e9000f8007402410560402c030b0900f17013035954240c84158a0742c0e041c04a611881308090803034051050150321078141886c10385c1ea05d4550350780002e58100518001407500e0101c0c1c580d44c01000c50703007a42c100c007400e02020400c40c10607192001071608 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 943551429 1250 943550179 943550207
    0x8182805011b030807140c1006290d0203040609061401080d030e0c09150603040c050a090e060f0901230402090901060503030403200a030809040605030c010e060705070e0106 76
    0x71140a42c8035034200c80e0301c19909441e0b0195950329541d101c080f012500c00c1c0750300d842e1803c0020140000701140ba014002400d0011820b000000c0c52460301c01e440402c1110f0280e003101c00e800040070800402070360012a0304000c0e03084001643c968803843d0180043c030320000c01418551030078070441d10031035500045c603043c5c602001c12a607030002224000c0b01542c01c0d0220b81e00258001c100400b41c1402c1c45414940c002c004211001c42c1c00f403041d404104c564008607000d0317501d07985e0700303a0801690801151240280c881388509000300040c1d1542a9500c0f4030140510260345520400102951003e60020000510362881c40c004d5008182000103c440d00740d40030780c802c080c2c01000c00c001620500c03401046810180c003450801e4a143c0f64040d8805400c00c0304060107544140500881d40c076940d0603c091885011119150983d100c240000c56140d0340090b4082d030700005001c035481e170f041100311102c4401118640c0d0f9801ea0340c0350044c02c100d42035200554009001c800030800700d41041a5120b82c81c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 943552679 1250 943551429 943551437
    0x5100b070f02150a02071a16080301180c050f1b0303010803071403130501120e03030106080103060f0621050118140609160302090c1b030d180818280501 67
    0x503000c0488051502c911020780002d6800780c0400c00c0308000b160441c03000e1445c0d6081003810010301c08040a0b40c5c2c2d05583d4129001c210000051001050798084c4064040d00988204010390030054050034603c13440c03d1020183f640807071110030300708035401003040030381846041e2a201d5035a02c203103035030301d81242d8000c0710120900600a005004000b09a800c1101800400c9015518000040d61155480c1c01807481407500d400d0b4180b0744103c108010f50090000d552000710940c0755041050840d01c204c0400300c156420804204298500b000109070310413043c0e001e14001c1c9c030311442e180740140074100f84200e003500758400480034402d8655294418004000903220306540c4c542c501794a8585c2031420050b0b007007000070107101609100b880307694480c800390131030b41c80c0c1080086041a1040102c50000241d400040c0d81014503d540c01782100120000d00810880545990b030410f00d400755504003e00020300052029070f85c2d8400411800c1c3e2040320104000f04060000000c22054980c0102c40c041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 943553929 1250 943552679 943552699
    0x1c1508070e061c050f0d0905011704050c04051e0103121404060c03030906060e10030512090a1401020307170d0501061b022e05040e070e0a060305100b070f02 69
    0xc000310307850103841494018030200203e129000d0800440c0c01c520000d072081e102d05103905586050420504001c440701d9180c0040075407a060005101c2402d01c5081c6c80995550000e010000f1300000b29018a030000301d401080c103548400c540c0e06800b1100c18120741080e4260000414040d8802000031840c1e402d5442c40d44c449504802140d41d0310451007000c1c0060490207035940030900c82d50003844803070f2007203c1c00704015541d00e1100070348000507251108480c416000410420004010007029402c1000d400390a00100d5000503001c02c02c90b10601d000600036854400c0ca5038030a00c03c4450042d8042d034101c09081d940d40094003c0d030004a20030103201d141400204085000d43e00110b412844010070001110f41380e070034001100003108004049082e18400949000800303a40a04094a680e8030f0741e480720320340700c2d0954806902030f007840c05020004ac04114140c5481001c0030030354000b41008640d945400c480321036102c0040c2c0c841c034112400801d218040005c58130b0381980d440c8c0200e41b00402c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 943555179 1250 943553929 943553939
    0x303090324090a030c1e0803040b0a0b030115031e08161e0209060609030106090203090f011d03030c03040c0513021c05060a15020705130e0f0a03020a081c150807 71
    0xf8031100400d01901041003040803100051500250081418110003c2d442900d99540c03075030b4490304151411034114100710704000502c681e41c400c4000d104011030090010b00d68030914100140542d001c040c0041030780070741c51010b100000c0300c18440103a1090b11950341d02c0d20350158146685442400311001b81050f0207940100002c0040d4880c0b403600246503189940750407041050303582c40394411641554861800040016181c4040d5100c1e480183c060603498084a007200c2c211740c1c014200c2d41c2040020400813516040000a032a8015500e140035a5039484600b482403942c012940055800300660b580d46600d0384094014241000b01e018461680352202c1500d01300385c8004481c669089694000104101c0002c0401004c0b86881401a6145981c407480070801c112021914194426181c60300e08214000030480525019000809004003110582e4000d440349980640a482c6034001f0445e400b8120040d0701c0c1943c801d0740200100803094101d43c1004401082c0d21860495008210740061 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 943556429 1250 943555179 943555183
    0x2601330e10060305130f05160504180f020d06060f031406070e04230c0c060105030a030f080a0b0306130606050301060b1215060c150c0a0203030a0902030309032409 72
    0x102034026040785165407030a29004900401000b06103a00c031245944690001c81c40202c0c000e40a80e0080c0040c00113035a4595840c0c0110180d9032103d030280d843d006090048280040c0302c0340805e6403181e448440c0302c0103800040d419040ea404091700d0a442e2400c0081d032040483d015078100c9120301b40c059120b6070821501034540b07030100d481030081a02d1100e01e880510b0243c1c01004016200b0390030f0528032000340c0c124a880e0000f1034101d42000720004800c02541d100b002058010708045008104403000e9603401800d1912901c0e0b03120601c401032010451103000758201060039400941125440d180890f01c0d481102c0032020306846452420002007400e05041c0642400d450340b0403c101d10340003440481b5140c081c0000c0c1044240c02402820041e560348a000800110311900010078141244009011000c5d0f805403001e4107068042050b0b412003a004026a41e00045180e0300145021032030011a00710300c1a402280d9042c051980000c0c40c0d000b01040d500700103014480c1c00d071140d6071441c1c4510703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 943557679 1250 943556429 943556431
    0x2a01050306030a3302040314060105061b100e06061e010f050d0b041814010522020420130b2a030c01020a0302120a062601330e 56
    0x1e4264000d444120f0110300000c1c0d901c0441081e030541d9280c10074000310750580d8a003601040d082c910350000350810a11000f4421000c207401e41e2000741c0920752400d400540244204200c19816034094020191161814032202c07079071318039082050240000c012826034403600304070340303a5219451180060342c0540c01d00741c481461542c1a15004031128007030700c0607982900321003040c080c41611042d009000740c469000b44042c0c0d8030f454046030141c10701894500201c014584490403280e25080800551040060302000b040c50070070b0b21810950f4850020038060320b06a40303a58140010f10961480f05100c040c014109110040040d140090300e03114080094403403003100700d849440c02c0e2006c1040b103952150361b181591070b001c01c580c41d00910001141c03d982101f403900c40425030114200c000300100c080303d00e038000580001002190300340140c9440c140306111250b030220542c0215031124039800d6000711016a01d40c0c082c00c41401c40191450000003228a00b505014408c100000c0e021502c0c080075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 943558929 1250 943557679 943557691
    0x2120105070f030b1c05030c0607030b010503150301090c0b130b1606020a0c0c150807081003031110152105030d0b0a0302090403171b07020f0f032a010503 68
    0x90242524140c0b0100c1c050034030030401c16802808109290000c44110092a482502c50f6018646401d5041e50302401c00c1c50040c0000149400d01103040c117070344e034081d0840ba404000a5812444a064400400d0048c041084010101c403036440f070200e6000c0041000e0184220207180303e141c43d940b9030342180c0d020700407448150103614000340c0c02000150f140d0041c040301565440c082403041c007203464400a01038503901021004441d0b58410944944c00f04c1c40a503c100607003060340190034004044000d85480b032102500300702000c99040c5507607a0038400285240c5003610b003072240403607858645a9844403442800d0364000101e0101c224036500850110041d500800a141401707040c2c0038050141c040901c8195000380d0310040440141d5400910500031406a59561070442c0300d40c40c50184014040d00d80c0c070300c1c080401110160015008101c2e504c2c2681900d02ca5140d5078203c2c0461000720001610780e0780350084031042e003640c12041040c1850400000e100203101c00302c134030041d01d451000380d8034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 943560179 1250 943558929 943558937
    0xc011704020904081207030b01020709050106021e0705060a09080d0813141212040209070908100b06090d050d030506010509130903020a060501080a051c1e020118030305040212010507 80
    0x2030241c03501810040c1d001e03004c2c0160510b07005500540c031142c0c141c121001c0d000b19958404280c01942c2c100b0452010704880c200c1040554101480a56560201540315850701055820a6020841446108000e010150401c1d4459007441000342000c101c5020342c008620499200b004810b214403101401440741e040b032003c6948841e20381d41d80c1c1a1248800121a1040c48940103000074030354001d099104024488010341d04080c03041001203000a0080c00801c02d5080e014020307460080703048a010341036208001444402c803000304110703001d902405a07114030b1581940b014450f01040c1d84a01ca0a02da40400c0305584940040d40c00d40100c1c00e03403940140700120a900108215440454021f0290046500c0c031815540c1d240140c0b10260031091164001d40351000810208000c600d07560700c1d0382d40010f026011040b40040c500c0380e4040c94500c2104075001c1d0005003038000c4d4000d900c40c1040030a0b5211103107040c10090081c2c00e0690f4200d000f208180c206413450304040c441c0070b02030001642c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 943561429 1250 943560179 943560181
    0x1005150a1106220c050306190c02071404091410151a04150302090901030507080c09040209220807060b0a0b120601200f011a1002070618080d110c0117 66
    0x2185200d03050100303c086038648200c031008a82035a04000980c440d40c4449403184220001407040010345844c21066025540601c0c0c061049075010010402c0c2d40c0d0301510000303025022414035441c009110030400505000d40101125642c015030000d03591105140344440382640c0d680c0b0303803401207850400519240d0609001c180043e60310311780c4441e0345501514002d41000303440b00004090120a0b0b004a038240d0040b0741c2009600e90911410101c0031007221540030902e415000701d0643c0744000d0903140700c070b0f130081c48000340c010702c09100220031a0448451502e5100d84d00d8108028551242c8580c841c0c9000f40c170000b5910ae002c03040318840d1460b11649499510703414015542001a0080030b0315000b45c07041c5141c1c0d498020005444980a4800040303094100c2c500185400746c1c001f00c4982c042d001e88508026100d40016842044801c42e1412811041c0300b4202201280242e40100c4440d0241c5403010454592041c4d21b2482010788000791003810202d4001522224006100520382d07200c680 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 943562679 1250 943561429 943561471
    0x3020105070c151d0a03080712021c0801140916031104051c0c0603140f070c140c01021c120b0a08010603030507170a08010b031005150a1106 62
    0x11014041151003450390752440c0c0d032180360715040c041000f0040302c001540583e00282c50700041390740c00e03842c84050302d035080001e086847e01c10981c4108440030b080c6130021211024a18804c100c01910f60f104e4051207071a00342980d1004040e05002c0c4103003020392a980d40e50402c1482c08810301c0f405032411450000b00604901c100340e0180c4080c000e000c40d4114180800a0203840700419010071400d000e054016400c0c5901d400390001c191504201c0403d407600803000d0902d0700300201187c20110440c01c510303032a990b0642c00c4901400031031000302101c00c0074440d2003a5070000529901a600240c0a540c1e0202c0071400d1031401c010119003c400250507650541000c1e42594880800c0c240050107140806440300446030a4600d26401100050400039000e4240410404010308007100310b0380b0103141c0007452100801014044c0150030f0440c5000001c282003400d1800e00200611016200c01c08070700c916000020550007070300c5a940810340e90806545071a0b00420b0f0944110700c0b0000108649040d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 943563929 1250 943562679 943562687
    0x4061701050a0c05181807050d05010e0408070803090102040b07060204170105060604210f140f01020703170717160f0c0507060e030708010204120210020313050405150409060207030206060d0c030201 87
    0x5000980058103246c01c80210f5003c480202c0c41401c46031165680c2da045034030440c003143c80503882051140020000e200016012300704641010740c03c000c02548036110141464020300c40c0d03502c10074074030344009000000c0000d0707500030340308444144003d105004c850303c0b8258240c0d0720440c0e400f54842d50400c028419000c44004600c0e0550344181d03054441003d030342e1038540000c010f91090326070101555211120b62400c10860313601c4a8000c000750700b0001144d401501400050301c1c10a486203410303000910f000d2151207446407002c140d200803141c6090029a115080c01c0880480000421701ca5030a01640d01a0000340716250f446402011040c1ca040c1007105d00140480040350305000d82d1400198560302400a003000e080300d058410a80a0541304004000000ea00003d041d90030a01801040740301628107c0c045034020360f800315050b500c6882da14407000310f882f07070560301c6032421505e00140b010300d42c00f401819201c0d4007100d0480d207036002000301e0b4800640000b020880c6030304050006500c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 943565179 1250 943563929 943563967
    0x117090102041a030a05070507081c0e0a0605060a1707140f0603010f0f06030908090409050309060406050d05011d04060c02010605120a02041109030a0206070f0204061701050a0c05 79
    0x44001410241c0303031400f480d106203207120640b0880a000c0103010080300700d40b0801d80c0061090800d64a402e0707084da1003140754054000900400d0392554000d94a0990680181402c400d881d42904e42100e12490440000c0c401513806a0140c20000000701c1e486101e03500c80c01e26140f10342d009241151411151582208140c83c1c40c0e6005014180030304940e840707040203140600b9400804425007820000181036000b250780c0300c80105400c020010010505070021521801829100814812850304000740b03107202d0791200642001002400280352940200076000c42040c0020501c19660ba5044441d580c0304d20750b00f19521131030808041303800110303290301c003840791034880c000421a02d5640d00021518902c2486920854008103040000c40c9020f01c1046804402c0d440c0d00307400d144606010a642c0c038a030080c0203001e100c00241c03135014401903042039080c2c990b00500030300101c0c6d107030f0310321400307160b803841006260b503084c003000c07071884082400794001c08500c503600c29082c1000c44000d1068061 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 943566429 1250 943565179 943565191
    0x30703050f0118050430080c0a0806010f02072c1b2a0715033e1e09030d020f0a031b05060403111605060405060304080c0a0c0e150117 59
    0xc3d59061b0901c0719120020480d1180340d542101a07140013016070050042080142981000e40040000500c806d41001c00107800c22402c0c40c1c80c040c18581d5040c180d01d807901d40e400052800a404580c1c0030030b110700c4404002c01d2248031080b640c0c4c40d100c4900440c12038285a40c1e400100760705100138005d0502404041e02120001c80a900114140c1c1c030806003082d1040d00a0388408031000369071214907030140601416800800c11a403580d680702c604013100724002d010083c1c001f44060640903a1081d80106a070722003072441914050740c0020000c0040e5581c414850307035003e0b004180c08511090300110789240249041c10291622403420b640884001812000316040c00742400c118802150003007285138800d9201c0d450f00200000f500e680140f4203203005140d07a031410300350710b03003402103031200001c0c2c4044407130646a83e91607449616100003280101e400c65070b542d1085200d0007007400180101d00f8101c4e1540302d9094500e48501c2c600307498542e010285d02d07002c1100000c41c20b0f034101e480540d040c0d0150b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 943567679 1250 943566429 943566443
    0x5010207080a1101090b12041703061003053402060903040305031207090b0c0129010225030209041101091401021c02071d0103020901060804120c05071208030703050f01180504 77
    0x40c6d21040b000b001504541d101d001d8403000d0001300000c029202e08008040c1c04110300180c154904103001403071120408540034201912400842c001d410740c103405101801813844450114903209000304695648000c8120040c070610011908400000c01250141ca40110186140800c000b0707840300000000740403c003c21105200018602d00d80078050000c03144c0d91000803aa01381c2c00000060951101d003d03401020101c40c16206150380c002410152a41d0300f2034025150411500c8018200341c2140d0000c0d4004e2444010042000102510701806100989484040700c2d25440c42d4980d030741d00348880c0350150b41f0000c09508410210308103210010074510440310f00507107840b091004401d50444441c0c040d00c4510051003145071500d0264090882450074200320b2034182c482c0000000c0c40c48800d0288441800c0d1002401014007a4034081c3c01410120b41201d40d03589068203180e40110364880c0080d1800020400e07401a03580024102d0308051410000050001e1000300140000b5000f20b800c0b03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 943568929 1250 943567679 943567697
    0x24040b011a0a080402030a021011070b190e0a05060a17070503010302010c0f020409061e060b032e0e070509034827010e270309040f0605040605010207080a1101 70
    0x1a658494402c01515107541c5444200700c91509803440c10641d900261644d330801c0c44406201a800d00d485044010141b8082030b400206001003440707048607400c840d80014002441001a54105142c800d9200c43c4000d240322540e11608116103038042800028002089008960042000807034083c0046000500003e03100140c1c1d5101c070211014211703513003503000c101000070740c812a49215500c004d103451040c2c503183d45001e904015200c3e00c0780c8400c01d040718403000750020403500c003000e10001d488400200b10103400e0040010340b80e500880d10283c42403043c1c011140b100a800c038111014501c0600302d03100b41c159031509240400c600e03850300180c03070166450383d1680c0d540e85200c00240c2d80048110388011400480103014103907416000401d0480901042c03114900ba00c100c031a03c0d0000b0210b5042000044035090307406c40c49440c0c5140d0f07005040200110401c496a4005011241e0403101000b01c00c0e074542c01a030b115a158820380800b0b80141d8010780c040703280e003101c100100c0c0c014901103420b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 943570179 1250 943568929 943568933
    0x5070303140a05010807081518150108060103171215010210090b0901050705131505070209070e100f140702030c0613080709110d0e24040b011a0a080402030a 69
    0x1c0850403100b45a006440b0300040100d603e05000705409400110013034400118101400000d090b0f000e40080b440c000b141d100e0748d0b00800203004480c002d403008218030909503910345600da61990203000940d250b46180e0b100c080c1c031482d41c004443e200654141d001101d40d55110050140a00034040796040d8000c2d00c4034180c001a070740c4512600c0c5442052001428182425098216000205501c050100070841b03a0441d4821801883c11528030007150610319081200440e00d034040c1e840001d4110401c842441911130304001c007840103000c1501e91403001411400d0813141d0070000314800f40494041c4c1240300c03108490038018101c050024080350301c00c0c5081c80c04030f0f00603030044055050721031286805000201d0300780b01010041a111405101041009100001d244941e514000e8999a108040212a80f041c84180e001d0808501200c901c003c05001c94503042302c04071002c071003030786a4030b00210f101f00001429100d8600128540750400d050040c00350307000d403400350007a0b034544540148c0e880 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 943571429 1250 943570179 943570211
    0x5010c23010603060504060e0a020901140a1d18190b09070522140c04050103020a030e032704052a3006010e1f050403020a0617010e04020d0305070303 66
    0x2c02180700d0000000c0034507060600b0021240c61107030a503041e0300042c40f0b10001d651401111415142c0c41590708034907518075400103e64164961281c840a0500d040d5020400000713180184204d20100232111040c44644285487d5203410712403d02c0610160170080215040800d000d60010103041121707250b41d154400684a48282000740c0110050816100e009440c540205940c508911342055130724180700c0c0302410b05024502590b810035a01082c042c510900c250000c452090700c52044e84d81d44c0180450610b11809214259403180c90160060000c50405102d480e128100320441e00d0100051500301c4e20300c0944601d4154102c100610846441070321406526a202400e040c41c0c5030044540b0f0741c2c0c4d44c050b00e030091050381402801d2010203440d4039144000e88e45001285c1c400a581001504141d40c80d01980e00080e4010b40051404540700d0b03040352489041020401881d0201da03a16660444500c4045030001d42002c8400703c000d00103401200a024031510a0401044c203241b80c41f0160 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 943572679 1250 943571429 943571441
    0x6090204030602270105090d0317011e0b090a09020a02030c030a0e041413080c120313060b0d080717070807120f260403051e040504110405010c2301 65
    0x18802c60340c002002c0004084c10944113801340c0e43e1403040e48021142500181581c0100380582c0e000d80c041904c000d04143c030400320301030010589d8880d110256164024500407401c2010328154520006c28042030454001c41661f0742c901d401801c1c080b001e0b04101217000690000121035095200c14808059501c0050000d4400080c0780d540e82d91414840008210a0342d1410b191041100d00e0042802089030305e04e40101080b81c4c00201d100e54442c81214090300c0c2c080481001c80c0b070810044144100c030b0014200324004240144002d0020b00c1e040020450125a106002440718404101c8800014500c08501c545d000d050041541050280d480c1c03002c1c0c1d54000d040440721245421180c0b110550040c000c07400301c9000e480c10400c41e908038441036a0b080940c5245d881d060707981e07200041c100340c4100b0454281a29081442d181a0100b0094040caa003090252600c200d06158440039003409007001e07142202c0c416501c600012200341c8410305860640c1e0203140c09103000041414461109000310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 943573929 1250 943572679 943572683
    0x60a271a0f060102011404030e1e0d03020307050c101b150e0d080c030601090b070602040b120702010c05130b09131a190f05011b060507030501060e04060b0a120609020403 75
    0x41d120314901840020b0854007918a844008480c0005001c040384c4d1004140640103c261650709034109000403440c03070341076103442c151703801205494600101580400903004c454811402c490071000c0980401c0403040d0521030340000505103d42d8020700840100e0500d208a001700c40380031000312005412400c2c0d81e640781450311154007440180030641d074055800c50f440341c1000c01c0310f8114100344000078400116441040019000807401c40b0500c900390381190002c11020100b80d0741e071400800c010303a081d041202c0b0321003d5403030b121041c0348146c025400c4412440045016503105410908040d5181d04604a140e0704841c0315100c0d012104284d106610b41c0c10f0fa4421030188150f4810100305c013511000d400e00660015512041000002246540c003e6407401d0030106004800742802d2084034105074000340401d0304050500c000d0076055400030b816185185d480c50051080342e0b040c0010340d00c051007100a600307010005580801d100b419003c0800d2a040d07000315680ba5201aa04140e820030f8000b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 943575179 1250 943573929 943573951
    0xf03020c07060c03111f02131d0414191e05151609120204090f080708070c050d0507090507090305030f09030c0a0810020d1407030e060a271a 62
    0x1403c81455005000c600103400c1000040c8000d600407030700850000440028102407540110f43d0441e090030a690030000360101d091a428140b60010000f180648207440545074180a150310071151040130440c035148081c0012207441d800f019544103100c000070b0102c84002c140308441c078503000807001e10440c4074465140704420101e0074041c0252041c800d00c012a50700307000c88100108140c03c1c0d0208000741c02e40c0c04480020740151300307013056800c4d1099071130000c00c156400100b4104010b004000352021500554103c259140c9444c28003104a000b40000b030f00e194440c071810000c50006810040e44815240341c0040301680c1c03590340600d1034208900c0d08034039403008201100241001c0011150314030044900720700c0c680c0340c032804944403208005040011900020039603009142c07900600ea103004043c0480300c7c10300d41140000d0007462a2001342405018040c00319180103140e02400143c8060312040c210000100707021000c51a80c880310860300c0190340c000700b261038032440703424034440c50b03c40301c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 943576429 1250 943575179 943575197
    0x2093a0f0209151e0108061011060103060603030e0f060316020c130501080606010905060a1803120201020a0201050109050915190203130b0105030a030e0f04140a0902040e0a02100f03020c0706 84
    0x10491300d80490340703082da4128050025110039a904c1000d158000b401035901c01c980c4485000e04580f14415801a841d132440b58000003c04c102560780301d01c0c1283e02070341d00c0c05803104031002001551111403401e946c0c0807405002041c0d08001e600b100c150007544600480d030300a90725001145403841359415003a08c09968200400c00c070724060050540c03021091900d80f14990500c400603156015614211040011340c01c03810138410704640c10200a1500560851182e460341c080c028041d501081500005508281c00003c082e51540140e41c0105a002e0242510205110040d02c28280051009485181e51000401a42d40c07500c001d46c0100c50540076682100350a0402440e141410703130009000e940020320401c086a84040d6813600ca0b00c3c111030400c1080300e0b501c001000340c03480340c03082c1040c10f100c6400d004106c0b03525440070150781c1c07003542e060050030b4990007125140e580031040a5000152180e405100303d108840c0d0085240d401c0c00c005040c440080010341c40c01400c2e030491700200b07101701 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 943577679 1250 943576429 943576471
    0x30127062c15031207060902030a0c17060106020c011404051c120c02030d08090f0708010f1518020f0d090507060e030d271802093a0f0209 61
    0x1108440d8400032000e0b0754540000d80c080401d6580000140a28103000d001c14540c0c03c0004a400911442d900142214007144e0203042031208080c0c0d42c4200701e8071450504030300e0355603007010440764121000c54001d0300c600c41180005541e14940101c0d50009000c0410000c00c0a6a0b0f401c058a05e070800c0d1501c042c1408060301d0840031001e89071540c1c00a11507031122034030060350300041c2c05011052501e00b045c5251101c42115180210080c40c0d00c1d0705004140d0041101c8005601003064040c96440500801c02c0300d07401c610807081e0b03d00034000c104c2c02410002c0d4241409400801130320180f40312042c9000c1078416514100c91800c3c10844013500320650810103940d0220090092903003c40242055580d01e05000e456000a0001403d0b001902c00800e20082a10300c82c00008000d101203407446910500280c3c03000b503200c91002c900c07454907043c11008c01075010084064000c2d14048806201d02180c002150300e881b8007004682c28901050b0140042c0c503140050760058032281d000028044041d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 943578929 1250 943577679 943577759
    0x5040504050c0d0e061510090305010203090a02041104050303180d20130608101109030102120f16021b03030913050a140c070f1e03020a03030f0203012706 68
    0x100880b114240d211605000d10241000d940c103034540340c110b031800b100c7d220f4024207880e4500140e001420b0380d4404001c0003159140400c4503d4014401c40c0c041002001075111440140501d0007a980c160380240b00c3c80c410002904407030349055000600d0100f0503540f650b074a00003031202d07001151401c440194845601d09103204050b0052144541c240000c1d414990216a03ca02d46a0030026040d1500c0240d402150307490200c590240b1f01400130b65a520001801c1c082d010015600003210640081c0012021564102c0f4092446102c0c0d0148c00310702510207015200d422440002c42d4980002c000300c13081c0307a42c1d00745000116996114040340038600040d55408407100a4140840c9045046c200075841d40903100b20f900c0b080c0d000071011241e5469041445445c50703a43c02415401c400c0c2036010040c0f6030002002c041d007070320a95051014098480e60a401d0340002c1c0300f04202d5000350350300032030180300d40c5060b500b0900070800000703400d41e903858403a501c4c82001c58402042d003000600c03220b540307141 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 943580179 1250 943578929 943578941
    0x70c05150402062205040f020901110d0804030f09090c0806010e0409030807050a050c010203040803010e100311060d090b0f0603011103040807031b141005130c030b0705040504050c0d 80
    0xa60308255020324081d004039045100c0e0144c2c0202c0c0c001013600d44554241c00c0d2880380007400000d0720800820103803020384030003540501a110b002c520f0203429050600d030001425a00509aaa5140c00648a560302680c115540d07070345840a00407200c101060004a9114007202000d040d83c0f040001c4c14002c001600c6003e6042c0050b0181c0d0500b401433010035000441507400030164945a544d83c03402020484860043e00741ea0b82055000106020a1010040207107060312490442452103440d40c141540100440784001030241001d540e15024519241c2d018120703003001d20304003042034002660758101100003200c82d608010700c68424402d0900b02403040307951151a02301d42900e14241601c41d03148500072060006c0400c0100010360701180c0e85000e001480d17a5000d06204902c555518050340c03568000c0c190446081e150200288442c1c1c0c2085170101d00b90f4000f00d01400c21400c58550b03005801c0b00070030350824032004200c0040c1c692600d1281a1080c0b161800d400c0e260b2030014040c0c0b050f030310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 943581429 1250 943580179 943580203
    0x601110115030c0b0a0f08070203040f180c05071106030606191d1e0420070303051b18010806031e03040504050108010c1d040f021c0b06031b071a070c05 67
    0x18070001c0c04070382c6c0242a59060f85001d0410f002165550b0764200e14500c102e400c0040344103203014000401d03418880c103050300700c05c03400000d00100b1a0160308032014042d289018082c44441c0d1080d040ca070910400540d00040f02602e1240703400718080d8148009000070984200003400b03407a01ca928030f105145041e40780c5000321205144c49401c0074200203481407555100f0710403070b0b0717035801c040320100800004a090400303108910303140c030444c0c10064000c00003202d0400c20090701005407080c000b2a28200c441a080d12101d0081c5454004011554050010892a018440c01d86040d00301d03804802201c14140c2450300956840d0304000612003135401c1070344060142c1e8100568518903a40042154000c10a00e15030500c50b54048000500a00032447c99505020310000c0e43c691440b903d584010301c126001e00701070140007802d10901c000d6100480b80000400d08180442d0503a0302c441009210660190703016000a5112400035018508240d84180c00704482c0103003403041100a00512200b10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 943582679 1250 943581429 943581449
    0xc0c0606101d12010510090b0d150213050a0f090f0b030d05131802040915030302060a111c150f03080304151e0c1d06070602030601110115030c 63
    0x546541405040307210100070b42002040a802c210b62640c41d55020040510400350003130049080c0003c02c81000f03900380c0907130510759051860700c5c20721341050280042c0c0b280d030080d030310303401140e08459000c000d40203c07a10a61050740c1e19400034040c1d80c1c0c2c500c8080504008010103403511b00e05011a400c03100d10000ca04c0c0210f040408030012a600410a00004082401d00981d9401c000d8038031846034050380c1120301ca104003980c1c1140c1c1d0040c150f003d00180d4a0038901003009240182211790004e80ca440b0003030042c0d0010001545940958000354000c0d5440050a801d10284020301e4980900003020b501c0326603a141d807044aa8200103002100a04030309800ea4241c5086031140015480010409084030703202d10034041d1826041d505c0a0280710101c500d101ca035215480840000c0e00701c078464440041d58026074200c92042100308100d1009004008918000c20342c1d0303510f0082d400040c07216040c0f004c03000112a003540300703001d00352007080309400500e800d0f4214545501c200000d44c105100ca1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 943583929 1250 943582679 943582699
    0x50c01060b04151b020f0d0f050a02010807030912050d0209060c2b090302210d020625080a0f0b0d08030a050f0702030306120f0a0813150c0f0f0602030c0c0606 70
    0x1410301400321310700e959010341d455017101c60306502181c110021018001c00000484a42800f40700c804500c0025081c0300b40e0f030720080398403584421020f540c1c0000c4040c0002550341c401880590094004000d6121848005410070b9203d00000c1d00075000b002803041c164010400c410244002d240c3c4174141c01000607801c101c01804c4030390041500e03c19020003401280c0e001035901e4480c100c1c1c0c603050503c55014040b19083c41c02d00030025101c01c426280e03044000702030310140464807070b0039061100c504200d540300611540d406e6104409800d5004640c59071a6030b9a54801c3d550700c0305144031051a000381d504598a0810380160400c48500030a1100b100d0701c03480c240540e06078040120f03504418102e03000c044a14903558007078200080701c2e200d001e0030300c61403465100300103628010b481f0321104512020310041e80c0e03850020560310007140c2c03c00018a965842070015510300c1c40b0708106801028450301c80115076a03030304201d034030645183c0c802002c0400c0640e00c8610030041c550380044190b48880c91 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 943585179 1250 943583929 943583957
    0x151803040605030a090609060b030d05090d080d020f04060f020c0103050408040e10081c020c10051c0b0603010303050d24090e0c0310050601110a02150a050c01060b0415 74
    0x90303015a01420003081000408102c40b610319800201c20070303402c003c0410504e2154a084070040c4200307022140a8018401500d0010380138406a0b920080090400041a086a900c0e18400d52000c005040590303030030b00c03c0901d00990070000c0d02c050700740c076201c03d004504403240c003030300d401c40c0303100c04c503042604080c1080001071858007070f14100c41c84060100d407103448040b100107081000c1e82040085100c1c03080b80d0a2201401900010505210b03001d50328102e13008010b101042d50003a03141d07004540108451f0046200c0e1140b44006100c10090000d407004c5940b000808503813007a801500014804101038254503618031071403003007204410002294180358260b0001014081c070500601ca41daa50801c030583c0401e00000f909024000c042e00c561000c1c10300c1803402444296070f028009007101e2041140d04000050340c0c444035400030003d020200ca000d4141d0229440b502e051010001c5c14820036449840900440d00a4804c1601b210748403401c00c4007201d1214420701d40c02d01041060565028 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 943586429 1250 943585179 943585183
    0x216090c020309120c030d050d0b030304030f080f04080163080f03041a010303081f17060a050a020901051804020405121c2a02030f030c1518 62
    0x1c443e80041d101d0040701e01031a400030f820114420140ca4250040075042d20509502c00020080a441030008100390403a0000b403641d207002c0d50100504800c4080101004920071070080e2000b000c2d20084540307000d46402c0b0303190035a004100c180c090011440407280302c40c00407040c0709000e020801d0340b401b00700f1440d00590104107102600456883d11070b852000d048020115807050700e50b04174001c80d1366002881248101035104480580d00400b0254100c40c2c20590342101c00d04aa80544e1041c00d81c0c0c842001d0114450480713610b600e5450a100000901c0d0801e1280c900480e04a2401500340c1b0306e480d202e0203055a20080051200d20710410120040307a03009404d8815020702c40700c0b030f403c003120044085402441150041c50b0f0101da03d01d00202d080f00c0001d249a0601c10f242c5044400d001e5902c42035504180040444911030100107400d003d4084810480d0314050001f03080300c1d03407403400e5080c050545c0d02c04141c0000719008407ca80b40080312400d0219006401e2051640d4805205159a5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 943587679 1250 943586429 943586437
    0x10203220b073e0d080403050f0903150103030807030c08060121110c031305010212090f0a0e130c08060f0106050d0f1508060604050c030a09020102010f06060216090c0203 75
    0x2007400001c00c003031020210710f56504221410f020703400c0300410002c85041c1040c08240c10840034a4031690205040540c42440c0b003901482e4141c60b46800c20a003002e10740026009003003400d4141c441d010f8840c0b004402e448810b802903000e6251010399042c81003006040d90300e001046820310154100f8400b03184d903c074900341d10901414810081c071660101c542070203015000d10a00f000d14001c1261020f4000c0840100382d219a141012314003141d4034801661900503256080350f030035100b80310107111418407045842c0001c2c40144400d403c55141d902010302c80c102a40c1c44000101e9000004003000359100000303000c0c10348003009000d14605000e500a61f481d050140d5020480042085070010210b6000701910101110080c0001716039000c8020088202d80309031800c5105403c0403802608080c442d0501a03804810401e155598a00070070b00a404e11f000101e0442d969480d00036100711051041c54041d0030a68080c000260341001800d00480440d004482584d14001c1400c40c2d09400004030303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 943588929 1250 943587679 943587691
    0x2030706140f0f041e02061b0f0d02060f010b07020f0301090c2606040609020d0c0e19050402130c0e0603010902030402010201110f07020f1201050711062d0c130602010203220b 77
    0x4005e40003240c80850124090296021120340115110b4208001e000c6540804103d90600b101d0011070b104070126038410702030750000d00402d03002c2c0050044100d6000207140850006c1e07c0c0050108200000c40d017120001001503e050400b030209110481100d00400c0300c80b040322401c4483c200908040e1038490350042c000a088030755071a401c02c219166640d1010280747c114010130b4070580c1d9280c200345c00000864000c128098420301d024807040003489a1806141c010300100307016420903100340c0082210802e82c0c828130007070754540340c0c060340c881c00210f0180013050000b5807607052610000e42035808540c25108a07500a1065142560100090b10811070301211880014502000410241c2508410b6003040e9401c08080000c035a411803501c0c2d4401c000d0f1001c41d03101d0390b142111000c00d40c14003002c0c0440c100c1c0c80c41e01545450200c0848607000803200c00142e01d40700703080010354001c010a07841700016075004010408040c086038151620302801c050038200741c05c0f195680006940009240c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 943590179 1250 943588929 943588973
    0x10050a0c091406030a2009010f030c0c0b09120f0c0c04050c16031202030406020a110c0123190215070309020f0d1b09091b060806010c0302030706140f0f04 68
    0x3c0c194084d950000c1c048041c4e85006d54080010110120310240d01c100c112601040341d4403556034007180310f0311580c8110541543d40b4005024503640b02003040002038100e40047c45411004281460741c08000d0008200b8403285980d02c03096202c6540c14121000152803255160004101511440c40c01b00c5140d00b0101900c00d055211501d0240d500d190780c400c5007103445101004020400a84e58000c0c00300c209540c5600c0140040b468015070b845100140c4140003c40c10310100045c141b05602044201c1c0240d03100f2401c0030402c2e0501030300140aa02c18000503449608103030310600d03400c4000f07138028070140b405202011154011400480c40c121455008004d180d01000600201000810f0a0701202d402d2196140c2d50384021400741500407000e8031104101d140070001c1500c0300c482c440c01c80d0610384510312540c7d241401540c00903201c0000f50f0030750004001390400114644a000341d05042440e252a0f141044241c3c0102001e000304500c14200411050001259280788000d000104001d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 943591429 1250 943590179 943590181
    0x513170a08360306090703200d12030203010e010803030108070506071109160f1b060b1c03020105070306060c0b062116030212060f1b070510050a0c09140603 69
    0x1500c0101102d628144440c04268602d140c01d24952082e00040c503040d080f022500b458540c43d100725140c0c241c1c0c1c8402080d115a1107221200a40a0b1010300401c50f0001c0000040350516211140072245141440c80000d0303000005102242d2420380150140031042d00541c19036043c281c5039580c0745d026004017071050030302146510402280541d603074424000540400c101d07040c00ca44407032191441c0c05a00c00411001000300e51000c1c89030700c0040c05c01310b158848810b10151071711303070500425500030615001001124004c940d0f009040e22505520300c2940002450b01d046240101101d1640d0085410044d114022001160f009000f154000800b250030840c602c41d25265034480400c024001c00c081d0090b018000c403005450051001164002c0d1001c40b080a1640070742502c3e000e044030030740e0104000308041500100742d5a0b0a103905440000054581011034071410702d401600700502906a455500f0404100b400d40902090406070303040119099081c6003040d04090800b01d80907001d850080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 943592679 1250 943591429 943591447
    0x1060f1209080913090b07020109110409020409120c060b0108010b030f0702010b0a03051f0e060c030a0207020a080d1e1d03160b040e0105090112020d02120d0513170a08 74
    0xc540a83e6402071520020514425000001c0e06140030240ca0b913503c0b070b500188905006005040100d54003000612203485840f040000402a0003801c0c0e800c036640d4201c59000598800514100020a481e918105001c901d003050a8404000c1c05c0b40c100007504004114041403e001d80f504404d51305181d00040c0c0c2c900408034010515103481b1540182d20100002c01d100020403a90400c02900a0312090b80f001812400243c40032030004509660040c40004c1e00f403400703070000e560400206100580f42c64010380010360b917040550000c8100c0d80124115295464020065100510a0203100f0720410390511000e04000c4000c0c04504030300a070004510f8490303800380414651072010f000ca101303840e525141c96032659040741c002d604120058100208052804003c03c41c101e5101040400301e00c0007550070b01c1209a005141280c2010700a100000380c00070601103008640c0f4190341d455191040091500c1152506078031101c1c9a10b001c860035440705401003900101260499409a91780300c5403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 943593929 1250 943592679 943592693
    0x3020105160f121112041202060a0215040c080f060f0610090905040308070206150d0210051303062004080601050603130501050112122c040603062301060f1209 70
    0x181801008074a9080c10714201075040001184c1c03946204080340c0298007040b00c0d040f50351049016050369080340243e910300624003840189542021803068400082207000000307071244081d5011505440143e07420301859004100492400d0b0300c0c0001060300e414101d0724005904030140030385004001c07814407142c00c00c3c050741904004240011040240345018100141824015102a0300500401c00400e5800082c09030030760b01c0c40b40041c545626004594200940c1c04602c609680901400303001d5943d10480008400c4000c600039800480c07031100840c2e0810b0120501e54a100e603461042c0814098007900041c81410740b6801d4603c10390369290f580003010603e040302001403440d82410004030b01080c0501c405040c0c184120400090314401e26001d03103121429100800e102015014031401010b400564130b51074441c0540009161600c0e5105d860544080301c08a4803100884282a00b80c0b0b251004640c1c01040f5501d000d41902c05a0038000340210031064503042c07042d1b20f46803500144000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 943595179 1250 943593929 943593953
    0x5190b01140316020c0916030f0906090302070602010f02040f1205120a0e0102070603020307053c1b030a050717041d180102040510030e1212010e07090302010516 71
    0x4414140c0d07440e4503004150010000343d80c4070420042c0110010410036003060021280070711020f085150650102c02c1040300208916080180c017aa203d034180c201082207481200075450080d17002c0e291050521030043d0075102108091000548104030421032940410b07041002d035140620780070600c10382800d103503181801402c4040ca650f170000601c0e0700110b400c00c10f40d03001240203800769010700341e503144180c0c220300049420002240040241c00500c3c54901451141075007c4808041044184865141d403101074444812055200052000720808800b10450000b40c10034002c0d407805006510080c0700d400b52000c004d21004c0900c1110810076049002e40e40504440d81202540044400030481c0344002a18400e101c1c61143d005d08040d810180219800c1e01d030043c1000d904440418002c400070305115072040010701404000a140d04030700030040882da01c0c0c0d41c184008650415141013031070321018042e401402221242000140d0700310050300c80c80c030451f82c0c03c0e100c1c00d1000c0c00c00f075224290b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 943596429 1250 943595179 943595207
    0x303121e010e0f010603111b150a0c030510120b040809090a060617060f0f15041401021e120702040e070603050a0b090603101508010603030f030f05190b01 68
    0x55054000b04104407a06101440780ea041c844203040c3d030340e83d0703d01981221541c0c801c42d04200000c20000e50b040b80c0a10014400c2100e0204a40e00142240703824058090280c4103140c481e0380f21181a03840c5030b418012141c02c0919403160560762840c081200840c100d4940340100303046c08101c0010305011080c000d5034103d107805410541945040d0341944020025400b911020030300848840003c800c81c202c14a04c110800707468264000b0945081103200103200164580c401140002d01286440c000041d10052100d42540b0000501000001e800c00305640c43c69106900e2130080403516440c0000e80400003062041d406a4840c00c078008200074050200300d80f80240708095000030312a506611803481aa10902e0401001d07965404005500600b0307a20b40d54594011241085844a50b80c0031a00d03008020f52401411545c582000307080d103502c1d51094001c43c00346103082c20720582600442d5409256407600304803601d0403100024191035820400c65419a440c41298200c0e4010642c0ca24600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 943597679 1250 943596429 943596481
    0x71d04030f12020d0b0a06031505060922050103170c030a050307030f020c0601050405100503030316030605030f030307090f0e1306061805090f01020705060a1a2106060f030312 77
    0x20041904001d0301088040b02d0007121101000031f01d4520920602100040410a0350742d0107141200308101c5030015101540c0c0401039a0811b500242c0124a2034600c68000030046040c0d80f42d0b083c08520200040040e055140c002c200310120292b0210840780000780605065440351a0038a00f00d008104509032a00d20600c0080d140181503400203955040340e000f02c0c0c003800179541c0e00540180003013192140c15010741c4144081100c1580351a440085180701d40b40005807181d5400c0041e14060340500c0d29001da820000c1805802c80d800318414001d17108510203980280d00d0715040d2804284000c0a0500d59200c05440104214058006034010620002c01d60340381c4403450710b00310043c2400c1e00e48020600ca8284125010a03040c001d0342c50842e0000044c10a0307946514800340030342006020f890020900350618006981c030016015898600300300048100300781074420324500040600020302c21640040301c6030040e50000f04075440d480d2710901948003506d512801da4064034844204801c0c0e6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 943598929 1250 943597679 943597687
    0xd08180c0d0303050604061e1202040b15040806060a0e011203020a0512091e0906060c0715030f0b090f07030c050412141213091e1d071d04030f1202 65
    0xb240c0e15411403402614221010080ca07a13403003105d406040e030420001450074030b1020042020340050704280c0079032400a0030204403110881d0010340740d201111028204e030351000c0b40c10320501c101044480c0c0e00c21010340f151210181004440c0300105c00501c1100d03404003140a50404240c820700040c8081c540c0001118070140c07001c0145100b581000540d9801400341e001500700380c0600d000403d0360380d04050080c0e1025201c20003031050540c41481071101c3c0348101e040015400e119075083e0341c500071080c2d0700011000e48840c1d00509440c020141540301c1c1542c8400d05c80b071403160000054000680b410700081c01c54903000c2c2aa0b85008551140700410250300d580030500290801c01c0c001c40c0c08003810f0700c1c020403205041040e140203105081c0f441042e400030a0150742455480032216250000c83c1900c60480032042005445151001c2003082a1005030409100010096074024150690702140701410a420001c1c40074001400038003040024100d1002490041800b52090a4090410340d40d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 943600179 1250 943598929 943598933
    0x31209023d21060b030f0711070806010608010e06130f0b040e060f09280201170a0f0507030207082a1c120e19051f0f0507020d08180c0d 60
    0x16030360040b4041128100460032100c80032403161500f510000c101403402d40d12800e40e80c03500540001e200c10144036155408a0964004002400040010718020030311b540c10068002c141d460306912480ca44000881804242d60340c00215108400c003148001580c0c105440b900300250400700391440d0403e00c2c0040200a6820110303d41d4841c0d4030003e181c1c3c1103a03c4102c155640d1b140002c000c46001d518090089495607008420300101d0703801490801040d15006160302032114080d039412060a6440300388070800102030084070750112060804504007140c3d6142d0f41c110348524642001072142c2440280760ba02e4204540c0941c0340002c1c03048a0a03040280c501105240a8207465808520070010407180c00101740182140024001d01500101c0c00710b01e036002c0c2200c184001117034240146982c0d04240c0b020707100c4c4420107110032038001c036245601c04504000c440003c0c08402c21500003008000308250000701c0369401c240c401d4021051405508000ca08020040b074069610842580c80c0c641 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 943601429 1250 943600179 943600187
    0x20f0a06021c09031709010306030b01080c0f0f03030d020919060203070c0e1303050307030e010509032113080c0708010c0c0515190f020c0a080403031209023d 70
    0x104000300c02c4086002d4508840540d80941203210042002c0c04d4401441d60008052025081111040c18003144890b129682c5007020395098200da80c190740049511002c074a440c864501c101c51081e220313202c0d09081000480c0c1c80e0311402c8a0740d456107030001081c407d191503115003800c03410f00d0855054032660310703000020745952060000380c854034854500851075141c4103032014011076603034004010303a10580e5010b42c0c60307400c001c0404003459a103415a220707111003801440e01ca0031000300a196103003041000c5540c103003080c1010310300011880c2c0030404d8102455450005e840e0300482070b5a2030782c1030258100d29188107504840712039400c0584c0000011380182c200900300c0e04c1113040d2005014401d1407d02c80d0001101d0031145424001100c0c55540003550101c01e0500003104007614018032401111b1401111100444540c0300015082080c0742c1d100d09049811412a80117020304041600000c006482003100b1600c0540c02e1040120703070100031551b0742900300b60320003010805000a08058 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 943602679 1250 943601429 943601443
    0x1c090b0a0e030303041101080a021801030b010c0c0e0613150306150f06120501060e01020604021c020312030106020f03070c140a031e030305010909082212060c2c0d020f0a0602 77
    0x1c7c0480e0440d0003151b4404403500965040500104800f02d02c01c40540046003e80403d441c0b0034140044a003008012407685660341003e090103000d081c106082440600448803010904031000d20710340500c01c0294070440356040b045075040304010a0074a071300381d121814440e259200076a50b80d1820b000091003a007200070108208011034040105aa0302c0c8410356020541880241c0180c102c8000940141b409010010710181c80c40111a5220041d03130100f450815680e5184c0c40055021004015003a41040a510074042690285041a41c59500c1c4091781e1180c0c09481c0507203010314080282078880001d000000c40d000018031501200701d689485600703000b40b1081c0c0000303083c20004680c6400134041c0d11009030b80a00d01508c0d0441120001083d140206a556174101c0030403000030340815540300c0c00700610b02500c400510701510034409046100060091249240161248004680312640c040d000da031095646903d070442e584000b6808680702984180c1c003c001c07080128941c1c1c0c0c001550 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 943603929 1250 943602679 943602713
    0x120106030501150c02061c0f0905062703031344030105010c0212010b0612091510061209051020040e070f050706050106030b031c090b0a0e03030304 65
    0x10704400211080440384010031032400f0b0f410500c104084d611002c1a087c0308010440400c000041c409458a000c070281c510001c0261802d5200d0014400c030394079203070400019080464002001d100e90501500c2d04c82c00010010066146254854024011a014010010300d6003071605c2140440c0c0d414441c1d00380301300040c030704030602594030881c02864038031048906880707050b11031194440340344e804c01c035013110060030315000d5540b111380c0c1d0102170b1100005413090b1160026041a14909a581e2138600b4a4400504002030201018006400e00805d002c1c026105585481160540482a000c1c090502c034900100710744907040344484007404035400f98a290a02c0040c21545040c001002e007000e003d6809555450300c011808503a80e2801030184400325403c50500d50300f8500280c4800c012a40248d0001d000300b901c40015200d6440c04dc807509841e0611104112400b02e070114000386100321a024040c8240400103a285d640b1340180141c2d08000801000c4030340d2890309240c44843c1402e21855 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 943605179 1250 943603929 943603949
    0x42f09160810051302090a03021e030d021c200f010e2506210905011b0315090c1701030c06091706070f1403090a02010206090a0218060402120106030501 67
    0x4604602a00040030741203540040540007000130300f05510009510a50400b980b200c4442d400000603241c10b4110b1480c55100559002160100e1082c542461407810f42002107400c10140c04800c001d40c01d016201c82d034224903100341c0401004052210041c103496440308a4807c18035050080f900540201c001281410250b072489105c1086101c0740b8010804034000d4808c0b9541d051040c4c51003694801d091400c1604860969690305140f071049030740c5c0f02010380d01c2c2d075150601401d45111908404a0300001e521701004640e00e0241928000036290003250ba0003512100315141d02c621800c824008144a10041515540c7da8684003a180790140702d40720104041c0c02c000103240c541c003891485003c5200001d46421366515108071103915104d4055070900c20000c0e80c03a0b29032030f02da001a5100d408558018282034026000192070403070001c0801c03400e9841029100010b0700c43c6140000d20001c900120074180c0c030740100282c06401001c032641c0480e45120000903110303503d034015504032441125 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 943606429 1250 943605179 943605181
    0xa0803270f07080f19170403051b090601081906080d090512070303090605090604090e03091504120201051b060718050d0803010b160c0602010b09010e042f091608 71
    0x1c0300c0d1100154a00000311750007041c40b0141d01c040550b14141d41500c44c5581041c0d24141080564241e08240c00c2542d15502101101280c0c0002d1481c0354001d0508440d40d454a10700100000d00400b0010001c0700e05816000c40c04000f4042c0d17400c800060480740050703440c94403c10300000c001f03030303242d00c500f51240942000d5820005030100b012030980e84c055441c0c034030203420f01d001958541d008035611030700712400704400903000078a0310030b105552100e84050356444021000300320341d880c040b0f4041040c04030104000c000440c98060040d0005034282001ca031100c440f122102d0012480c07101d0300c0c985024800c10011001e52104200d0480d420504100e40d40d15119000d014031900003000060a1100800c0180442801c800142010316698103442d1210084c5580e055201c8a01c6c3d480940942e460307403094001440c120540901401c02c4005020749441d194650010b810740601c410002c040c986243d4081610170b810100c0d01c0c0036005000d000c400d007081250342d4496840c094410b000101180 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 943607679 1250 943606429 943606439
    0x90e07030906050f04030516170f180405060a15020114090606030d03020f0d1a15031006020a32010c020d0e0111061906180510170a0803270f07 63
    0x4045140941d1b01551400c1c10f05c08004101c560b00c1300c0c1c0003001c0e40c0951044900d1100300e031400000300000a400300707850361958070b6034045628484005140901c200d0820b8208480c030b803100304140d403c035402d0507405030154039290800c4e80104014030302002282e4011040104100001440c42d000307500075421281d6800309420201d01b00e01840062440c10b82040040f07106014032a00184590101c42401c032810460110025088481220240d011044044100101c811a1100020042810740041c0902c401c255440d10003d42509400000d0541140f103c0181006040810b424440305080200448034000c48065980c00041c13018800003a2081d0700d806940d48200103241040a240300202865280d003040c101c500d0240c01e02110483c0c0e6200780008030f9813030315051681a52040d001c00902414440000c1a42d8010754000c0071200d00b0221102d80c0c0c15800103140908c0503000204203440b61100410404180c421603400c510680e043c29900441d02d0010600001e065121011210401d03620 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 943608929 1250 943607679 943607701
    0x602071106120f041e03030509060702070b270d0812010f081e01020c0d081515030a0908070210051206090606040902070c090c05030702010f0501051e01090e0703090605 74
    0x203007810b52200d900070201c0e40c1480301d82031042c0c002d4031030b40100d1190210050041c148003e0000c00740c001a442d041404040d036801c0c000c19402c8905403014140f2181091010480c5d40b00d00ba1000b800110a0481d541c00c00910724200404044000c005410241190400d980b05400101c00110a200c50301d00000c0c1104441e4001c000b02c41b8124060110001c40d4800310300315105842e4280c3d0305540030000701400b842d00703000c60040644a9112902c96080a083d094544001040c11601500c5c0e030500c1e90724502d2140302902d60114069070081001207881c5401b0704a8000c0c04002900b08908401c01d0b0701c1190040058440e003421800146590340d180f01c1040000132003615201e0b0440010007052111030f0241d0004c0c0b04050203102415012070380d8540b81c004a80300d05e106100050400310034440c0e40d40d420300910101e00394084c0180030745c0d41031000084101c2c203d14000610072002280010075070340620441e00040c2018401403001d46030283c0c0c054041d0024100851f016480c08001400c90311003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 943610179 1250 943608929 943608937
    0x5071d1c050f070602070b251502220503010209030703120e090a06170a03050910050c03041d0a1505010c02190e0601090e01300f050c040b03010903171f030602071106 73
    0x1181240c101e0401100d001d140303513049006400d0f141c1030150502a0b0306407005000500c80858240007e500c00300c101e0715a514071162f560007080c03099004001c01040d5660005000c000d0300d40013810780b80c1004415100f950303066400d124058000c45039000304105806180e000390125090f011007452080d0107030100e1a110401c013200180450820312840019041c4404840b02688450511070726103011301307040a00d1074101303a2101065401311000107500d0740040003e41d8220a660005108103200e42812100400650180320304110640c0c202e1000e5690b042041c054100c0042000d040c80c070b44620990300c1d0008100c2d14030380440e00c06000000c1c600480c42609048884200807030aa0054000c850202000002200f002800000e031402003c2014480e00d03000e05031061008103d00b124080c10700c401e54400038581c0d4400e915100c04980400d8002c949202100e581064014a5588001d040e20f40c541d190b15070000b0b8209552004010071055a00421103e4069441c1c190384100c2034080002900c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 943611429 1250 943610179 943610197
    0xc0507020a03120e0604150215011206050402150703020f070807060e090a06030803090703031d130504031b05071a03071202070206120708040605071d1c050f070602070b 74
    0x140d8141c10800301d09072040100c140843c1e0b1818180d025600300014400d0b400c190051050040010141c03800503030100600d1410503800011440250b1401e040106038001049024107047c1c4c407040010210f5440340c1540c80701c4100c00c4106030700c0c3d034580e080083d41c603100540008802c0c030030307204080303101c00c40000c0280032182150388a54200c6030f25002c2c820034400203490428002e840b0100400020a800301862107650700a000f0083c0d1491414000c1c0b540d08441c810340fa4040e86d180d42c01c94541c079440008560400000008a103e0301c9500d01180c804c40038401840d0039680d0700e4140010004041341302d80440b082000c544840c080c030f10560811503c0169250700104000000b99108003030a40c0243c508140003c5c4400d08043d956800910100400c0702e0311000600700340308100801400c0d2081a4000469191008221502030005031003a05000720700f500c41c44580104954002002c5405001d1682c400c0a98000254840010356920380794090320015015804001c52840001001c1d0f80c0148 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 943612679 1250 943611429 943611439
    0x9140c090c090f0a03060e030c280609210201020714010e0c01080a06180b12070f0b0903160905040c06030908070305071a04110a0e04081e040306110405040c050702 72
    0x3114200410051150b0b40310388a400211180c80007001c86c0e00c502c40e84010b981008041e44d5034044030040e440c00c10302e800120f07a104080d4071949021182c0c001c406446400d40c08080040c00c00b0003420901c0ca40c41c03018611011801a901201e840541e040d0080c1c0704181c456018120201d03421800d881c2030f90321200203140b290348510581c0c07440b90b200e4030086401a042c1d03000021965269610017001c00c000b02c45540665403519440d4080c1d040c510110440386101c0c00240c4902400c0694000b5100210701c180e6024140100b412143c50f41c4c180000d07104100e04440441d0b1096442c000c1c1d1018010894042da0f10a00d100000200300c0e000b402414809588102c0b40340c513022103139400b550f098015007401da0382852001c42c02ca80070720710109014010b501480d03000765070205a104000700c14440d600f2440100101d039052000081c60441600d400000007010248540d2285000c404580500d62002c1d080070b0a120004028000d00002441526800c0d58280308880f62041c040c0d5045c450706800035040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 943613929 1250 943612679 943612687
    0x20d0b121005071403040b1005060304121409041803231e04120c05031b03030d0c02010905030d020408010606030c0e04150f06050c0c0d030c0f03050d09140c090c 71
    0x1c40a1980141d074044040e080007144a0141c0f0140d400b1504100c0c0d04651400c40e11091020b140c40c0c030800e001c0108001c0f103095107076282503a10346011039400300c1410280082284080201c0201800b514800d5801802c20020712200c010b540c54000350004065002c918414156002807010800302c000d00c0706034450142c6811720850800c010180858122100340f1000c1c030010554080d503019240c51180100842003000d13041108040c108000200010124484450100200e803400b0095944100528400082c04840030100381c1c05016480c0c3c0c0100070f408001005081500d02d903001c0c0080c1d41e00ca000070003002d41c4600d02501100d0307082002c0710220304034004504061429801a106c41d088ca600e2450701250784034848603069800d6000031020410103d043c03034000b8010000c481c181c0c18100d4107c00d03860007648010340320080001d0041c002400c501026018503009004807195650608400c005840c240e041c4610300080d113400d5a540e034010400d100c4080d1905200d410b000d644280340d01460 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 943615179 1250 943613929 943613953
    0x201c0c0302040609061d0603010b0d0516090501080a0905061609210605150405070f0201243804050907080105130b041107082206021c0c0213020d0b12 66
    0x80714171b039215030107804665003803c1401626480d02440c02001e600e03110ad42ca4811042101c000d030b400041c0b15000e400b900000845625500c4000d48045940038200f00941e925428614000382c04a0b10015207070344103001c14820740c5160400c207413803444070756554400550385030040f01140b4191503071084264000d800c071003070203c1c10560109410180301000064500c1c0000085000e03114112012404180d400c1c00803002e0607028001d21840003641c20801c000c80d150401055100109402100382800841c0f200c0394040c071000f6804407112074250004030001c00c00000942c2e1030b60040c014540100c030404045920300d4040c2050303074180d8100801c0407220b2000c042403003008248200560f0703803090b11a001c10944291800050030500c0c000c1e05031554400c40c0b490b090003140207801203140c080003076a03c204011035000c590107a40301c0e248003550390000e0b080141140c0c0b10091400180d41708480410002802145070f00518401d841c080313061161806a50412080c1d041c0b8100c0c9040981103a080303190 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 943616429 1250 943615179 943615187
    0x1009150e010c0b070e0114040b03040f030203160b01090e1b01030e0a170d0c1b02091e0901050f01050d03170901020f0705010509150613201c0c030204060906 69
    0x110360185002800c044060b21075028464080e211400031601c04510240c080d40c0c401c4190440713190480da01344c40c151038515907041c18072008001605222031a0203000406200340100d030000303190b2114603507000610f0b043c0300f10740d420300303101d11040e01c0d240c83d5a070350400301c000c1015010404540f0417801c240e410f010055002d000c0460350000039028200c032030320008034410019907400c03080c244d0168488802020341c0c403c8480c8035030a80140402c007115401304035000303000701c9c4625034140d8142005031100030021007010324035410007801d00322a800700007640b181544850300c2a10140d490000b5640c1e41d01c01c2c007815030301c0300202130001140441c03c01002c0980c0b18102c1c0e0803001e00c000061030300d03800a402000b44d42150341e0403917007030351101c041c80349821007001340401078494804048a1400e290700080c0400d10314003c2e601203152500c0d102035082502c0101c0d05442c00c0b0003002e056462415621034180c2c290f18104c1e0103020391404883c0c03400e80b40b00e4829607080d5400ba44174581c0d024207151060b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 943617679 1250 943616429 943616447
    0x11010e0111011107060605030a02030303131a090a020102070f05060d0914030304150c0201020f1206040e0d0c02030601081507120905031b1515060c0118030e100915 72
    0x64103102803544540c01c107250902c10301400020070035003281c48440c6450000196a45a031041c3e10a5000ca003c55016036404011a900010b040d403071a01414500e01d0140816241c40d2100c0c0b582001c0d14080280914010421201c1503200f6800e680340c603500c60320610801d41040c000c0d142c021000307010388041d15006610403251a4040c005030145042d20050840c40d59100b10341c01c4609000c10b80404512074a2030040c1c1125818a000030750802160580c800051b005442c0749400010f000740209410780c07240c1e40310a948a68040a41d4001481080040c0c6491651401240288101000024401701c086094210918403035029251030b240c55000300e0b0a001c8020440040d13039518161900082d000304001d0000e109182c900e4500070f440303606414105048102a46e40c04e00c404410170000c107115440114034900f040740c840d038859024100107401072004069101106504076180014950403250644214104540764440102199801c0328160117034420742141c104551050101a8081ca24007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 943618929 1250 943617679 943617707
    0x100605031506090306070528120b12011416170c070c0f12030f0804111318050705120a1a040f06150806070318120e0d05060f131101 58
    0x83c20700c401c0380000303802d12400780c0303d00c00800c0c80091b0000040480c0c0c030046860220341c6010940c02007460b040a48200394107045144038560344c03c041c49045c1d03a190f02c03c003070103c108002040f800d034961030b0240588070151000340001c02c0d0114415041482071254940980300045003903900c1c1c80314103042130b040e00a0101114095117416000c5122200100018000c024104042c0100c400c41d080142040340c80d06100c0003000045010813006c5040e00c00e442804017010356840c082d48030f480610b00003c0030309801e11031801200d0b0380034500b40240040c1005c20b64008550003c0f80c0071400c2c103225071b02d80d15808002c1c00542c178411788a210185480d50340e98014000d581c4013000c807249a40c1c14048501c0c00800c03004054610805200c0d40c10b080124650001807818200802140c1c01d0000c808250200d0340140050040c0314900050340c46201070090300c4801500c0070380107441c1886c1c8903440314001c441300480b481410001450001d089d0300714049198004002150986240c1c004480540b40b030484 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 943620179 1250 943618929 943618939
    0x5090c041a070c060806090601110c0a0f05190623070f05030309061b0f031003020d030c060f110706020d090b2a120c1605030708030f1006050315 64
    0x400900c04401e060110442a00112482da032031100380b9040a8501c0280c1049040181c1d010800c000c58a840c40480c0e00074100342028440d0300c502001240c508588440e0544d00900c560000041d40845010004141c81d4200d5442000702e071302e0b00d401d51541c0518410000014604a901400c0103107101c282d0061400b1049454034114191700c40e24000310326001c084410703900010803c005a40c06100d480d41210800741c020000c000502140b180d81d005a09083d150745200102041c1c0301704000b142c0c074009650181c84005100030f1800d000d8040c2d070700f020701552900e0600e8581003410090b403041900034103440d841c06041901540350b000007074000c84c0e03400702070554500200700880c501d0320402c0e00c101c881d60204424402850250902003000350f481d640c003100d007444028008070440721100d0f8071607090620f030b81e200c0d50a21484c0d03440094a400140032030000164038411f0020140c020741c03207500680141c0446440d0314205860325400c07407052100046060001c20200f0056902004140d00c000740 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 943621429 1250 943620179 943620187
    0x30030509030105040f1b0e07030c02012003040302120f040e060103090b04081801020105040b01050f0d0c0b0a0906170118110408071518060c0f051504061b050405090c 73
    0x42421103c1c144c60035104505040d03020003c010148030300b0301d9400c0420300d614110501d041120810b000d0f025000c181455142c04504050a00c00d60015003044811f240c40e406a00000811002c02c1e03100380d40540041c0241c05040b03261405110445044420303d0b0403d0b0329052900d0207400080c01c0c09040c090403d601c4c2d2030b02c40045015090140c2c0598050a105565030801c00b04210210300042c25107410b690500d0100400f054540000c941140c43c161014a0440742602c0003419142070964010125220b080c40031503c40401005000c141c2c1c3c2c3d544861300215245c40b4242d80179250b0040d0600113503d600c00601003540760100005011002100c042549212856014016003044e00054500c1d072060703008000120b004044910701082e10b082540d00030780a04000c03106515030380034810520410581d12003c00000c50488004190000180d80c0780402001e600d42d0854010f60703003a19500d041680500840350481910300b01400e4a41b209131030702c0e1811091101c3d00400a202c40e140030001c1c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 943622679 1250 943621429 943621447
    0x1c11010903030606020c01030b0f06030a20130b070503190207080106091401060512010b03060f0d030f111609090c030203030a020a06110403031b0606090c090e01300305 74
    0x4003800540318840d480208000b4140540249000c00380c0320301a040608060000310151500391704408503140584a00e44d481d5506842c0f400034042c0103060440840341c14049891401e0301c7c42c0500b040704020401203c8503a0755aa801d0341c180070744c00f40a0500c2c2c1040258100124000004420090003801611244e44c0d46400c40c03070071141d4a5000d0188680c46001511640702c5c0c002c0114050b0201d414081d05141d407504000d201910140508282214004045005940c0c0c0016070444590014800081d0000500d0001e0044d070084941c540442c000454120660b000400d2041c8003100c10744184620070f00d0120640d0245c030b80c0720170a80d91020140c45c080056201440240403085180d001017801d00140d282a00440b0420007032004000403d01040c070010343d100310301c0c1201e428442c1201094046608048009054030340c01400c0c01c5180890f03507515250000c20601c102c510503840318016a03030760850940709210108110071040801c042c1c2d12038407030b06803004035000303406450038030308189482c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 943623929 1250 943622679 943622681
    0xc070c15050a02060105030a030509010f121d06340c020d0302062208091e12010b040c0c0b13050703061e0e0d0e060306030109060612030e121c1101 65
    0x35810080007910000364104140c1e0100320890040c5019001800701030095200100140502c500c00707810040010300700742c40540b042030303802510a0322507020081d003091008107140c8500303400c00d042d01c0750141800043c100b030107481056030342d10706031454003007081c02120540711b80303100482200060040d4041003002513250414040c4003c1d01c00e07001841c0361700f09110b24603003101c1d0884807041c8104080b0580070001e14003100b0f42c5d2007810103079039504900d00c400c440a81070315240d4186a4010b1203e40d45039154141c1508912000041030b41c04000e00030406100b10707410240c028020b03003103810000c003207285980c0303c0c608003048600940c04e0f10015516035880c40c003654100c04110100000140103505813580030320800c4c012820210041c038103100d4802024044040e4900c10600c10755020001521a440a40058135659440304041008030307264161044030100c4a4820b0b00040d0025017030665508101c08096601d0100100816a032081e040104d0b80c0c48051b409030408020183c40410794a00003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 943625179 1250 943623929 943623959
    0x3160b010801050115050d050c09030a0f0627080a0509090a1b1706190803130e09010902213309010c0c0609080c0316061a090c070c 58
    0x49014808000d526001c220307820f40748183c100290181500d51050803040e08281211203404440c1d801041c640e45200d0a0016801100e90a40c0c05000d41ca51180c100050503039000f245a00c2000108800074110031100c0101c0903040d000751014081c01415070100361201d01415141d90342d80f5000d440c1004180114015090980b00d88a8040e160b17400002007a50440311103945024902d4040b00c500d0035064004892013001c0d213401d00800403a10450241040080b2003409408240c0071a6030341d21400c0500d24501200340b007507880c4a2030700c40100d0030040e0103000d400e819036001456280c080d2428449885868141290400c89228015600030540c00503400c044050355030380380c0741180c81055110041184e500030030783d02190345840c1400340c09640081107000030680240d0001040380c801c0ca07140150b4816560740200b00e100c08200d0b02446d1000d048084210743c800c040c20302c0601018050907001011111040e64800743d1000050081400700e4003426a1600804014113125a140403007101c20700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 943626429 1250 943625179 943625183
    0x7050f0f0409020c100e031c0506150406090609091401030b180604060906140624120a0b030f01051006050702220b1c020307121703131a06090a0c020316 67
    0xc1400e0148100c1580300c0d086c4440002d8000d58600740a00e903400e200412000e0700306100a6644000c141d55031105c800344102c01840f01181c81d0f603503803100300c058400c4c1090300c66500001e88412003c640040e032402040e20a0169402c0d454059003103070b8506014100042c016400380c0300110a8100380310b420803050b8095801000c00150495481c14079070199080f9000c00308010070780c5418001c1c15160081d0650084c00446484500380101d6000104188191040d800c079070b20312007040c0b208000499106c581020021000c8481c142d5846907150300342d41c000c03210215100c40c481d0003013040d18080d4000f03281c82407005000108090560481e803120450000c40824990303a13400c0400d40c0c505041003640c1d610100c4095034119039030140d002a80c0c0b1012401085129403201c83c0b54001c001052540b1001060340c503004544a1900141c03d4001c2402e4031015552032420b048aa08107183e01c18034140140c401030310600746541c1c0d81c8002400707010006440411444200700e500e604c404000a0045454 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 943627679 1250 943626429 943626433
    0x81e120103060b090906010b0d020702030106090b0910030812060402090907120513050604060e010902090f100f21020f040606030506030f0106232205071707050f0f0409020c 76
    0x5415810301400303c50f140e015072802180c0ca0400d00c1400c000018405044401c0703c12141ea0f140c550307031615070185c0260a0025010340c280000843c1c8071400e1f402c0744810000a83d403d425564602010032660320440c40701400c0323408200300b403041952080302125441031020740094a000c820300042140484102c035480006545800000c039104924040c02e50410400d2901c0044a070598981c1d503110000640000d000765640c1c10404664002074010341c549980080c94460f040c6030550090000360012180f400d40d04101c81170104000c130380862a03905a40d04c441114001c125114030994a8110546041c2d900c02826a000a41d90f5135070b02564015000580d0040b4240c1014000e25203084010300d5110f411b40d0400380140306040381e04000150044114125950340710701d4001103030f0f042c00d0750800c14032040c2e0000c141d640c4441464120902901056860f181d0030f51101310b604002d83e6064800d800007440070400841c0d40f0310204040d00c9417003140040d80d4030b01943c0e198010100d0303001c010540e45135 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 943628929 1250 943627679 943627681
    0x9031e050912010c030c02010c052a15070e091b090d0b01080304140409121211040e16021c11010204170106050109080303010311120a0b181e0a081e12 66
    0x915410b006d40441c0d020030f0300091060303528120000e803490080c8000b12000c41c4c0e915807070400b2a103c2200074503410b9030110640e1410040801000070590b400c032039944c04200d402c0314050107400e040394182e100d582c0b20500c40c1070408141034a020030743d0102c03400a52140100000201007580c1d11b018900a054080041d41d80342d00c0c000d600003084000c10b1030644a01c0c60880490702003003030005690210222403900b01d44582100700036100a055003201184044008100460402924081640208104907101c001e0300d0500108030394032280ca0341c492241c6030394413106480982c061000710070310440b04400541080c0d11454840446540c0740c4500640f41c3d102d403070810031542c0040101000c1c04510000c1e501d50360450701c0b07040d9400d9010380c1c91800b50240c00d000c14003616041c07000d000300c594840c08203c0642071040b144081503240c030641d48514000c1402806c0d14905942c01c0e02840c5881c40b02918210100b0340364008290008001540c6031011600c6c00410021002c00402c00380701170185080f41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 943630179 1250 943628929 943628951
    0xd020a0806070f020109050709020c1204030602030105150903122a060103031e082716090b10022805030703020601081e190615170d0309031e05091201 66
    0x1d4030303074140b40f1401d5900d030040480c00f01c0c0c0042626000e4401e040d50150b9580c1c1441e5400d032504954006040c0403020108010041044580065040b640110781d013446040310610184d00ca4130a5090107940341c2d001c141768020309505140688540b0b031040c200060f8000400c104c0e002d02107105c2c0c003281c0d05604800300600406411203214900c0c155021481c560203c2815009007000d03001522103048849640b04041c0e4686503100b46902500454047c0d4203035881d58188030b0383e180400c0c000d0070302450820300c030f4100740e0424520b081ca03c011594010200310008012281006144d0440488401a25200880823070b808000a00120b4480c1e40109055072402d401d03d030810404102501c0c0b003040d81c0b811244100c03400180c04070b01641c00d140e0810400001d1910000401480d2603184401a20880c00190002c0b0441c452004503800825503503052902c50045007204c200d00001804240051350456668100c2d022600807051942480d5150040010001c0d00f03080300030b0001e84c12691a01c1078821 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 943631429 1250 943630179 943630187
    0x2010c08041208210610111612060c03020901090b0304060603020301021b0d0c12030c09050301180c080601061e0c0b0c180d080406120207060908040f0f0e0a0b0d020a080607 76
    0x40251320395418140c0ba060807400207415903107070303040101044034608007200d5004052180060491407480c103030801c0fa82d1440580c511110b40e0340c00752a981e20b0300074040300e1240240222400d142d4140d5a285115040c58441d800c0c039040900b0075203059135142c03000300042c6c41c2403008100d00110b0540c42d090f95100801514540882d44020b1002c002d4003440c060001461a065020320703250905000c15a0251900c00f01e420800340d601056041d03007481e450080f420628000c40c802e503030245c40d41c81c2c3c01a4451802036030f912000e118507030000700088420711841248000d03035a0020740300d107440f4584485039140c1b034113800003c5d41c5400d000c20000850284c1080d0045821035216410350380f1420b140d00365100c14030140501c1c461181803100d1440c02d50740042a59045503085540644104518949810031100940140c0203009107420010008a2105a980c072510201c8550030000c59046e070b00c4440b00f90140c007400c8030080e0404c0500031068016030301d40700907074080d00003140144540d180000f0300030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 943632679 1250 943631429 943631467
    0x92409051b150405130504060e12040503010f060807062a1a0105010c03080403030509010b130603030807110a03120b060d0c0f0c020102030d05331003140402010c08041208 75
    0x41c0c498004010130000303604d40060b90601c04000685c00901c40d56242400e00c00f909030b1500151185c022013100c5d6404c01e1040c03000e8800e03980150000c0002030850b1b9803540458500f4040e01070300c0d9014030300070031105226211158003410360384400021807160540700c204055100d00c00f04c3c0c41110203803186450b65041d80c94603004110910300b041c0d400e1212740f0068010f80b0007030005020103444900090490350250400420b0071700140284a503440c9510b080b000030080d900044001803d150013140e50284181c1451410004c0314010b07043d54100f903a0f00307480e1402007400d180300171905e4840c40103143e1f849802400c8018003014010821041c869802007400b5140d560200c14401e100c0112070240c1da0000a4030505a15800d001485841c1c1d55071507480c0d0b640056542500003850409a5402d80805610a0b40d04c0700c26146840c85014180d4181d0694454428410600c0b190710005405588543c0014240f0b40c0500e1080d032030035468820080e900440240309aa201600250091440200c14a80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 943633929 1250 943632679 943632709
    0x60c03030c05070b07080627190b0a170111040611010509010c0918020705030f0703090f03021008100306020c0a02030714060a08073e01092409051b 65
    0x100f85000100c0e0748440a0842c00380c021010000380c2c40008403203440d007440c0c000c6950801ca01410209500580460344030b03d0444108a41340d40003204281c10340054010b41007880d41c02040d0304122030411a222802100d000700700c1500c0d40d01c80ea00400c00c101324500034400380c00e00769286052007607040389075400d41c0c8000c0c21000d102d0323250514101c40b00d80d00c0990b0809591180500800c00101404a030001c1e008548001c1d1803804006a145103070b4040f5401048a01e01c00d0701c405000317541d542444540003520f032101a400c44081e50f0900c0466115a4002da4002d442c00d8030511101e48a031a00c00403a0060b4080b1303100e940c403901c407000075454200401c9000780340408003038260b400200f010803a82d014004484050241031404100d64901a0100d641102011400380c10801d0120040e0840781d4801d8075150700700402822081c1144e001800742a04998226950845a500301038204c064000e1103031004013115039481c0e29000190313082c0080340d4002c5140103044600d40c2c8580c100503080e15042c0003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 943635179 1250 943633929 943633937
    0x90f010e01060c060905060109021b060105091305011e0c11241b12010501080a0516260903030f06011b02060a0309150e0c0d020a0308090307030c060c03030c 69
    0x400a00d1419091207040d20b21510701000d402d400c900d0140003800c2404002030050082400220358508654003404020782502d005244483c0300a640e6611860203000d0700390401d0405c00010103101c0d0380c404004049114100003d54500c11103110403c8004101c03560482980758100b030301c08250300092a985800b885805414503080200324180103610348404038800030200f000044c202010030820003140c801d03081ba400d42d10411240d1841e01420240580f82c0490400703404110f40340598400e40e80700b417040301c00f05800d45408603010b03106244034641403038001d01300b100341520003c4102c0c040c43c004d1510500568503406e018506001e5150000d100030704001003400c92540146810401000c00398040c0c0705683c0e2503508007070031000340c00800360245c10030b03800300500e4492200d6540041d220b0a01c1005503180300421008000d034414100c400603521101c881003c2c03010440a10051012200c010210303100c4a0b52036640f110080010341c0b04002040803050120149500f500403400700340300b0351030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 943636429 1250 943635179 943635181
    0x923070b070209270114010e011202090a061a030615030405060712060b190810051e030c0423100b0f0702040e2a0402040b040302100302040e0f0105090f 67
    0x30205980d402440c20103445400d4680100b003a20782142c84115009581d50300c81e035440c0c07064003011406018545095500300141070000a5070101403c50035050329144250102d001640d40c082007134170140680104120b0b07640d0301002500800f00743c401e948410020f0b180079102d142980030020740da218a888541c139034400b04108400100d010034201d601071007900300f8255454031060003800030b210300c0d000022119400503060b545005901640340d00403810b0b9440520070b42d01e030258603040c086a882085d070070003d03001c0302c05007000600c58807502e174082c090211009940b0310800070341602d405441d50b01d007072011114a00b006038240a002540124010044a020f614251b860a030512800c241f41c81566004252401159100d801408040440c08112290000c5110741600c044280b15140002036924200328901d504107030094804840c1400042d9040c00e2658091140500b44960610b0805d5820403012803075601804402c0d0207420540f80c1803100790304140520407a044054042d018880a500c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 943637679 1250 943636429 943636439
    0x4060306090e0c011b1e06090506070c050c0d020f1905090a0207020a061b14060a0e010905032b050108150603060f042306090c030c0a120204090f06092307 68
    0x1110f400c034042c980f590500840fa96078240803a02c0520025006d00303900d8110194810f00086412251a460150303040d10215150741c40b080c1c8010190800007040c40c2c10800d600d50341e500d80350011200683c0083c214030301007100200028270b52103210206078190600c801040c000341c1000d0f1010796100c4410482140340c56540d4000491140040c0b05000411005030040743e50141c0210b0100326a6034444048242d14228040190f00c8a0781190840501d500c0d000074840e820358140501c1d503036590020b000d989072040011101d06a440e210100c0705001018241d07035101031a00380b003a5402418414060121440c0004c800510444082d085510980c089810300030010b000c0d1002d00c0d00310f03038071a1001201000340320091079401038417202c0c05d03214000c07441040440000420b0303440624000300c083d02c0d07201186000300a05840207008031900d00a413000c080005041603840070b0304d034600901400c04603091543e40c4005035100c07503034101d517601004c0b4502c0080400c0c100d8914130740701407003014180c07040c10700b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 943638929 1250 943637679 943637687
    0x708100906050c030c190c061b020f0304180b030c03030a0302070204050601030b031b01031112041e210e060f0a030f021813020d06030803010f06090f1202120304060306090e0c01 78
    0x1c41e44030189a1b0141c100340c01042c0610411255140d0000e41401a40d98610a00312401c442c010745c040540101d07449800745660110486058400018119004030040300010300242554401507426108145030030450b0b1343c0420107088903800c1540c01582e210190303c14441070300c0000d442c1c1c506050420000700404da9011402d01c6198004918401c0c00000041c0124050282d2800d4950715400c0000d507600f03007030f410140052145006008003082a05844081e00b0382d100c8072440030f80213100136416219010380e83c07080f100f241c2302d0601d4100541c80071080011600e500c007102c40f80d03000c00300142030701d401d540500070803800c42003e1504504100c80c0d102c149400b004685003481c485c450b56440d51034101c60540c1a12a94058103504001da181c507032400718071582c402e018159032800001c00001b07046100300b20940030780e405240c00242413407a107813a200008140c07890480e40302540341e00c0d0000d0014101301810003010759960115010b03141ca400041212036504201945070007a04c902ca00c20303608 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 943640179 1250 943638929 943638937
    0x14250c0c030305030717090d111603030c11040c030e060603070311040213030609081b0f0c0d030215190c0c051e0304030602160201030c030e06180708100906050c030c 73
    0x75003401c65682d901d05c203040f1400403035001103207841e07054501800750401c40003601d1441c1d40c41d50745882403100c0d51402126a91980d01d0150312040800c03190500000307114907418803d40784218900145080031000040584041e81e02440010b45c1d070740d020040240b001c000f0641c0102050b800740540340e0460300c0d9900d40320b4010700701034019600003944490607100c030320440d00103540008080100d4219882d01409940c402c10841c40550000321000352410400304001c2c0c0d02c5e403010030080c803941f03122070148801c248641c40c0c00d030b0541c01440b6052103812001c03032101c3e10580c07480010b550a081c00790005c0044031000ca0401c01000a681e1003c8009040080d44884106e8880000520340401550032441c6200e144c00c01440c2c41c0c00400c0b10f8501c9401e550500b1481d51007620188a078104c7e00303a040302107030300024514a02c2d62060020817000341503d40003c40101c4040705540303500e6180d2400f18030f1b001c2d80130b83d0644900e59403041003040c000c10744103107904007030441c046c9440c508080101a280b405 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 943641429 1250 943640179 943640183
    0xf09160509120f03030402044b020d0902090915060405131520070b0604050a15060c0203060c090105030a15260705030705060a030f14250c0c03 63
    0x100000d0000750700e5496003503040341460380704201d4904030a980c40f0251a03800c280c804a00032410070040c174034141e0b030054112400e0308030f0120100c09001c2a01400480d40010070603014030040c901c0c01c044203400240010003e150030003001068444c120700c14000184002081849031f0341001c03440103400c8440c2d40c0205e421039022980032510380c83d40581c0248001100c203000700386104040307040302440c00319041001c0c80410050303000118001100031114500c95001c00500003105400080e5003441c007030b4445a0000b4036141d0000b04048542d011042c49900d54001d400440d081d218900110700e030410803d5800741a488541d420015244000782c01c0b40406000e4800340e83d00d589000d04842e10703c000c1ca2000709800004854140007140712110600310031024080c0c0c134000c40c003000c15282030001d04071f411103401410300c0349407004002c0120001c010b00907034411025211260f00e90141401031620340607a44600c0c0040c80d14001802589400100c4202c502c140000104540c0200303244d6001031048079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 943642679 1250 943641429 943641437
    0xb011205270f01141504020f030f1b161506030b130302010e0106180b0108100611011506080708090d140304050c031f0e0313090e150c03060f0916 64
    0x150800700d400b030400d20360700050b91041d0b00c1c00c0714022403010150809030140d4401090504003003000b900b0b0105a03c01c0240380031443c041000071a07241d0500310f0020740e00c1164680c0a4100c5c40315102d201c001c640c001d00d01c80700000310a218030b006100400c0c0990418840c1d2020400041e80346540c1e001582c1700060880c2d524046810040080c103000b90002c00b074981307114000b001001c0d15094450f080107500c82544038180e15042503800a94040e40ba038600130440044102180c3c1c0c40d042c41260751001005004542c2c4d52240000d1111524804142d40900030507142c1e0746941c905a4001080d681000700b6040701a03106110750a0203d030400d0585032981c03d280c0080da81c0c0c0c0d440c0d0070b10314035041108010a03014814070944a0080311380c18600c00d0030050b0000c0500ca40e6082c407030781079a00d0140300018001341480c00e100300410986680848900c038050410350f029400a4808807114440440b4840c51b2008000b04000780b5241c0380c40c4000314100102c8901d1342a040107002d0609100034007081310140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 943643929 1250 943642679 943642741
    0x6090923040317070c1e030206060f012007091b0c020904061b0c1709220e160801140108032a0703140c0102120a030506040b06030a0b011205 62
    0x454400c0690303c3c0042030190565403a400c0c4800b000b46845d907021801d8813a0710701d85c80d000050350000340368030582c250168004d001070340b0750302d0810012120200c042814420340720704d4841d01c0c02141700c03d40c0c0b8040c141805050707100d280c0790100058802c0441c81c000c103030440810b0f8000f02500400b204040580685042d687c581d250301d8800d001b040d844001e03600559003180390203e1941e204a01d00105d40c4540d42c44462045194081c0110740210704d1140e501060540c6110480d0482c004c0c000e010f1484580023140c26086103810f5801c2200d4041d42c01e41d4400010820f01c01e640013400f4034400d039400d11802040541c507115046407240951403030902442803101c0c803009200c40007004200c42080040580e044150b0300d1414400200455840c83c0300d0340a280c115070545c1d800400c605500c065500e000da403074080c14810480013050014130465006688440043d200c0d1604809184030b0b4815910014070120902d0000d00700790842c0b64844021070410040201d504030f1260380c041022802840f1400b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 943645179 1250 943643929 943643933
    0x4060f210201050f2d18010509011b051c0c0303061d07050c0c120d1b03020d05031806070518040603110d02041803080708090a0804260a0602040609092304 68
    0x19a107035907282517034000b42c0e1701c1500c0e41184013500078181e42c00150035860908000c0801512a40116800c9502140344040e101c1108076414540c443d000f84240140c132903c2d00c8210b031000708103044800a10020384021510000c160301803241c0006014100303101a03038400c2009200f0000e500040410007004400315034042c40440c10801c101c100c11000301143d0156200c107002a5585001c0c0c0a1000000c0074190060225805403c89812894250307024000c03c010b0300c1810b94659002803c1000b510407114421a568203044c84114015070f40740d03450541e00d01c840c8103100f0389034000307100360b038803640c6401000c00016401c0c40c80004a80f4044c0d41f8003912240500015005195034440d041304001101d004004040c1e2001d98a072080d409601e601c441c640f524041e40ba51030804101c000d103510703010401484003001c182e46400c082840c003400b14185500d982d1055040645020044509a4010030180040d0344c2046481e00038204400307040008580001c0d4200341e8240311036a0091044c5030b1340101d02 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 943646429 1250 943645179 943645207
    0x3080f07050a061b120b0a14280609090c0206010614070b0f040c0b07121812050f010e0d051909050a080f01060b18040b060904060f210201050f 63
    0x11860f410907802c001a000b1501620060720058880c140041d8012030501e0b0700711003500c180c802d043c2c005001c1c3e201d05404c02e08403016403a50002c5199004820f0012100d40d0f03940c0c440e41c11740e015046184003c0c81c40c82c11401030880a1389803c08048107040c207800900c9a0750008040e41110514a0141c011159018220209105d060000707021481e400c0104460540c90100d42c41c056803151200178980c50741c030074640d1900d01030848000c004802007601c1102c40381c4504041c4040c1d0107040110809199100c62440d64a128075070704480c0303a00700c003401800c40032080c482d9400310106a0081d01c41e03c08005402400e034420300f032122003148004481900305910450082002d040041c1843c120240c0b2110016030f0782111040c00c40e091f41c00c280c40400c103003101c00d081d503003070b084000c80e054503c03110901040090245600d82a4010702c05011120a070b0f5582d0050700004d2031070b803806001c030724201080010303242c040c94040008600003042000c0141d920030304540c4801002d40156456040c0e0100d141 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 943647679 1250 943646429 943646443
    0x2090a061806050f03150f0c0d0501080f0c011809020c01020904090c080105071b02060307020a02031207030e0f030307150b03100f0f0e3c06060a0605030103080f0705 73
    0x18001c0201144a295a8149644880c064440854041c5600f0034004101551001c1d60b100c40c00d8050103850114045204403003141d0b41000003010083d041960f4520001c0881e0b80c00da000c0d41c5207074842d21000114080500c60004400028a48520001c929084100c840d003100d1207030150b410b900040ea820010000e506680003400014414084082103040c01403206042c1c0c000ea11255103848049050180940c00c6030440501000f28241105543e40820509800040c0004254061000d02e4401a902031045401140400404907141c94060500800c4021400449070183d14454285920340d0350010544002a40c000711a1402410441c1201d024150003070480741c25204d20040c4110025160300810200302c0c1c85041049501440c55090040d41c0350042c4d61801c80e00544183c6100e440e941168400312081220200e00300342000c8000179801900c0c9104200682204041c84018640343c14041d0050901c1d140203030075541140c43d000c01d07512070250380c8211722200080d04010407d080c0441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 943648929 1250 943647679 943647689
    0x140c0d021204111008060d0f080c072607030f0605040512071203110a09061d0a090203070e0d08160f0f03080a0506030102160602090414010b0406020c0a1202090a06 72
    0x210700d40d0400d0f150410780b01000c4001144034003008a8084e00091041c000f442c032850340104a42d04c41c03030740b545038443d403140d034290b058941040800000c0305040b42007090070000d0084140d1040c0395a04511101440d1302212221000364000c114100046a070401000c00e10710b0b0080740018203611585803c9103854001500c032007169a01044c4501841010300e500c85003044d064505000102e01c2844a031224071415004101144d1500014803050b072180c81d41e03561340e881800051010303500d490001358241200b03501c80001e50b1380001c1008101540018a64031312142aa40d52502c2c198079958100703e8012440c800300c0c00340d5035070451000e108240400c5400300c1e420440d91103c900c1c160400a1a241d41100c10940550034813001c10b4440c1814803c40340340c50544042d9a69400c00c039035914029501c16000182e225440f914000c1d68211594401030090488103d07603aa180e160a6000e428030441c442028494045403608000d0320fa449040b020740706604035440c4038070f42d031100416401841c1c0303900300b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 943650179 1250 943648929 943648957
    0x106080a0506090601092310080307081810051b031902030309120c0d140f0a08040c050d0206030106050901110105011d090102210a02040b070c050f04140c0d02 70
    0x3003a05005010038010300440c0d018007501c81583e00c4180c1a803d5400c0100c0c03d25205a260b40020040a5540c44a40e0403003030b1030030181000742c3e03600a058035541200f001134402c080c00181040d01c00d8041b81d01101d0b400d030305403000d003013801601ca005016801058902c40031202c4555001110500038000c80e80d500064034110644501404070003981d94100711010603032841020b61880c40035021b0b009640700401400020181a200d00300100d882d04485440145030035404d020b52511181010f0151240c404142d1310100e040ca8241001034001c0da21350f111034041c03c054451880542c64401c00c40e41941c989003012513540c8210001202c28016404244e44e55500c0c4c43c00114088120394054000050a0000d1658544518000e02d00b02c0c0b00f10842c10020121f8940e1080c3e1050308520342c6a40060f034840018100381d6501c00b0250258440c240446090801c03038414400d9180c106021041204155410060059005a400d4011001030710100c81c030103010440003040e2642d50111050aaa4401c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 943651429 1250 943650179 943650193
    0xd0b060d0203010504180203030901030c260702060f01140418140105101e03020d02010207030b0109020d0c03020901020714040e030c010c03180b0f06120d0f0f090305030318010608 79
    0x1911030000e40080c0900c44c071440c10a0304044414000ca4224054181c0042c00b070740c645903242c0015001040310304120000e200c4802c142108030a8190106000d0f0012001d50501c1c5250451000b420034400500e0306073b50708000c0c0018031240d117404200301d01211041e5030000380940c102c282281900400d41c00200f4403801807001c0c0d0107078503041d000240180035104c40012031544420182200c0018a19002d04c0050840c100b04094540700310cc0d090380c03074018015501c64070303100e484050884d0406d0704030700d10305074001600038000e490600c18541100402d00d02107040a00c4080000d44803841880364030081001c002c5200d1329991164828503c2020b0341040301d603244004842140600000c460341e0780071a1a115411a0303001d000780b151070700d1580c840140c4125a0300c03800c0b1510303458805042d00390480022200d2507880041004420f0f81f504140e144d44516040102d401044018040780030384c10420880d07010000124000194ac1d04000d21801c0300318900c81e8003d00b98010031039680410568401d1107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 943652679 1250 943651429 943651447
    0x120e030d09060206010504090f2003030706020403020102070b030112172b0506010513060c110d03031a0316090515040c0c0c0e01060503041e020a06022506020309060d0b06 75
    0x6644500710b51803502034800c280c0e81c80b000c1004440d048800135000e80c000d200b0300800038001440441210f00b04045110400c06800c0110389503400c00c050455509a0008051080d0b40c1c0400c2154018424003805911315810541e1240b031402514200821006c4020448d101d502c1c001e030140c50401a28034130101c0c25580b6098401546224098910341840c5085c2c0820350a51082d011541812106106a49480d14050088410040c16070099605c0c5c1d002c218a0b0a080d80c07a0190031460500958000c104401040000101070741000203880c869405800608806041083c0902c2101c110410029051761102c01d01604818191455988503107000035041d40140c01180c00148030b40038038040c100141d1190074488000741c082c010440445c1c000e00014000a40300300104002044a000e00721040009a01044082040e5000040560000206d01c5540700e281c840000c0c1154010b201414060b1400740080d489225405d50342d405108000390889990001d5042400d90180150030240e40350425 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 943653929 1250 943652679 943652687
    0x703121106370603151514210705060301030b060906100f0e1809071502011107020f01110607020f15040f1211060c0a030c050702090f060406030506130204050603070f03120e030d 78
    0x5546c807604a6150a43c0201340000c44a120011200015142d101e041615201d10f2050321100d0316007003850b2103003a40c00f0816403034481c0a180290311484940780d80303013801010403080c14402407600d07010700c0e8944840501c4c00da0041c1d2004104195040c82e20320041c1d208042980c1c81f503c00309843c2504000c601780421030000151b88000ca0f0030350200006d0364171120707008909a4141c8018591041b00600185026241064000d261101c050400e01c500224500c038441c10034200b00c80801c0982c0006070300710003501062000651030208000c01c900e01d0701c0d2558550780076207079050700504608013541402c800d0b140103c40702c04041c3c415408031101841c003076440300c0045d840580c1802c006402c2091455409000d281030b101c0603a4004c0240d0559991113440c0c0f401684020080c5610980b90030700003001c00d10901407280203420400c40400b8030401d40c010f02c802e588025000034003951100304104600c56800c0e0340791040c4d0340e1080c17860000351650f9200b201c404490100e03290f4180180394150b0603490304 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 943655179 1250 943653929 943653941
    0x1e050d090c050922030e06040315060603060b1303121106160221090d050c12150f06010f08091c05030603102705070312110637060315 59
    0x860780702000e0707541c01d21130714022811401d8900c2d00401c02c004100001c0e0003203004802014000d054039040950303e460f0b5143c141da246010340c4800d0360f1040b0500c40c0540c0342c06548080c20a4450091909010f11a100e910b48968400680326803100e100181440b8820482046181742d500e089803054188041c0050380300040340610070151184801829503580c0f259003002010103184091410700c1046001d11054410a80003152603000e00004191103a80d00340c406540132a50f00002c00344680c0c440504c2800c1800a0448a0200035510422050f6a881400203400b0001403800410546410209a01c0c1100700c0704103e800b401408003a114060740200070f10700ca0784085040b69030881e61004070b03c2c01c44402811000036114040e003126540340e20b803218039800c1c5100303004440166907a138803041c0901000c2d042c0ca00004483c41d4103c5512241040030313076042400f00c054041540e80019006019040c3d103e071031141c180103070310221039641040e44048001c503002501811050752a8845c04005d003c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 943656429 1250 943655179 943655189
    0x2091216080610060809120c070e1305031e0906041205061323030d15051f08061309060515241204050f01180b0702030a1e050d090c 58
    0x84155000141c000300000c0c02405210036001c110341042c207007075080f1001c801c02806081e083c0320351aa40381c14800844020603824811001404982d41001d03800b0a06800190000e500c1c500001990b1002c2400401229000764442c502c2240b101d00c501138681f0f1a0242aa00701e82c4242d0224000410100e80200c00b61440e2050044c3c4140d03581d401ca00070000e1240c6030010704440000c410107401c54900440300300440c40c5880c112410120301c48050800d403902c0d115075600b200010201040710b8140b64003000c1d0101d5a145c81d0684000f030786800105003c2000700240c1c40f034881108007c1c05c00102e0350192801a0f0400002d010600d804100c607250134054201140c02041c5006004602040000000b0721203d000d00d01c81d40381c83ca520300b4407050700801034001d58507405140014602c5450900ca42d443e05058000c0d03400110a01e4102501442c070010283c00a41d0000c014101c030655220710003070800424404443d0000f098008100e510b40124100301c0d21552500c1d1082051244068080c01114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 943657679 1250 943656429 943656463
    0x3010611100905011a1e130e0105040501230403020303071b050109030f090f0b03040f05030c1603020103050114030c1005090a1706070e060d0b0123071406010b0d050a020912 76
    0x3c8140345c2480000c3c07038140c40c02c15442c84102910000da18049081c519104c03030076000032030b40d205000e07201c9084480c190740489942e03540399550300c0c0842e4000c09101c6800d00094510010303140545001e03407030744030082c140341c1041480055202481010810b20b6038071078010008005c070060318640940130100d0807032004003107040940001041c9040c20203460555204400320340c250746599840c0748164400540495542c0401d00034a02e252800b04680740300c080b52200c038115614a10f000250440b801a0003010711072600030641140782c0c800180b1403401e01025605c24508440f842c00868180c000c60940e50741c0018502e0001568000e28000b9a0950010b00c05461084d200c2c40000d9030804a2880c200d500100203010300004160310754029800d086040c1492803a1040400c5038203140310040000050030340000ca4034009004d019140d2241e0002c00500801341e0354100b045680c803901030004000c892030703154000200d9222040c1c05480d0000d43c003500e2160304401c505000c580720080e15851403108 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 943658929 1250 943657679 943657721
    0x50402150406030c11030a0c1e06090506010914010614210c040303030b060901020d05030c040902070f0b1b1c0b0d08091c0c03140102091e0102011a060301061110090501 74
    0x1203004421103507c00340c181c640840e041615551031281c1d11207140034000000c401056900403415030701035011624810b0307000d44036960500d030449003203401e11250102400f040a005004a50f042401000c08019000381e50ba00c42a00d0b1741099400029010151848510001841a200801c801510503248642c41c28445a000081807102601545800314010390210940100d918000e40c01103800c02000014a450141c032141a0002d0780d2020348201c42c00ca4014005000b406005201c503070700150307002901d800100d004c18524940d4010045042000781003081d2800b040000366100c40304690010f815480b0741450703824440d040d5000180c0903401280c299000800c03d54001045915040d03200340f800100b1030851712102040c02001015201542d03082008dc03203140e851111840d0b01c1c040030a1590008544c43e0b00080c03d4543c1ca800c01c180c040203c2805043c10396031142501d054551618040c00c640b0001801c00349408001d0b107480409619058120f1305100c0190043c4020b108104445006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 943660179 1250 943658929 943658957
    0x60302032d0a0b070912110409030c0b010b0d05010b160b0601032910081605070c090212060f06210402150424050306010c060e0c040e01060302040b0d08040603050402150406030c 78
    0x740c0c2d06480f46c0201a008000b0000b1074a00d05a03120603042c41c000d161428202a503031760b4001d0b181000780c1110f100e840d000304449503c40d14078021640034184240b0700d5400c022030084055480800050010b110081c40700008107183d100c1c0e407001c010895141e03400e00030000c00511020400b40c044c00024042c0542d1994003503660300410038507010398800071410a10a090030300c1140e050308420402c580e01c1d02440f000090480c1e550019100584002a0110142c02c182c0108081c2c6000120601c0c000d140a002d81c00040200002c4078800f0307001c003040c850f481c1d82c9034400a0300d400e01e50114400360a601040114100d8400c01c00080c1514003440e420811080600044c1c0b41800b08a401600045a90074800000b8517650412070001d20326108542174100d84000145c265100c60f01c03007490b941e54902041080d45061300a20004220a9400b0000c242c05611801041d00c41c5006080903d0703102e4002c64110b46a285480c0c41c0384540581e51900c41e501c40c20003c01078407802d0b079040001003c1200c4611 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 943661429 1250 943660179 943660199
    0x151d0d031d0a170d0603060501080f07080601080c040504020604051c0501060503071410030b040509030a080a06030b130507030203030d052520010209030115030c09060302032d0a0b0709 81
    0x50259085508243e100b03850058045150380210340745242c01d80c45000000c00a0218000d140c080d2840e0710151003104008805289403001c2940103141d00e81c016401080140000306101080e03580079a00412180c2e2580046880742c4121b5200d00c0d0005469003c0c142c0c15500a9600c2d44201e200c2c1000344002c941d65801c05554102901602c18046500c9070284003601e4190081c45030300000c2c0c10045264207c2d400040c0865008903064010740d040000c1442c2c080b5808020541e0154400104004039411340d00d070515001001443d81c034148e600c82040505000080000700700943e80101100da448240c000c448000c1c140035203081d100b03628000c0c51500641d0b01465608501c0301261354542c040990300c04c1c100090b110400040516540c00c01150045803821300402c00d00710040c1c40c2d449a028510f25142d003104043c0d5000894182c03034030005100580e408900502229a01c54040040f100d03d0746544850840301c030b140341c0081c403800400d042004804840796200c1c0c1c605071103600042c3e54071407441c9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 943662679 1250 943661429 943661443
    0x9090507050a0305090c10020705011403010b0f0f04030c030f0b0a020909150d08040b03010e06061804020a03020d021902190b0f090f030c030c19151d0d031d 69
    0x290210301c1c00e00c03640d6034162103540a2540030007404100d801010310600401e51010b8000ba6010050304443c40510a40d40c11500031014081481d84c2030b0f2441d8500403007085103000b0525900d40010000400011414507070040e1400341d038201c06a150601d5891030101040c034001e8134112141c03100304c2c00150300801540300750741c001180a042c2e64041d994192581000c0c0c0d145100850b17000580100e205d0210b90320002030030103006042410b42da00e5060000c2644030310710060215100d800104840e540ca001d0100c0000e440e05d0040d100582c68544084058001e4016419075100710381c40454440d00050048d001442c0c0b4416a4003900e952014407482e030f0310381c021043d2029006000900105260701d0191064075401103018013503400c00d6104001c0719046034080307a0180340651003ca040c041041d400d0104070b42c440440f03d9941219000d9994440840c2455000000e41c0b030b69036402440320b26a8034000c02488800c03131043c1e0741503981c000e401500074154200380700200764007100341c8681d00030000381e29 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 943663929 1250 943662679 943662691
    0xe070e0a0e06091008010c030b1201182d0602090406091104031b0b0703110106150c080a02280501050604061a0a0e03030a0c050c0316120212160501090905 68
    0x1600399501c200f4080c845002800c40040030898140003d0600420b204140f0840001ea0340032a645003050b0400c5440c4410410b9422642d00d08081644400811707584900c0340c6d640104900f40d075030001140c1d0300d421130282c4004400c40001100e07500c208555030b801012011b400721401c010443d280d803c44401c443d18a80b07030b00280f130b03010407007440807500f41c03c0b500428442c03c003000500036490750120300143c0c02502007100803d0103110010b0074504207004036400780c00c0107001284041e242c0500240700c100c414034042c094000000340c00602034824484141c102c0111065128510799203980c030703142221549401e0710594070f4030740881c810346441d006080c200c41d00000c9030a601440c080303180302254042c2c5107901c140a103c280605040e20244080c2840700d100303032181d0b5034510690800b541081c20b152407051107600141c010150344c0044091440c10341350074039440c000003080782c4081400e0020803c281e01c8940700d2486003102403015410303404203403803003070380d403d100142c0d00c4550380c040c1e031029030300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 943665179 1250 943663929 943663949
    0xd08011509061202091c080903060c090618010219140705060f043b180604050706140d36050a02150919090c1106010b1e040e070e0a 58
    0x80303c00c03034010580181c05005801400d0000320100f114100c1c4499400b41c2048070380940104071800c26107018041103900c1080d40c9141468440d001000600fa8807414103484540e04c0326100d0320183c0d034030800403640100030070040c1c1c04100c4080c4c1400980401c4101412007035118601000c60281800c500380c840f96090000c6160826051012004076a50050000f607440d1000203038a400c05a0480740d80c400740248400c0d501071030706141040c1c00e03c1c40c51543d504000343e484041400b000885c00244903080300c6c1646000d052025014840f443d441c4106149001c155007888070706000c100100c2d2a0f1000342202140018020303546d00703000740302c1000d01c020142c0345400004007200542008000c40d40100840070003107261007045000500600302e43e400080d800708902d8020b2203c0c2180d07201c0e4070300400e99814589602e00f0a203400039551041402029440c0c2ba0114010031024090310701d400321004185481a180c1e6280c41580444030422582d040005100c545642002d060800040e4151013200030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 943666429 1250 943665179 943665197
    0x102060112140d0c02010207090c12090611120a0501050a03031403070e04090809130510030f020f1809060a1a10120509010605010e040b01020d0f03020c0d0801150906 73
    0x610008880010056031051245900094200c0c002e02c14100c510005444c1c0c0c007642041400028540b041a8006402d20f61500b20001105504201e030b000c1000000c06010682003014509400600905081c0100300c48011030503112000450040307600c241518002082603a0b0f0b03d40400044144610003d4081884a015030711101c4c0e8000c010340d4007500030b050401e40c88052074081400c4840c0b45400b525101c0d00071441da105440d001c218940d0200c1c0c014000d001c1402c2c003c1b140700803101d040c80014461500886890b085454911840040e69002030000702d2424882c0014002a4000c440301c2010b4050040050715002c21481240003e41c0d0524407045003000c0345040c030403100840e0b640c000900c5812030f6100480d0481e409020720481248002090300751a000015001c07031484240c081c4664107200602600b0b036400503401a40306c802d0b103009490049811810b40080c811142c0b0449103014001c400724159070003e40f083e040340d102800641c45452a5038040b510340411307009a00000d45510 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 943667679 1250 943666429 943666439
    0x110702060d0605180106110f0d0e010e041a0a08030f0d1109041505040c020304181805070602240f010b090102012a02010c050307020d0302030a0e010906050907050a0501020601 77
    0xa01400c41890108000100b494a480018040809149407900c05059010050007003a501151440b000c64408001340862074220101a45a42c0504010010407a2480008485a00c200c88140c42e8110281c0704100c0740d0351440c3c1560084058208050140b04c00403c0060306c2c240c0002222600051507851b20300b002400f402501c041c020508003240d0009062046040a5541d8030441031240b80c041040b40f289407610040c4000e4688005180c8255001030204000303440800600000d0021100300000d0800c1e404c4481400b60256258054090300c030301031000c541150001444e25070f40e05244a40200620400c3d110300100c4e0301129078003081030180700100484403a00c03010b81a0720f8014000070400e0390300b80d80f2845950b00c80068804000c4141600d641c08035130288a45407283d0303220b1400030714615005c0d5001c1c2d80c0d4104181010205940003000850728a69940040103000400c4003d1090b11000d044c0034014200c26a03403900c590040200000d124034041c3c1303001e02103e00c1a0058492a8682 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 943668929 1250 943667679 943667689
    0xc030d0e13090b0702010b04051006121d0f0d120207020f01080402030c100c0b09030a02030316140a0203090103140601090b070c030203060f1602071410020a0605010b0418110702 78
    0x7941c114180651204410710000b80b02490091041c07407258000200b0030709810801040d6500034209003104484c40e5824805298000e07001c0700d0700c80039102c01155203a00d034442100c001c00003507040c80b40c90003100c0c8445a410004101c88001a00c196603172510180f80e011403908900c118103000b540104540052441c5500803040d9603071180c0010103803199090700001144a09811100c0c981c0020040718102040080307441129820a100500940c10300c0740201d0060340e41d10010b011000410300104054081900c074604843c0c0c0764081c0550262a80481000607680340c00103100540480d0410090a000c901803500d043e105960503501d0100d02d038501034031441300b41c0c00140181c8151604810202c05600d0821840b405800d02054a50030b0380f90444504002038414400c000443d00001400c12110f403012089001480d81114407070307806003102e003013a1b2030240e111a000b040701c0e0900000090001c0b80c0b4015104490366214031640d5603503440b01c0030040303401e0a8418540c00c103080c41010094188 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 943670179 1250 943668929 943668949
    0xc030b0d02040c030b210f0613030c0f05030a0e04050603160909080c010603080c060c031003170c071403100e15130b0f06120f0703031112070c0501020c030d0e 70
    0x3444c00c0006a45000341e001c03400380f401444099144400381c09614070315200404c110001c01c000c840140c1420b0808001e940508015042c2c06001c0110600041c0140950b208102640d181d1010440c0d80c4c5015081019000388400341c04035206600c1d1500240c65818041107651000d90008040c101150400c00d05800602c2014001d440b0b14400f03101960305040d003445402c028600400f5200c3d00d80100c064914a00341d8000c0241684540c140244444000d01c0701184040d40e40c89080b40220740a540c62002145c01203c098040f64071070310b100091401d1001440308600c004c02d80554441402808100091300c440300c034400410381c0691003d00003a0400602c243d0446c03c101c51024806480d5110110980d60a507a0907131340095600c1449082c1c80e120080009400780403001e410340400b52000d541d240c0c0c40a200c0034042c00f0820128070300303100c000d01c4690240ca000000c41034035050f26040c8030300c41040324041c9a026108100d06d0325200c0c03034002040640c4408699a40c0310004004060000105d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 943671429 1250 943670179 943670201
    0x70f0e03030c0a14011e06140a0f050103020913020307080f06221d060915222d050a05070605130303050c01140f1506030c09091b04180c030b0d0204 65
    0x580c03088003506c0d50841c0d0004200d000304800c0c0120b03840341400c228607680003070001510700ca48102a01004140040403800007114024200143c80b1016080810304442d0044c5a01c0e50480c800410040c101750024601c9001c0c3d1702036a1488816074400b014004804a40d00701240300e1410400e4042c160a04d030381000050f00d55141104030101c40600099190940544006200e5080000d403000701c882d4501d012940b0031000b810242c0410030301044c0d034091030280840500750148001c0d03010580c400035242001354190b00808440c05100342d0500c3e589868a40d44121075a010303203000001c0044c0302d881901c1d564407142c00c50041da41d03c3d5a03002d45050b030100c0700004455403928990001031407902c61051148a46480a81e01440d140400e441001d07402580144641000d00034860304032041005e644038800103840402c90f85c3c071404260304459001c0c16665400d0345002601113913040c080800c0c422126400b120034030038101c210000b5000c7e2084486455003240c20b070500c950142c50540c1203100000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 943672679 1250 943671429 943671431
    0xd150e0c0109170f0102030708091605011b061d150a050402010f081308030703050a18030503190b03030c03090a1a19050c010e031b0705090a091a070f0e03030c0a1401 73
    0x80340104810309a1f001120100c010075280c3c410022414018001d0320017880654ac0c5502949040c079002070031062001c1941040400307003810440411140754072422240d51a00354602420303400c10754441e0748a0b18139440e960f070100050081501f84100303005003070280d80d0585071940c901d02c2c180e1045070065001084d26203000c0c0c0c1040254049042003000718015000b958010501d0f2800500b100c0c00d94460540841900001640000101340d01009803500b04190318081d803020030b40342d8074180262030b003480c5459142c000014202c1c41041c0001c01010150703070a941c81c043c41a034445d90340200c1c00d50881c4c154184d680801c0301c40b00c410714401640ba280121410164104803204401c1400c4422001214906900028000a007030300b000f00031421034145c001c014150745080101141180001400700d4245035102c250700c6042000110001d11861200081c3c01c0c05c1d8602050020300350b1810001c80c2e004900048402002401e01100704ca5420b00f0306401410717140401c1d680c00700ca0300c003a950020525 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 943673929 1250 943672679 943672693
    0x120306092009130c0e100f12200408010204030611030127182f151b0307030c02091b03040b150d141204030c1e050d150e0c010917 57
    0x80520035071560044d03030340e202c0d40c0310410380341407201207100c2c0e1000000307111000780c810726100d50040030f8050b4120248008103140340416081409021282c204815042d0b0101c1d0219030000c05501910480c6d02480b4280400311003030f0808480c911003070180441340f80c100c8000c0c1c26510b100e2450520110318000f07000810a26104034070081204422085650000340141035120600707650140312035101109000b10007604003000112103113140844242006400318051000440c4080d1a401400544041c0d9569050ba8075009000c403800304801c9124100100200315000e081c1c980b0550241040b5204500e1501c42d610340c2048031400501603440011515a051280d032103404080c44000d1280d40703504800344064413142e061040c0204c408086c000140b00400116109585a200f2070301400c0c02241c41407010030341c0d01c043ca40c00c0d420464102405d00d000703000f0060075032020160b40182540c108031181d14070440a480e80580715049001544085041c04454420a04028aa08070300304039014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 943675179 1250 943673929 943673959
    0x4050901030515070e2101061e060f0806010807050912100218030c0a061101060806040c080c0d02060d0c1101090c060906110a061d0a120306092009 65
    0x100400036001198203811421000f20041100c040050704440380d800e08254015190300416402c80c105056a0020354001042071201402944618003402d007040b1410580d0f0300a00043d81d18008034402d90b00003030010b0703205031425031088d90301a0180905a54036401790320b03400c40440745500010111540a0b440a00140c08060100034200d0f00300d2a4507005030303e441c01000c501c1d0042181602040c000d0300300404500c0c4540c0e0700e401d080d05031551810071a610702d00701031b441d9004220301d80241c64dc0b03104c0c440500c07083c800d60789482002c840d083c40440e002032100340103100f000f07030020b04001c0d00070605202800d040e24080c0c200300101c0c2e40d14540381200c0e0030406e280c0d0b0300b0745100640682c0c12404046051090a030312061960140429082003e199045101d483d0b0795620cc40c03c001c1e080e1a50707a84500150111801c00005480040d011110420b4103410850340402070321703204401283c9020800600702016000300d11080b0311a200030001c3c3d140c0c0322160710713907171784044881035000c40c2c0e060340000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 943676429 1250 943675179 943675189
    0x503090a0306150801060312110307050d05090a090b0102060105012316061d0d0309030e1315060c021c0f020a030b04120804050616180b030907090b03100507050405 72
    0x55001d80008100f92000f003a1a40d07a14001d5048203540c1d0b414180140089952036080301030354030301c40c5402e20000f0707403040105045008400004055000c0d60b0003811480d03601c5805444c1d080c40c203c0f05020074035038903a9400201d44000d007000e80941c01400040003c2e6001d03a0140c08440d211021800001c03c0d034017506d0b0b0040e07000034502143e4003103401c0107100f400f0322442001d03c4d01c3d556940c0d5800c1c4042c506a010794500c0e142082c1070805450340280c408051081054500c00c00c0d02902c0ca505500880401c1c2020f81903000340356142d41c100480018041e489400340d40c4174250042c10415801500508540c0d03000d0340c407031040d5216411003040e440161544142140258011008542e40e4209842d0594200740b8003040b00040095180920010540202d4229085064480c030b1001244140c8400d641c0031040d0108143c1030050030030009409a40d50008500c02c0c00440251444a51125695021505000d1582e03030150321240301d1401c20440c980c0107640200441c18286d007050745d03580000d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 943677679 1250 943676429 943676449
    0xa23011e09031515091a0405071e020d1b08040b190215100b0903010b2701050a030c1a0c010c0c02010215010b16151a0102120a08010e04050309 63
    0x800210320700010014420400c144002e1100c05a000303020300700c2ea20800045207030190107170045041c1c0c1c40440452400c0c3c01d0b00346002000020300203201c0e92400b074801800c4070b00c81d420f0306148030300607905c03606001c0d10104412030f4094107900c0307030300c1420040c1c18501c0f594031454404490f8160200300114040807404040c0021b07003030390715000300d1820000b80e0082c00c01c0000c03e104244034445a05018940700c400207140103076255007488903260201800024050020680e065030006940140d140070b10742142c101d01195115851340d83c3c0c150740d0350428440042002c0c0300246c410000b500d418040054041c07090b40d03407268580484c40c00c00752044201404c441040e040c07000800e41c40480d80045517018000c500c81b48484011101caa5854603070245aa40300d50340a2000c0d8000160000007000382d080042ca500401c0348008204004182518008c2e60010081440c098403401a00c1d00740b00c103105044a22443c40c9648403c4547d02c4d02c60468032125000c1d0080310140402d0125040940b80c4034441 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 943678929 1250 943677679 943677737
    0xa090902042307090b04060e0d03051317010b0102061501050702220207110913020f030a0804122102190212011e050c180904081c0c08060a2301 63
    0x20740385402d0a0343c001d80030254a9003c1115440207010820072980c002860b11a4954140c55882e40b40d03810746022511442008c54007203603c440c08201040d8020f203100c600340d05070f070341c0c000800ca6100040016a43c03504100c542c0383c9a210041040c8000d9446a07000e040d4061010f400d10540030381c2411090006040d917520f20504070f0340481c004083c4854490000785003a000c1e0b034052180e0518081050481e62070140103030180552540344602902e0410155031501e4001d04482e0720385444411100c10401c4655055624204105030001080607450f0303200c500d20740b55002000042e840c0c1858120902c2e4824090780e004241c51518400040f007070041d1a04031261940f8140030689044400342150006011504010001d01031621101c0080002400e220000c541c2c41c3da0070394461514124034840e030301c055803241c1803035a80205000f945400c051900ca2058503205c0c040d50302c0c54240408a40b80744500020b41300002d0700069104042c14420900d6001850315045550b4540481c015000c104121 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 943680179 1250 943678929 943678991
    0xc1208130e040b060406321c0501050a111206040207080a0f08091f0506061303050a1502030c09060703142b0207031719181506050a09090204 62
    0x1c102c1045030b201c407010360120301210100805810b15001c035040d0345152001c410743c1c020028083c41c00724024031168160440007010b03440480040d031841411580320000881d01582021301240198401b80240b5015503d40000c1c1030500461000300580d0001c0034081c1500580d00b08200000f0501140042040c0d1529844440d41c02200e8140241400402010a680c5070000408044901d0b1071f1052a0110b174001300001c107080d05c2d00c1000810520910300e80c00c06081c0c140c00e001081010100b16450502c3c0125a00603d2100c1d40ca00f103001d1744000c507410a6802c9017001140071a241c2100500b14141c024130f48100c1c0d04002141828842e440b0031107068211044517034910303101041100c640c0049450340020342c123125031950081c1288140c0010b01c2a500e4502d000210018480b41600740c2008280d041488032150244c0306e02d201501004042d2030311485420b928400b40198007032041100c2002d000070748140d103000c0c006402402e003a9401c0740d200740c55078116400074143c41e014003030b85904504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 943681429 1250 943680179 943680181
    0x108090c0607020d41010507050f0904060b0c0106080d050307020c041e0f05190e0304171f0f0506060703080c1e12060118030b070e0619020c030d020a0c1208130e 71
    0x1004060200d40d00c41117444aa040108004941c1d070b1103c180c0e01e1881c09010300d9916401200000b5000d0485504036852070940815000d6580c203054010320200d4014806549805803840310440b000d100454455015074001483c2503082e050980c0030b469a840009070006402e00e10300c81807400d550f0a41700b4920a941c0302e000340012010060040084d03803840c10003c1100400c11000f96450740110303c1850b000104400031903040003030038444c0c1420321245005003041c19080c0402e183c001c00400085014a13840c100c0014281c0c10904111a50940c254458480c6595210903540590344083c6aa803001c10140d0241048442c03070b4000346c042d202c0d82e103050f019a450000001400aa030352444909150780230b2030104049500c5080841d0814050f1800740340b40080000411543d108451320f180803190900000322040e980440d000118000841c1910040d81d410003080384d860b06109800303450f8452080b42000000d402e5548203802d548555031043c2080440001c9944500707160b0f10158200c44404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 943682679 1250 943681429 943681523
    0x3260307020120090d1203270c1208030a110409020f1806030c120a020f043c27020412061b0815032107020108090c0607020d 55
    0x540281056125120490500715030b10005207802c145e41030040c00704c81407000d404040c1c0f80710b0f40100c0705d40b004c504900500d20425400741180d16a0034041035403024030321200844d5030058048001c4c105030300f29814900310b40f0b914000794020310143c14961581e071010040080d11044e5800640078911604042c280c86407180c41c03800003200900914184180010020031042c0b03003440c800da0340313010847d200740141d959840050000074401c8511895a052010a000507011781407811007094807507811041c1c0340e00d40c10880d00202c02c07000a02001800c0311943c000e110020303401c1d801910320908203a41d00c5001c107500109000b26802a000046010305800319101070001e18090000305852240405440c1002c2400081c61410090f0045119080700c4003014000d0354100184041e1000b0b00d010b00f03180d5140700e80ca88569520055049011444080000e03802180c04101070b01144000350116180044650070480344100a400c122442c0c05890302520318150800c8802c0880d9201c14690b40c00c0700041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 943683929 1250 943682679 943682711
    0x3010203040f201302070506010f0312080c22050117090303070c0c0e0108070519060e101115091e121e030703061a090d061805101508070e01032603070201 68
    0x50304000e2400300e80d035030200f0001d01c0c25003100033360710004d2605c4040c0d034032144181d42462084040c2c809100d14031341e030108040904204440121402602d035418800d440400d401403403d030881d854030044d04144001211035000e41c00b9902650f00c41e00060008507110700034030703070490801e07000f40c1f800e030b40849001d2103e400e00c2040502007000351f841c800946841c0900060101000c480d50320f00030049403000903000c40c001c0720f032f001d51440800d040e10364110030080101c0c2107c0040711850981e1141e9049074110b000d103c075004240b15440b502910060300148048421035011070490030518170b012259210031303618440694040c261955000c00e00724a02030900d4440c400c0b20404880200003040b2211466407680c444108e4030783e000e6804610b44094400c03081c03005000960240c8140200e545640220304242d101038041c11800316007410b100d4440b4209a510401d5016038a14850a0340061021840c00c603c26a00c90001c8012403035422070380d40c01c5e6000d98005980d00030250303444400e01e0710b0345800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 943685179 1250 943683929 943683931
    0x201020607020a0f1e150c021b130209121c2c0f06040504060f0f08010905071211040c02030702030609030c2a270603010203040f201302070506 63
    0x810b200800107107038140c41321113203004602c00060070340c8040000c8101488003100c0010501e50002c1d03040e4801d40c0080484006450381e411000c0050285840d0008000310501140c445080c020f050f446440c4080c2c07003203500030350109030744907485080e21203030030740050b01001a045210402c0c03110fa150301c0389440c4003a10a80707a1010300c6016800d0340b030a214400e60702082c1d0603c0c441c0100c50141d040c000c56001b141852285801c90f680040c02c08102103400b0723041c0e20098044548020b0a02c0c00a5942c0000a0032249002002403c5400c00e510420400313003198000c0260a000d03c0c07511081d2080307140003c08460741007a03400050f0700003241c44001d503d8107002c000d500c1201c4030701071450712040c0c6480d50303110340780c5024031704d240c80360b41012040c1105145c0d0302042050001c3e045c107031021205528242e02c4c4041040c55000c1c100340000162940c2810f0080c2d030300540d40038840500c41c2d0403d580301e00b01088880d4030a441d00800f0500c2c0400d5640e1b40c42e26103498a0b03411801030759000ca5040041c01c002c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 943686429 1250 943685179 943685191
    0x120d2a080406030513120c151a19081225031e030e1908040801020a110f010e030307030b120601091508010e0303130812091b09040b010504230c040302010206 69
    0x1240c4950400030986c06051807080400e985005010750306580780c81c144001c40c1c00c0c0d200b03410070700d0280c01000301c819151701c22803400e8049520341130710700c20000c1c0311014010710701402c030454116602e03200e101740218010340444041400034114032200c010300040460504542640024448007001c0c11041188841160384650307032505010201010095943d507000d240c003044068440f0360146802d000312070007950b0292000c50029561850203060080644034070280300782050041c802d0b0304850040510890b0102d0250070065411565211000c1d001007a00d4003a00313422421300c0000d010100750500415020344454000040c000030030125000c4041d50540240400c1d13850070310045038010000094942c003200c034040400b80c90f00c5034686804207028920401c080e039a0f030b80081c400c50002c0890003c4204d40700c1d80d20804044541b4003000034017401910081d0448090800500c03850400d43c2120b0002031003542c40c800308115006210b100702600300c031018501d9001050900c00c641e8103014240c0c02170 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 943687679 1250 943686429 943686451
    0x12080402010e092701111206010906080702190c08010e060a0e030406050d0f060f170105070306050d110103020c030409140603070e0718030c08030d0b120d2a0804060305 74
    0x100d804548038142410020211008560141c0320104c045401d4000306a40260f00943c02d4441405881c0c030601d00000b038852502141d01c400f00451584d105540262140c1c1c1d1941c000c0684a54120341d0240c1d0a140000940d1880748480012801c05024054007042c0301006001340303100d1501e0841101150300d1509005002d420402c010130465900800b0b580e03110030079050029101400034006401030003035600000382c3c410f41c002d00250000b11b2450f10007007600e0640090040d540d6406044045449900a95602c4096007041c80e01007200541c0041800030103040040c41c0c5644403541302d256402940c80042d2068031424802c0c5880034443c00f00784c003c01c0c1600200015800c1500c01101810010000810005001c55580d98400705040c42401190441184903103661070300c564035200c3d880781c045400ea4908140b1382016505006000c4040d0a070400d019084800e61600100d070181d10540440f0840c411803040c0c203121400400440240c1445400459501d500d030182c090300303448004021030400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 943688929 1250 943687679 943687681
    0x80414061e191805010e040f05070804060b040b0a29030109020a180f0b1612030f14150409140304060507020909010213030206070302030c06330a09021612080402010e09 74
    0x7609008035410584009080006a80202d1001f103401400d10b00f041400325400e10084c040e10a8104440f14003560065000344094544c900a0205540401c0740c4160054070800080060300038003686003100d00309072103480310b000505034205040340e0400c0c4c11194a50350b0000b0000724a64200b499501e20340c80048040d00c00b2841c005581118806038842d18101c1ca40001e40c0d6405100350f0111900200d50085024100f2140785000900902d0722010201220b40380c2491070038242900500700c0d100d4080c10181c003440100080500c0080d010040c0304954207502d208003820894800d0000c2c00280600b55690354444295004000d40541e002e040307180e40e0b91040051102010194240f0003e481e01540e24555440040c5422451842050902c82c00750150303105229501c003456401c01d480100821030f106140703040410b0035007908014060700381c0c080c2c807400e420400d07005e040d00a4102c105222021190380012030302c8104a000c400045040010000400c10003190781040303800c00101015079642100d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 943690179 1250 943688929 943688957
    0x30c050f040509121605030d020418090b01032004090f211202070c03050d200c1c14060403050307030f0e1f060f030b060a0e04080414061e19 62
    0x280e00c403598070313036000c0d0f0300010341845610000c1640c1d0300c1641d030010459035144080c181000094005024506c4d450000380c50950b021f4029000b0900e01c6904080360000703036444c40e40c80610802d05441c05142000d0700d00d2034000d05a99a11842102c28081e2800440d0060f01d2700d40140140d4141c01d151003090070541c1c40168565005030a6a10003040345001656600c0904040304c1c0561180d10081c040c0c41090380c000c00459010041420200380c005042c1211481c68450310344900d03030542c2c010b4102e03114008a00703032040c007050071401e01c5014085143c1f100403811034007403d2180840c0c1c2030700400c0c0004180410b20f40d0520903e02c6180c00c0310420000c40501c602d04a032503000301043d4000c090f00300d07060350350360701c203190312050091a52201101310b0b640c2c0e9103040b11010300e0448101d4410085000001004003078051120301c43c3c0e6008200d84c0c941800c04038854040c5440070b4190f508a0002e0203404007225000b410f103034680f44008041c0e500c030404c0610040c04801c003800d904042001c05d0703240071a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 943691429 1250 943690179 943690183
    0x20417060f1302150c0a0507050a0b070818040e0f160609030201030e07050a080714060a090302060c07050d061a030f0304060e0409080f040305061e0a0506040f06030c050f040509 78
    0x80c020703412014a01c07500e4603600016041c1c00c90f10509800e41300b400a00c0030165640020200c486911030015518026aa00104121400507204400c00c1c0c030f800300071090004000c0b00051001c84404011607081c0e840030408a0304840d803580b02c031000303680110502a035600080010080c0c040300b0745000c24241d400d08070000d002c018540310080c103140c1c5580102c3d0300d0807414410070000e480050302c00340c8495600e041e45070303840010b4820108021440094010340f400e02004032204150181c845010051a642c284559a804007180c00c0c480d00400c58042644c0d91414a1341400c10700448002c10000c00100e0350300d1003100b00c0038005200340c0c05404980b241100201c25a41121407a041c03400034404034002040c00303046070039002480d005000540c0101d100d1001d01a0041d617001c1c4085480ba03564121500c41401e0504040780d542580d0500080d299040740e03000540c0c8408044c2c404511103072440749000030303200030303400485030020f1151091000d410700c1e000203078400721f044070305018904003484466 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 943692679 1250 943691429 943691431
    0x504200a0b0f19020706090605091c0f050303070c06060803071208090f0f0d0e09090a080f040e0f040b0c210606040b030f010f09060312080a0b040c03020417060f 71
    0x35000c0c40420b10003091003010341030302d070b06581e0303440c01d2200c000c0043c00081d2600c18034080c44000c141c88000c042400352042081da5096400a00311191803844862000f141f8114000c040300c9604103103203418009101800518001c6d03a20342c03030301c0c06240740754588907040d121141c100181c0c0c2e90040c064400454003a01902d50200e5003804c2000c2a502c4d100030031801c24006200200d040d100744d0140c10014580002c2c00070003400c04d075861541181079002003004020068500c901c1682c0800d40c0309000c0756040006000010690005038a055a166214104224210b95008902d42030030304000c14840e14070b04503075201e100058000d280403484800e9042241800c1c003a0035448198800140d5952241403c0314041c0100d6450140c992505041d60700d1085006d0188000000c3c90100004054480d40920020b4071b900460610050450303000c200c8401c03500500e01d80071240c0b20f50460314030340c80368400c401303004106980c050390342c90a0800300d216155141c0030580941d406a820412040c0744d520000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 943693929 1250 943692679 943692689
    0x503060a14031e21030609010e090a08030c1605030c15100b0904063f020a0e06220902031e030307080a091b15091a070c0e04060504200a 60
    0x204907041c0068021601d814080740c000121000d80001320011608441c000e1840303154100ca900425a07218000002d00c0702050b135540c90f40b85e001c0d10328a0001010785000d10340c07040b00c5410b80f83c00d11218803802180341600300c07000c0c6e5294100142542e4031207410f00c000140c280142d54008101e0a00040600740343c0c4080c49820f0307891401092051503540c403900401c0051140e0051001c4032980c0d02c6039040c500502002c0454103007042461059140c00c80c40044d0304103900104140b41040c685018803006c003a000305003e0307005415000b01a00c50920f44414485004180b03400141c500071881410f250a0303804c1402c0140741040c50300a2040040041203941c01902460300c001d050701d0741507140d80038060950004107102c50206d141400d00b441015400100c81c002c000340c8407416041c910546200140e80142c0325a100103120590010a40b140103007181c0f841135030710b0109165910001865071505607002ca40c80e5840d001071200340090015014140802034861046600c01600000c50f509294490 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 943695179 1250 943693929 943693963
    0x3070501120b03031201051e0306191803021e0c060f0901020717060a06230405090a1b060216060c061107061b0311090102070509090a080a0503060a1403 67
    0x800d000c07000072034002040300785001c1e0480740c50705003a030050103001d1002d005403402601c2d9203841c0d100c580c15920701c0d52201e103400741c06001903842d4a6000c0d041442d100700b10303c49035900c84c8211510b4100303030500360402038001c0c4e01803e1500a14003100d04500d10b402c1c8010300641c41030002c408981d0b2060b044854078005011042ea46841130801070b402c2031070369803101d001c00c1880d110b1103111071008281c6078810880304c3c608115030342d1216003c800701d0b2107040d103101494040070743c21215806c0503803200f500502c04001b12880c0e141c003681e640800e07803130b00ca40280009507030706400c0100540403c040f800e00c0b4001c8407445406420000014070704000a14042c0c0301c01e40f502d401e04100d070448070441c1c1d0001d42000d02800038519030401403402210b9030005038006132401240c6c1d407607130004405844001c00164042e000503894482000340314480a02240080d0149980d14000245c00c03100074035400c07145458041d100e2034160204648584664000030102c0d01302c0703500884c540d40104041c03580c200c00000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 943696429 1250 943695179 943695197
    0x60305041e21091d0a1d0a1209060e120f010f20120a0507051b010b0f19060e120708240f0c21011404050a0e0607140c06150909070503070501 62
    0x4042c0040d140342c02e41818116901101c1c80c1c410100807d101411600540c0008000601d40e40100c84d541000c3c418500001c0740700340c100c00719103885141c02c91710521601c01c50f0080034208501c1070031203080341d030303444495540d40c03c00c0164218a5401c1e403a00303441030001c90b0b041c207035240f4000403e60801003400360300954a000040102c1d000b08140c565035268030014118100c0441e4109008107001840c0310311900100090604a140c11019954501c0782020b50a014a2074500d0950390000c509e201d259000055400d0340103031640c104802001040b859000702084809482000c000d4140410b48900e42c0c20602c04200c40200c260140c41e0700034841080c1641d86107540c522010305000411500458200c2090000400f1100e0359a01500b0740003c440801c1942c55004040045070183d09a00c85c0c590098000681d038180184620240c00c0712000d031480c500040341c00d0341420304070202d9600c0103082a0700ca004215003005a807250f8041c00c0038000b80589400c2800003561a40548200c504004004c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 943697679 1250 943696429 943696441
    0xb04061d04030f110d082e0519050414160804020604060e0d0510290f0f0114030412030b0105070c0e0a061802090102010e03040f060305041e21091d 65
    0x58024141181c07003d81390000c103003400c001c3ca140800c0e10747c1d00c0e1020b402c1c000903841150300100e0901c400d0f003020b00412124500010321844a0b90740c085c996480740800710015542d00c46004414400c40c00c680e01e1410307440e040388000b841c014075104000420420508005c0162a0401281c081c0c62460802d035001b602c1400001d40041544080202140a68850040700d042c03290402604030300c0751104074004200c0c0901004544034008699944030082400022041c28109450300b0003c0041c034200c00140d15800314410b01d42c0c4255012900750300c1e01d000e211340050380f610903080c8800342480c08034507101d0711362544841d00c2120f000d8000104207040c04604131441942c0000010202d06214911240080385000029084072034020b01650900c0040170075044040201d0b030660b140e2614804405090140440080000500441c0c00200c0c000348180380c891260b0314105820711905c001c41042d0000000304590082c1c6512803024001200c1061000c405c11603680042d007080030100c6499075840c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 943698929 1250 943697679 943697687
    0x60c04030611041203080f0106050c030f030702070f081b3c030109060b0a0509011809020a0b071203150b090d02030c0d05030301170309090402040b030705130b04061d04030f 76
    0x20758041544c0313401450603441059002186d1034800c450f03a841400851381d0b03c000c00e442d24490150611695081000108804217101e0702840c3c01c404144104c8241c16203c0044040c1d500c2d180c2c002d40101d40c845881a010080d00001040e241007003030319101040303a0500c0e641c1015044c4001c0b0440300ca40c1c0040c500c1031454143e1003110031071134010001d01600b006810b12000030944601e80034059202600003250905010300e00c1e80c101c0d04082c24001c0300c5000341c034140740289030f40e07803040760301c00c5070341034001041d00e44100603040c00c9001c0c41181038044a8100c001d001c4030072008823662078206404c01000f281c0080015079902c581f090702c03c10310000e040d100280c10480422042c03a0f00c0256100300c101480f000001550507200700b80c45d04400c0400c8070044680d28010590640d5214036448005001424180c015041d282c4000e000c07a1034203074070f8100064588004a0382000002e030365a0740181d641c07070325000700e0000708100c000300880c0f04c20410f402a42c503417000380003405024070101c1c0c0305075261103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 943700179 1250 943698929 943698937
    0x1e04150c050a17040e0901020c06061026070e010e031c090801050709060206340201140c0a03180f0f050a060504081306021c030c0306170a1202060c04030611 69
    0x80502c003056266800c40d843c403190f400c540640300891500f02c002410f422414800c4610440d290b100508c1b490751500200041981405014010007400b0b114404079910f05842040656040d109000f04a1422900007000c1800081405042241c1d1048100c86914080b42c000000c0c0c016401541e007100a44a0598003120302d40d00072102c1d98600000c01c85801da03c00402000d8500560955415484100c0095440482c1e80d04480040d0540c00c011042c070f2000c0e560300e0380c5450f02030002080b184000301050506100881c0d03200140b400c0000c200b00e61a6042c41858080501703480c1d07000010b080c80d180c0808850148000030030558040c03068000384207040102e002410ba10260520007807a213460011202d03001107110f2200001c49110200d4041c0c008210f1444800c01402d140300003500c1514105c0c040d03c0c2102a01c001d140c0c2e20800800c3d80102690111107000400c4014040c0d007005250082c0c1c0d10034488900d10440d0042424000080c00207000ca6044a07008200400c90384803c1e2032030307655841 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 943701429 1250 943700179 943700183
    0x813050a0308090a1d150d06020327010e070e040501020403020d05010b041107030e0d022409031225110a1403070e130209040f020909031e04150c050a 66
    0x1940c034800104011928008200b00901a5070800001c0d903500c5100c1d040b051000410501440b0000019601c840c280201c03a251001c0200034403903100c01c50302c070380c8103e038000d0b118845140c00c06081002900342440600c1d00801c009070082088082016006403181441e00a40800e80181c001040a2210075015070740a96001044c200c0c2c05102840d08500030000e40010724001c600740b181101058055405941c40c0c03e826440345421084210100f2044800300041280d0005103d09911078001c0020b8482c20715900110200b65034550090805203040c010b81182d004200701000103640d00c030b101c030301d00c6a001c3d002c04100c0c0150f40000c0c0b0300031825080000c120f54102804040004000781d0003200100448001c2c2d054504694540e0034003000c0311000c8980c2c40343c012a0850240060a1803080194054040d020ba00301c050382a50026824440c03c1d1403100450780046500d012004082032000f40c42d84510441394a041d180c00b080408510003641c0074800c1c0100440d05d074044c0001031050468480e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 943702679 1250 943701429 943701439
    0xa032015060d12111212010b03040f050313090b0a030c05100302190e10020d09050f04020705011a0111190204092a090b03060103080708030705250209160c081305 71
    0x384140c00100560140d5124040602c5000b0000581407201421506001584201c0020aa003800c01d2300503d81c2c405041161410391707841e09030010910900240c40707007240e0a40f035181c2c4580b0b0300c1003e80954440c071108500c9560103401c10000a440c4035440ca003101c105982c4074986c1c1a6510301075000b4051380001c016404102550001096031296014001c40303821121410800c1040f00106d03070300c1002914010104800c90420302003480d1200d400007010b50001c2c005490050f00d5aa4142951048c80d0013100c00c0d03804060b03507900d17580c01103044a0030804210041030148690282402c0030305845802034002c0d0b940707030401020301101e500008040c04020020007446c6a000b55080700400e014031400340c0b00c1e481c142c2603c1151401007030302412650007224450a21850362501c2c4015440984101c0500c9400c10010030000c0f07040b64650403032003006a8440c540d4003240144411108010315601e58226682c0b0360820058121030494046034000300ea0360b40ba85444550540081d01c650445a442 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 943703929 1250 943702679 943702703
    0xe071407030e0111011a090a090804080a060608060c0703180314060601080703151406130e010806070302210a0608150a0f0908120601020106170a032015060d 69
    0x4075820280e64070b40c1d540d081e6601c40380002008605400c983c44207100a0126661081d00c3c03001d032500e4000142c0000da03a03100000e0a0882d0b44c4c038204582d01c194070102e501e82040241da02802018440e45009084410142c0100d160484076005240324010004050008003410903a40031860420034000d1a44890403e81e0b61100180039030b95948110380d018000f80d5408001604180f003030042590280c0401d400070309148c101007280c982c0f0400022815040700c002c0c400c1e000014100d4642500800300700f0b40c00121541030008990078407800409030018035004000403440d10326401400070522020401c4103046031904401c0d80d001e00040c0d8058070061086c420036410807400c50000900814108030200116644409144143c1d44507900142228405008880c0c6104107101c140e41d00c808d05200000b031407600c0745000341c800d507210400f03504181d0280204008258201c1d4514602e40c02d0102c41a0427621580c41380f5507111444041d651082c1025400700b002a15807040c1c5030035903135214140e4820 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 943705035 1106 943703929 943703933
    0x2e0602150c070602030c0a120204030209070806180106021f0b010813050309090a06211709040204030524010608270c10051e0903070e071407 62
    0x380501000b07810b0000304a0b2000314850892110502d8070b9040c101070041c00344070b260720340d00441c42c0704100501c0540d403600b20159101101c1d01c3e150800ea510000810ba00c581c60b0000945249076410000c03602a1f00072400c0f00003814a0450405a096800c0c02007055500d11028540400c1c40311000ca4006894100405080c0c0d0140c0100c03840c001c1d107800401c100d813504507064007581d40c0c3c5100c2440b04c4548010520716407421101c10101c0d01d2203a817580c0070700c1355050403c0409080009003103002500c2e150107032801181c0000c1038429200044007901c0743c842280980e003540301c44a1380045192805075200500400b00c403042200000c1400801d0100c085406103140b52a2042c2c120703246d0f65030b80300395040941f0030803a900c0c07585604030b90004400d07170711100d81c12500c029800e2040c041c2079140050b581d0121400f0086224041e100d582058804a400e24640c5c52404000101042 = true := by decide +kernel

theorem cover : BRFrame.Cov 943525179 943705035 := by
  have h0 := BRFrame.cov_init 943525179
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943525179 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 943525179 ≤ n) (h2 : n < 943705035) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
