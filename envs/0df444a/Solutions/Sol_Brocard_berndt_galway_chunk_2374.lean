-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2374
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:31:19.286093+00:00
-- url     : https://prove2.me/submissions/311c8161-a593-4d27-bf1d-d480f76da860

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 426798561 ≤ n < 426978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 426799811 1250 426798561 426798563
    0x3060c070c1a0a0807020613060c020115120b0906070f03020a0905030d030c020c060708090904020102070b0d02040302030601060804080d09020123041401030e1f1b0e030f0d14160b0112 81
    0x713808078954402c001207860b0402110002081c0f0141d0710450702103500c95004e00c0c44040a03000010b40d20391107101e00d012072030580d40003400c40050020000c041011103044a42c0041c0740c0d04c0106514201440f0103071020400340744040402d036020407082a0f55100780c0d60301005000140c01d450103003042e0300c1e00402610850000001620542d64500c4407800c0c03140c00c54606a82115030581842c03000c0c010020201400350040e4118813400c41c01042046144004000c004060301c00181d0710391461061505105050348040203104401e4100004185020110341d05403034000c00004d545804ca00c0140c8080d00d490080c034130850402e54103208242011001070007601d11114440d101c40f903100c00114140c1c1c4a50040e45465084441d58664180314100102420054030700701003481005000b42441110411988900040d465070b40c101c02d6003010703c0205140301840c0702400350803282160140000c0590303d040f0000b00d200089280d103801d54080040c04940c0e00071488419540d42c0c00094017a4108100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 426801061 1250 426799811 426799817
    0xd0c1104020f070c1a09041d06010f0f0801050403050706090f080a0302041e0303020d080a020f0d0b04051b0a0c0203010b0d0f02030d020a1a0a0e060703150f0503060c070c1a0a 77
    0x901190904d102081c85d00d0b404ca1070070482c0d140c41102014071002e0681419005c90703140b142074050040c0344061017001d01809410b0300150443e46480b0f540d5140c91081d80c01130341f8030f92400c01400f010a62110840380341941204010640c81907a2030808582d50306c05901500308a00443c600100741c0e07242d001001140c1c21300e0034903440129000f1940500ca1940c0c44020056401054060300c110f000d01d86031a0b1111203450010704003202038180b04d8103944408900014107548065482e51f510305442069007000c000d0a4000050300d0140603024148030307140c01d010074442840041002c41d58250010505c0800c0038009181e44e040600d000c042145003800100c0c4240942e91380003015034800184a108290051480d18502100c080c0d28148140003801d1010403030b4803480a80440c0c07504106031800f4a900c0e07980040c8002802d19241c568480c160081c4400741c0b0f6043d000c10039039800180c100c0c0c011001d0405550b0301c0e40a450110110b41c000e50103c403c5d10000300003c034000034803030064854010103031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 426802311 1250 426801061 426801083
    0x3170103060f0c020c0f010f11060c0415031509051005061b010c0f09060f0c050d120b06071115070c1404050a05071706061309050412030606020d0c1104020f07 70
    0x480c0a031317210f41c600401150801421007640003031398461107032180381d000d041c10a0000001504441d40c10200225a0108503100004040101780402420700b001a620f03880e08020000320318090035102c241c00d2151801903600c607804541c4401c152003071800100300003402c40da03031855802c2404c0014040406020380359440e00c40e500000c2030050f44a0079214005a840c0801b190034040140c40d184182600102005640c01e0b000c00040c00030000c81d210b0070000d444540380c0ca85509004400d4400b80c1c0070540c0107401c01d01c00480021100c00303110b501030340304031020040c600a42c5a468a0b90142442c003400d61081d0b4400012034544401e005100c60505a80a01c6a0381d00d501d01802070760010b4805c44000b0790075000c0c95000d07a100501d1187c2200004142916180e89641100000e8045401500901c0e41c1c0300140b00401c0140841c1204602a5040074405149812800707501c0e6034440802c0418000054540000c1080d0342c00098030540d0001c0c003c40d00c400d461305070a50f09400104003242d51841d95 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 426803561 1250 426802311 426802331
    0xa060207031712190902060a0c0203072103030506040902030111030a060f2303011b09061112090d0501060509131e081b0a02040c0c0318050d080703170103060f 70
    0x1030301211115200c1c1404079200351113000e044041420030811180304039039030381040401644c0c0d8000806619443d590307280400703000381c01054100382c07195001d1140190b10003041c98035840e020315075103040e03501400c000a1359562040464080d00383c02c10001c1d415481c00f40d001034114000c03005513002e1109c8038000c000c41602e070079141841c44c1c55405881c0c0000504043c0c200c0b01e0300c010101110850b806400456045410700200302801001041303000802c80c4540705111080c4e00c040d0086000341c0d000f0060201c0b000c1c4c0002c000082c0b0810040501072203034515644e0612000350060002000040c1901030b6610b40074405010341142c5a17030468026103041c101e42550181b01d04503c04464200000c14500a920003200881000030b81005c4501d0284014000c0941d40b0b0b0720850000c0076060701e07102e01491007842c00030420008280d2155010012080900058032500c0b07105144a5205281075580c001d079060030b903a041c007030485c5229200c4190300040100083d642060340c42403c0d02d84140111411 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 426804811 1250 426803561 426803603
    0xd0201020a0504030f1505190e03070f1403120103050114150f040506010912080304020405130b040b0402120f0f190201020c0910031401020a090e06010c120e0a06020703 74
    0xa1007201c040040c8042c001400403035050b4110b5115948203c100c004081c286225420941d00d0450f000c0195010700481c40f11155030b03e0181c118090110005140390924660300c0300ca00b601408805070072811081e032641203185c410001c64042ca580c001c03204040313603564030300203020740302d6200d0b11219131240d48007081d449420321003401c000300030040041c5800d01d03540003808000c3c0001828607041095210340021a03081c540751003810640034040701642ca03d024014001601e00103020704100008010551000c10700201c035007604142d0007483c20b911030b01c40d40009101e23054030420303441c2c40f40200360841104000000c0e542d0916400f141c2900c40300d00d1000c5c41d08000340c0700a080640581c0003403100b10468507103d030025502c40c0d44403200c10701490700c0e61a410314035101e900082001d41c0d400150841000d4200e0b00c184010540c0c180003008610b00000000c00380c2c9001c2030018161081041711080c064020030307605d0038000b8080c09511003039546440096031044144020340b1101c10b1f42d0746904030158 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 426806061 1250 426804811 426804817
    0x90e0a150b0a08151c05010b030d051e0304150c0c030f081e0621030315030a020a14120d0906030e2b050903100e150f2d01080109050d020102 62
    0x70070b58990f040590b9031444044803c030711400285500c24248403c456085403d0294008031500540002031095603150605242124881c461024441c083c45100c80405200c5112418900751040194690301c0e685060080141c09441c02e6078a5801d203407031070000036440700c4000c40c00c034003035078407804445480d60301500c03110401d860220f441e44407601114105c4041c0da080940001001e000c85e105814404919198000700d6025040650000006c3c441045040152828444400c801906403001c4540c00503003808120720400380311041624a6038203d0340d440c00d038400c2071452182550341c146190a0000c200d02d40d1b501400740828901a1050051800091005417190403044994a0310300304001c0e010980c009904030104101c810002114551000c2c8540d603170b0010703c4640460712071401170516007402d00403c01d40c07a40050301d40801c4100108510303455000000c4070144560350115081c41d03205c4246009140220220590000507070250542c4608030060040f0280c1e1101e41e4000700881c01d0348 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 426807311 1250 426806061 426806077
    0xc0d0e03032704050108011508070e0a050c0702101e030608250b16021206100b0d0603020301062606090601050907050d150314031201030b07090e0a150b 67
    0x544140300c00031180c0144405001e105096038001c0b031140c8003110006040e00d0b400d8101d88141e0351203000c24420303980300740e91410260800b00050248182000c00f00004100020045520039807a20041070039445600200c80d0080d8001e030100000c842c60344000b52090403000c401c1d020000083c07030341d140c0c2e80d07204e441500185c0d0609800350442d64581050548001c1e40b43c1d0b03400d281d610b00107000142451031080200404400c8440700160300180b40100114040e0098074140c8507003200c4204240607180720364190580c1d45403400da9443c0c02505848200a00c1e46400c001e40562910b1400704032400001c40c441103518200b2007003444030142e40800c070303110300303094072603007115031040005012615003619000c0e0b001a00e8600b80742800840840d84c0b05503164003000b0a640046800180103018880c4880c082c00340d030b844000e6281c0801c0ca090108003480502c0041e00071070f004000302c0c1c000d40c4a524540c004110801800c04242002c0c072200008005a002d50411004d906000180440540c02a03481c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 426808561 1250 426807311 426807313
    0x702040207060606121802040c021905010507021207030f081f060201050402040605150d02280c0c08060c0405120a0b04080c1501060f0f020c03070b1b070f18060b0409020c0d0e03 78
    0x1b407005039092201600b03080070050158042c2d520620200f00503880e15006550080b400890302d410030b0040a400e00c283d424044001c0d40d020410f800210b5048a42c003012580c45207022540c0e50b4a80214640c00d100c04100300c9400403c400340011307074944c15000540114001c40b41000031a0380c403020010230804a98402c40c0c11502403190798006200341e80030f0404040c0419500b81a01629440904038250000c1581d0102f0a2001c1d01400e10980070540381c00340c180c80008201c40e040c08064072056000e1446400d125441e00c0000c1018045c0500841d8041e40e40300f00c4081040c1090310342402a500440384807100c07486601103881c5031458040d0018101e5150b40c50b80d01080c5841041114042c0c2200d074003c09600c911806245180c4080212200420765284041c0d122450800300040b46280ca4000000c554080c41d4140f0072200d48881c080216055100d4201001211000c9030029091960050314800303030109000902010680061944a07100d400b40c0e4003284d0b10807000c1d01e40c104c160810a804d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 426809811 1250 426808561 426808601
    0x2101090911210601030c031a060a12030c05031803100506090a0f02121602010b040e071e0902070c03020a0506070b060f0f061306140f0d11070204020706060612 70
    0x3140c2810302488403150302105030b00c4029100805820310303180007030740112021203810b1000c005204542d5000307103a0300da41c00d02c00152820200000703880c0310900d0003040000b1800c50301241c1050701954400d03040c03e601000341c903100c0e03805940e82d94220750302c1c0b2342160082c0103203408054043d8140c4525449008010280407007034607400c04d1003005004039110320341c400d9420403440d8110b02800851a00c28200151001c10154082d440242900c01b841c00c01c40c002ca00b4100300d10801c0002240140656a04038030300e4584200c19840325040140c2035000031051440010f00005000a000594098074026030b00c2840b241d54480c02e001003845070070000b0f00380015880210f103861801250300010440020119107116941000180295100070200340352402050f80030840290004209680c0d0719400190f07e0070010320100f8201144140d05200c07400b0f544ea082044440324200042d03a4410350042c1c001c544505040ca40400203055502440c4045416001014810540c80c040c2c0715420b4407883c60440 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 426811061 1250 426809811 426809843
    0x308030f04023c03011a0d03170903090415080319030e010c080105030c01020c06070b0703180b0709050f030304030311010906020310171506010804020a090221010909 73
    0x1600040c050012030b0b01081c145200503800f2640c0d184104002d10480c128100b048400c02203445040154000318001d034104003117103004042640140c880003d0030748103c000c10380240b800721100151416484004800b000500250010010250908102c1520708001100456490021000b040d02c1080c03240c1c1d000700036148100084440384100c0d80310300d003804034a400b404a000e0b0b003500e603448010800285883d0041119250400501407486400c0c001792100e0501d01703006c50044c3c07180f01400781080b140d03c0d02140c006403003a40001d1016120400780c02983c076003031500c06950202602d0702400141441008a203524108201c0b07112004010f000307501d8241340d40d90554601c0c0c0d00a1443c0519540c0d1861a00450700c0e900003144507842c005107501380c607800d040ba40e0840c1110703508280c000781d01094204000c40500b8100782e07042202402c2020080c0d0302c0b440003d07a0441c10ba0808078416002080b107121092002c807001001a4007101d02c1c1c0d240340c0c0c82c0e100400c110350740314002420900d00000d44003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 426812311 1250 426811061 426811081
    0x70b0c0a021c030b0f0405010b0901080907090501030b041b051014040b0403060207030206070c0b0a0b030a060c0f0e010c0b010e09190302030d0b040b031c050d14100f030803 76
    0x201140c418010345807480310416042805000c1c1000321000710ba04d60500304003604d8070040081400c10222000c00c2076504140c0c000c5518007034400024140112280403a40919040021000501d1100018810f540e124a0321400e01c076401d680c100c03148600400c0071220300600c03441e80026100060b11800904041c04012034109020510308548014104000f0442204040092018501504000d80c4c1c0c0c09203440c000b464a00f00904080800500d00512070009500304c3d9170f56003001401c03201151420709400001d0a00f68000c80041030685028140d05541c5d0b00079035030706200c90700780e241c0c210400e041c070005454511903c24014403140154005100215800300c04581015038141101e0211210700d0516a09048000c0140d0143e88007180070b642c41c601034000c40500c00004c0da410701540748600007107940c07a00224000074111741e01450f07c001207407140e82540e407980e030626803c0c01620341032050540000c100740c80d500f003402c070b142c040491090a40003440007140d9100c22414036664a00c0e00344 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 426813561 1250 426812311 426812317
    0x905090607021b0127050108070206010e07050702060d1505030c060903100e0703050d02010f05151c030509061b010f09020112051509040602031029031803191202070b0c 74
    0x864140081c114900d03030b8072001411a8003e55040240844805c0d00340300014101c001d00520540465019800510044101c8a071441d00311409003800354a41d0f041d40300080c282d01403c05100004c0f850a003004402c100d04581501c12035806609840f2858002814000188203640d07030641c16501804503201030480980c00100c9810610050380d080c03588075910141407002d030351080c0b40180e46524105d4503240d0700b032150503048500044d02078041514040231075400ca070265848110720414000c1c40d818540580111440d00c81c001f80401e50b6180c156411100c105138003042c0000c6507280c240c1c020b194a42900c908480c10360140c6030300088140c002c0201014081c0107050140c514050440d074001903c44400744d50041d4410040940c03a8503042420b800f20904642c46090144141c400d05200404c0310100c0c64000076011400c90b07a2691a01100c0120440c204050b841600c000550300c4024200c108080e80c58903002d0755034020021601c002501603000e42940684035a50080218458002c0d850003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 426814811 1250 426813561 426813613
    0xd06060f0903030e1c08120a1a10030b12150903070c030f031b0609110f0a06031d1207021e151602030a050105070f0801181d03040f090509060702 64
    0x1090561840c600d402d905e50010003c4e00304c070140c0300882c0303001a0b4000f0900044d0301c04ca0800d002c000311410000880231041c0100720345c07030188030110540740c00360780b00c0d8024484503000a0070021607064003021960780d8006071082075804890719001724169010100444601503044250301c070100d4255203603130383d0155008400310b0503c6180e06084018980c1150b41030300941c064840001c01c001d15046c00038007511000c40080c4119202c3c1c0707400507682c0c0d072514200181c0b03032903250014030382001000ea0b414030400720041d01d0707662251030309911070b604049004082c1240700b0388001c21085410120658041d80c580c4c00d0a42c002d0100d48203a5280c04000041c01c43c0c80e04403480d81009141507004a41450420b00007034071641d44400400000079000344002c0c4114405180c00486c0d0b40c54188000509040c0703c040301a00d81e00d400c0c068901d1103018403050221102441501d9031240d40e000f1145040d4001d20800510b1810301c80059045880440c546210742041d4019081c40300308131841c60025660100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 426816061 1250 426814811 426814819
    0x1110c0708070e310615080105040b0408090a0506070f060606110a0308060f090f0402040c14040512030405120d09050a0e0601030c090b0d1d010b1e0d14030d06060f0903030e 76
    0x201020344c0c60001c0303990310f0302180a8000080e810f0384030b8501c3c0c900d400484d00171401c80c0c0c7c10072050100003403400c810141e00c107070085985170b220000400000c0e0402c0c05940101d60041000c03c5100501c04040c2ea4413464034401e440801c03805907203050941d04002d00d060000c816420811070b00340824054110f8035400030004000074010700c04800015907542042e9003040a54034403004010460401740b260200c0c00c122800c1201c5900b0721280310b218144228001c43e4054803250100c0000c0c18010800c1d24042c0000801ca00c10390a14003036402e54031085800300d8000142c0c6610001b0b494103050301850160707001001c99184954a0350019005401d1450b441c0342004003145d000034aa401600240080d6000c0c18000304500e1070500015903401520b10040350f5036403400026445643c0c4a1402c18507905000c1c8841001180706c500040f054241e003840600394060b03007a250400010044010042702003c00401c100f030347e4680e0030881726003942441d60380228a8102301840880d000380190700c00c2410041c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 426817311 1250 426816061 426816121
    0xf031906120b0a06052e1e0c030201050105400903080a06050f0904080c0708030a0e0103050619180e070e07110a0302031c0204051504170f0d05031801110c0708070e 72
    0x98821011f807803101c45500c0010880003c000c100355080c00b03000c0c014241202c601080ca0480301c00b121521034180c4001000041e14080260200414001a0441c5045141c100302014460501403c5040c0c21100a50480c0c507103d80840c0034941103c12a0203020041c010100940e60b541d21068203030f001078000f0240b84601007002032600745c1000103184014a035074584182002c98000035040e144081d1600d44990142c0964101042c0d0110f154021a07001140307030810041c4506401001b40750000e071080d601e0041042c00703e034240703041b00750300d0003076400c0d40d00c0002c07a490458103581c54072080c01c00100144c00c200843e555100c04c8480901e0322005003a4014503103941c450000700c41402100c005400c8500100d010070060074200d010b80d60342030444000d80034050440c42030315204c8800410140a220011000c1a040c100701d03c1b040c40d41c810400000c04c094005c1d260780000a401124032142e44d480381420100d80070300d0110f1007400700c41c107030b214400300f546030740c0e800140080321a0310b0f0404ea11142 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 426818561 1250 426817311 426817337
    0x50604090b0702010f0b150708070c03210f050702011d01021005041101140c030304121412160f14160512070c06050f031906120b0a06052e 61
    0x2500703805025441940001961046045000e4117481c2c483d8070042c4140301c00104240d140038034a007200e10140d440002281c0e121054506101408425000038040810680c2c0c82482081c03154504ca8000c400e07501ca03002c02d04d20500e0115020f10600d00d00074000f5a0030101ca109070a00014070072124541401900d01c80f140c07414024044034400c68080e940b0640c2c80802031142e507003107064080c01961710361415290200b00c0480a07540d21025100400c0c4043d404000c4400500c10400c0c28213240f0dd900380f840d40c5040b0b880d480c01c2c00d49001d440000d907a4040206d0b5030070303c0c0d0081564410501d207a4442120280859020003203581042e485200d00312030515071380b40080c1c0c081c0005100501080c2489440b000e03a030074002000304c0b080e040001401810040d4150100741c071001e590788800c101c0215110200700e181c42c42c0140c4060b0f8072080460040f080704a08100340036034528400c28201c401049042e6503102000480c4055002d00c000c541005e84031304c00d50202c0682c60700b070000411f0804040301f4500b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 426819811 1250 426818561 426818573
    0x160503090607052506211b030203060415050a0303030905010209062701020106030b061207031b0501080907031205130e07050318070b031f0801050106050417010606020c0405060409 79
    0x31881214a501301c1511451890b00c0006904805260344010704c1c0c140b420001c024120b4a103528085901000e4042503404805032504291040390703031081d20020502011101501940080d1030292180741044825885440a04ca16004481c0020032450b400bd195407011340c01407003110429030b117a5400b00007030000398031064001c0c0283c09110140160040c0b00c02810210803011080c21411039040400400208501d0307500c3c0c1703400030303802c446408a510f146160701c2e2405140741c0c002000c2e820a141e00306c0c0d1840380426048105d031402e886095030f070b42d144072086444800c80e00008141c0c9207041c100e2840d45110f00060b140d982c03d9000c0b410348a5844d0710b008481110100e58400c005200081000003221451290309003903a600b034010800141484428109400001d0144082182c001005006036024124040050802d803008106558403200000c0080c0d2050041a02c00e800c0b100d604080c88205203e003034115446036001d02004c50000080101424020348903661280d1118010000301d14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 426821061 1250 426819811 426819817
    0x1903050405090c0714060c030a0b13050a02040f300305160602030406230601050d1e1b170123120607030606021b04020d18030314010b07081605030906 66
    0x4000110507210700c00ea00d80809001c192505c0c880c0f913174114006004581c0380c64815690442030b441c0004c198206e44002007418284810341030584181080240810354200f580100184c0c1e01d04051030394003580383c4440d42070042c0c142109403c1c0814a04426510100100a61040500c6450807520b00107402c8400c11001a440b40140e4106500006101c1002424840c502135030141c40c00c2c002990302880c0003042010340080805050040000b0041500026070b130100c9692502c041024840f014404049030082c02003c5060400c02d08a01e0700c4260680030326010129259007680d6408141e091206e40040c10824503a420500072040d00007a42c2a9a505004501c40e140d440c0201503e1404110040c02c4d62a04d80c014000c2d5000403071204c0c080d002c0c11106c56000c003000d55015076548650700d182c000078a01c07100c0780071804a03d240428100741c0c0c507410000400c019940c1b401401d03601c81140e00b9182c400e03104001d25a00c07040203c0000c1c0b69030514921003140c010000e5a003486c40a5011403407030b40c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 426822311 1250 426821061 426821071
    0x306020904060f03120221090409110a031113200a0309080c030a1d0a0e09190f0b0708060616020109080102040b04170102030402010e06031803210f040302190305040509 74
    0x3040c00710b6080c841741d504200d940000800800540d104214400c4070203214400d25412034000e40d11101c0345814414000042c0b0b41101c0040c24950b1800e1303030390511061000030391159511400d8200700106134040c0d14066542100d880141450007800c04100c1510710342e1000c014002415110907100c008210080058800038900402659841003101d2008050100c440c5402c124010012031107007080e20f8402c000415220502c80f1540705440301060315141842c006400000750700080350311000c110313000601c2d42405104203144c1c04d65880340c15003030301c0008088407829000842409808804e161084820390180d0041c10b003c940b441d11031039003509a1340b042c2c00c06139016100150800c2034201201c080d000342441c0c20021421810903a00081000c1d0f54201d22921a841c003001140c45120480c0f012120501d0f00313400c4907601d120b030800c10f0b00000341e10740c80c06250118080008803500c583c00b04542c0315540c10340c00b420300501100c0324503d406103e510117a040100030710001c507c07500e5040100b0300034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 426823561 1250 426822311 426822323
    0x4050915060a09090c030911060f04080604063e0702010302070b0906070215271603050a0b07030c020c0927012708070204020f16060b1009030c0306020904060f03 71
    0xa418242590162601079038620200342c548192640450340b0954007423643c000486610390780b1524001e101003603018a400802003801110180700800c009035200c10300311458082045082503172100100c0c6a2400c212001d4031003040942c0416040c08110010a80c01e481414010306007022074541903041ca2080f10881050783c40740092140403a0100f095a90b05c52072489010058a08048014108032009119003151401c0340d4011030100d0042c01094400d1210b4039101400742d580b410480c3c1e481d01001c4050f2007050114010410340da1007409194200312241d00100003d541c04414400f01440c01400c0301e0351410703040b0170016000007140301c140c0b0b035002c820000304411072501d02d000303503060725481301c1404141544110780c001489207065070100c1c0d404030b0340146c5400c0c4c820114030303d500c142030014200852800c0c51804001c000d86c05000c840308282c07112100807826020585840c1d4813070001412007080d8070000c07c00506550001c2062041c09000411115503d890711401003401c1d800890318 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 426824811 1250 426823561 426823577
    0xa03020f0318070b210408071401052203020a030f030f24090b010206070e04090b0703020c070f1a1605030c07031202031c020304020f0a080a0501050a090804050915060a 74
    0x18004015003800340881c4c81c0c00500d02800c4030401071400c510050144040d219a100080500c444a4143d46040340c220200d0300001035810040e9000b000101e07410703c044182c1c0d8101d421000ca80c031607100d480c540d01d50002c1281c03851316181501e10080400d141010503449050b488003281680c0200d148020f107082c13030f200702458407180d080c50180103130300040502494a0b400c03001030781e80040c09940108060401c90107002c10743d404140946002d03100940840c7c800000e0048550349540280242c0b011482030317400043c1c0382c41b0345101031501c40c421440001121b0817013910070076001004000101003540c0070f1215107025900ca50440d00807204004058010704001c1040c881c641200b050034681034400340d0302d0f100e110b00c210806400ea012403124a59400f10015045489010041c0139002000303103000500ca689884890b5250018a03084840f9420400401c012400074054103552030750050034503040c04c0c103081c184206100c005003500044042110440c10315100c1c0e100070190348105940b01c800d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 426826061 1250 426824811 426824851
    0x3061104050f03030a0207030b07091a03061c080a030b040204030b1305071d040f03120e0708010c05250507150810050d0203060a0203060f0315070e06030c0f0a03020f03 74
    0x1102d1004801654001d400800c01544800c0e8085185010f882c1d10200c070703010036100d0740405c5948101540080801401c032014441000c0181e502031882807038201c40000350385400ba1441070503030b110044001d002c0b400a100d0016818040d03044140030000160005003403542e1794a495507511415512100e0030030241011609001040c81107030041c22801388511039200c0b0420014440c90310041c005410f45076140c1c000e40403d40308000002c01300e04181000e01141c20300314150780d110080b40c030650300517601c2c14551506090041007607407031b2122501c80606100c5104010b11401c2c500200c022900c034001c0a03808250f2900d11002c2507051310141d90741c4113551414001c03501c08007510350403480c0300390750349107161006903400a0210760104d48070002589035152200030654482141c0111a80b41c0280a9041d090b0070100d044548140800d80d207500c0b0400e50042808110b110607622401851410001f0b0440d0705401c00c001c0000820318500185000d030300c0b080c00034003600261004850180d903010100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 426827311 1250 426826061 426826069
    0x11a070203030313031704150b0402072009070e01020c0f010311040b0705060153060406050a02090a030809030327030f0f0c011b0c0308030a05160c02010c06060306110405 75
    0xc1083c10888032104a87c24545c4500c83c1110f40707480f2001a8507164006610252601c1c0c041e124040e0b4080c804240502000b0a2680d03810640d40480380202c0d084030000707640600c50240145e20500c180c021744982180c4905104081c1e0604065034140350f03d4403208000804018010b0000700481c410280d1900c6240c904503040210603403108161004004240101c0078043c4410951a0b4040340f1450410b8180b015644001000e0040b4460744242645050325400020486a10070f0b4803c8034100015680e20184804034001d8100c1203401c0304105c9030a1002696020003012400030050851b030078001d00105d041c0c5600101c150701500d0882d540081102030504100480c4070750ba00c50045c14110030403080c0a940c5100e110b0803d4100031000c2c030401c1d4811a240d142044682d000f80124506a4507400d220340503070b106a6403241c140d4034260000b405442150628503683c1c6540e0380c1c40e40c00c150316400458000d80d11950982c0c0d56560703207038000300080c40b600c101468000c90050340c0c1d4840b07141c50200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 426828561 1250 426827311 426827327
    0x607020d080a050a23040e090a06061403010605040c080f09010b0904080a030b040c0e04090f0b0709032001210e0a1b0504020304020a0608071106070c0c1508011a07020303031303 78
    0x1e03001da543d0004800300c0b14103981c01586c040e41c41c0d07004070041c80da4804a5031483c0051504d005050a85441000700301e8000810003400b100c1c000380c00030b02c845642c45c070a0000b101d43d03074220b03400080c0f00b0070049001100021002d0360005c4011001080c104907100001d0044002034604035030500c0c2c0010400038050300360061807041d8100311001c010f225040c14010301040500b0784071920880da00ca40000030001e49544421082d90030a032170b50120320380904c1c007610889880c0030640d118089604100030a00000301c03946400b02069403008000100180d022200200160124502c680c50b5004444407140c2080f500c502035000381e551200b2403215462100d88940d1680003240a24010403c00c400340c6c40d8080500101c1340f15180c201400d96810004440c890722000c082c29103402210140400581e0007400b00c110940201c1c0341d40781403996140001c0117a501449000041040d9000410404104000c11444401e840140340e00d02071060340020308660044661809100d104e4550100b895888281 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 426829811 1250 426828561 426828587
    0x325050a060e030a03050c0c0a2406030b04050601050d1a10180c1806140a031e02130b0c1c09080f0304090e0f03070807060b04020c011b1b020607020d080a050a 70
    0xe6223191910354510705407140300c0c0d01c50181141c40c032a000d04c181c01c03408030208a18210320f02410055075403207250040c079031442901d00360f602d449a400041000c1c41c094013000302d0540d010086100c0381d45e2340b91060b40c415500820324082a1149200000c1504062803406050108688005000e0001d094090403000e0003882840107081c2514080c0009071f0840c2c29106c045d0802002d503a25404030304000c03006040e00c1d240c85180744984143c030f401d50301160340160601d00b500e2810a52426160021341d08140039400180c100765001d100e62011416240d50070030440841850540c0c607050702c0b84d508602d03100102d801e078003003580002010800400f6521451500070f002c400038021400c032000549a403070040c2540540003000c000750340801c0242a0b0f101e1940454041c02c25520340d180042c110340200400c183da61000015110500362280c031a5550304440c81404400c1e080c04251134003888402c1c0c10154089801441c44c2c40c2d118040346e00380002d000d1800e06c0d99615030759003004202c014800442180 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 426831061 1250 426829811 426829831
    0x120a02190602030d0f151e0801090b06060a020a0501050c0405030f032a07050301060e06011706210c0406080601080f1c0c1110030b120325050a060e030a0305 69
    0x40c400c0750342c00320866490080e82d90010500750100c0c1e28500091010a548808550703070040005021688414901e0106804c0034100c61482c1c1d03100c035002d0a03141d00880c01051403005800007040b43c80d003840900464012841200c2560105035507581c211441540d41e2910840302081c1003100e03203030400040c02a101e07403201441c1060a03021921030056908071440c14040000c5030384081c400c404002032001080300500a12045660b80b00070300380c0100540710781c0d0000b602e0410258082000d802014040c140191a400c440482180e640454104005080c0070b14010342d1107007141d0782d54034011200035060f000701802603549006079083c03501c02c481c8000c102e9a0031040c0b0108220304060482440031400d414002e0043c0460b280549034041d40e2050260f01103c4c126105420aa05500c6810890700036954854071400d80c480890ba01c2c001e00298500b400315a80b41c00da495074424407800410361060040b03408200305d50351484241c4440e04940c0c405688007064000d20551305006442d0007400340a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 426832311 1250 426831061 426831109
    0x20d030e131e0207050c040b010c0506010605030a060b0a140f070804032d0503030f040c09150509090318040b041103070309060b120c31021e0408060a0b0609120a02 72
    0x10345c0300e0f5220340018104a201d107544141030304082e4080c0300350308440e5510000f078600350341e101c9001070074a41040d00d0348001203103800804038021080d44121100940309480e081c0782c0640744502401e442d80122100002d0340d40a01051001844940161000d584143c3d000094030420941c25550034110b42c903e5800045c01011880100da004001c80b80c0020b0a04524550360f07a850030b09400c841240d602283d0650b10b02a18000c030401070420326011344408950001007921401c048640d00e010710a400f5420f480794079251300a902d89544140c81c008009040130030360518225130140550012520400402d49500c845020003540e4410a404500e007100e45a225490010055950303030f441450f10741c007a2030803204140803c140110340f1401181c68a44512501540450000181d0400282590341c134254039030f800985000d80e0701b501c0c15550164002c115a50352140c50501800681c0009030700450104070f96117072a11010b0304442010041c0e00100404501d6106200c480f01d00b140840190380d1042c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 426833561 1250 426832311 426832313
    0x110901030b010e06010504180c201b0a0909030c0b0106140315010c06051e0a0c0e2101060308071a0c1812060403110f010c0507020d030e131e0207 64
    0x20303000781419556014030b207890381e5581000580b802d10403500301e040d4100c0750420000108206412103d42eaa0066668070803d481858030840788a440c4071584443d600541d017041c074904110729401300e164800500b00b1350a80d580b400b42000301ca801c6441640021514002d54040c409801d0240d401030503140750864040c0f1101d40541e8103400003a2041720175440d4250021b039981c1c850380002c803d16411420410203400c021400b62410000f001e1444c4022207580e000589d03000322445400c0b40141075440300c402d08208402000300001c47c040e42c0c21002c001c4500e114013850401d01c512009140701e20301080ea120b0842c02c000744c480d140018a0350b0304011400410204410100c26a41c80780d51102080201c0064503000030314904038030800710000c0c89201c0400c011306a001c40c507a50040041820754100c0d14003c82c006007a40e100101e070101066040080754014280611850030aa010b85400300341885c4060000d2035900300f802c012200c3c0c0713480d031030800c0303072a0110028503c5a04100c10f0861822580d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 426834811 1250 426833561 426833573
    0x90515010b07171e090406050906242b0506030a02130b010302120c04150f0f0f12140a0606050405030c040b03010b09240405190c0311040f0311090103 66
    0x2801c00014001000c0d00042940f040d5800250744492201181d43c1c1040c07004680d160b0a99042009071502c510304003007000841342040b640c0c542c020040646901c5042e249005020344504003400d9101c0d01c46010000d100c0c0307410444240c07481041100b6090080c00d580b50244406581019000f0f900c80d4001762802c400580e42c00c2078101c1480306001010405480080050b0000d01a4140610b01d01401608000f5800c2c902c2c8001c03c00e84814411500c050031314144119504085c8140c0c11010a5418085411050081038460004216487c1000c2d07655486059003050310421048052210b0218090001c21768040c02600050281841c0c91802c003860b000000360b0302c0b07035240d00703940c0600d9480c0c01c961240d85003900702c0c110480d0098070001031070901e0a04040051910508a103041d640311441d540c0d81d05c1c0070b0044074010075100145a00100c48168034400405e60541808140742d6118041384041b174203074001d0f000800d0350800308602c1518504000c24000414a4050312900c1000300510010f61 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 426836061 1250 426834811 426834817
    0x2160e0708190617010902030607050903030304060b19290a0e1c0203030a0f030b0603011a0d0e06010f05090a021912020403060609091e0320120c01090515010b 70
    0x5046002c00b40785021440707000f0001c2d5000b07150b0038107590340d0000d1000415001141c92074800c0e01202c0030f580d204601210280130390b004655041d042000800c000c102d0b50b40003038845200040084a8407031700b07160102040c0e171095100101984041c10300624022000d244404907500c6800020716040700150020403003214003008a118450002900361500070529458251682c068202c99950303400c0200a0001100040c4120009050000040c250b0074401d003560304130b41c140031400038406d1030b001c001a8250089041c44400581d50b0600490604007048524024103400b143d0000483c100000e22000c00740c000c000c10035044c0100001c1c00c20800d40f08021030100454900050f00d01e0765540c2070301c040c1c070550f48040c2180d402c0c01c1c400306080103c2d501c03903035140d8070070b88600000c0200140c000c5400b0740032142c05000700e090503005001624516280f89003c041b500c0654030b801c0c142c0340040d4007d40044060000030b039901d030380041c01c001c13040165101421315003c2c070080341d600d060340080707440c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 426837311 1250 426836061 426836071
    0x10b0f010c0f0204060f1703130303050703110a120e040b0a060e0a0b1c060504090f02090c0c0316030906090b03040f06020f18030709150e09030403050d02160e0708 72
    0x11a9030300c480c01d00c01039084000c00d40b83d0003441800805c2d5108500206680c840c0a01441100b0420044081c00400001c8a001e0f101000030150710515586081c4d500781c0000c0c00650612008103134250020b40280810513142d403042c080444000402500245520000d4a40a00881c50076a11000c541d640303008000840b52245020354841e031800001c51440340742c640c0041d488030004030384501403584514113004081c1c41241e0811131599100d0410040d94600500945507020341da03442c03405400d04810b420352054411014038a4840d003000c1c2c40c0e19507480211400000104044035100305030388a0700603001411245001880282002303003448240c8800751000700031061600450003044499010740d01d03030003d0000302036121111183c0c07540d60903e18405143c840d0081800c08070b842c01140c0f0030b078a81d01090032281c0c51658202403003512140d002601c5040e061205000010020b4410484214603040582c00303804120b03501d150f00000b01c0041c0d0010115070308020100911294004070440d409 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 426838561 1250 426837311 426837317
    0x50a03020a051c0503070f021005040b03060910082406030d140304020a170f120f0906130504020f270d02060a2a030206010e1b0d0216150e010b0f01 65
    0x1840f010f403a02e40d4400d81a0718014480d02021448005000306030a650b00042c2c000d031941822442d9880c3e0440c1c5510580c06441c0407201c050010030740c43c0c1019001030f980010300b08610100c854442e0700369840c05114111124003540042d401d0703201440c1181c0c909420400540003843c21540654003c2e0103450f603c190030044c540d010001030159610303014920001c102c01c603d07016014400910840c2c9800c0c2010062459128041c2c010111450100448898003d04080d550800724444108040c662014004050058980001051940e00c0c1d00c010045003d0485006548000700800c18900c119405d21281d00782c4178007101c000c1140c56000003a101241c1c1190a250b0350402c825041ea118510644203000503241d9025416091708910200d4604ca4040c0d001c6501c0c0f41ea0720001c4211940c400c5864010302d4010205102c03590005e100a4802c0c0d0100303502c0981400f00241c42c0030010325030340400303540b1405000c01003a5000e0040c840d41c204520140004d001a1140001040320014024029410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 426839811 1250 426838561 426838579
    0x405090c09060a05041e03051c1e08180304080a0204111308010203070221160503042310020a210306170610060801080703030f091e0e01050a03020a05 66
    0x40c012400c0860740c585800626698a508100b14000e02e00e400034001d03a1150b030480c00100101020342c00314581120781c403174000c10f245050303c65206000a0709070110028000d008070303106003801c3c0b42568108400030741e9944c2c2240d0303c1c00101c42d41110740c000d003084010740c00800c014030842c100442c19162907a010f4070041102800d1b02a4402a0301c0781c501c50441501515402044c19403041d00114003070707190f5500302d81540142084401c1c9661080c1c5803001c0545040216841c1c50260280701007002d070007502507a007003603070340d02040c189544100910302c1c1480b81410807085c0d600c0c0000e03074001e020031240300800e1440b909640c4c10480c0c4016142041c070940c50f030fa030301d201c0c51407098014401404041560045040c0e01700c000c25910f0380e007500d1654010700c002c00c020501c03921070701c1c0c0c99040701d00e200020150589191030039100940c040c92141c0c00c000159802083c1c3d618601180c030703241d00c46002c090005c18a024000101d04206030009446807003086c104201507666034000209880c0100c400d140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 426841061 1250 426839811 426839821
    0x30112020315091b0d0b040f0201030b0a0e0a0c1b0f12051204020d08090d0308060907030b09180a02090408070b06040b01020d050c0a170c0607030902101d120c1c0503040509 76
    0xe2840c1105c0710080c280d40c80d840030801001401550f25002503c00c4c1c809014501c5400e0401c00c46060341c1c0900030201003448005030b80488242c1001c44540d100341088128108141581c00c446820b550060f10101d50300c402140030442c000041ca51070b9209440d09d1401d2120001d100c200006001c2e1010f172003020b5900c00310080c80354000484015010081071012000c1c030341e00d006015100100d602d40c0c03080b1034035400198254000c0c0200d10320900300412424159a41098840042000d9292182544211212800140c031800c1c4840e00450150039829100e01c40e51900c5442d42e4001800c0d039000740e04150780c01015980000c2d0000695181d800c145845c0c100e403000181c5800a800b8018184031790b040907429946000c80028500410400d091720441c3c1c0e180031080e4180c52007128000c0d000f500445841e100c103845409918410360403805190041801300300015412001003400c0d2100d13401c5100113000503d03015107103035511460781001c000f00d1000c40d22900d85a01a510500f409035001e800020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 426842311 1250 426841061 426841069
    0x210201060f0b1c0203090f160e27030a030515010908120a11010207081309060b030114060c060712140c0f0a051603121428020c03030112020315091b 65
    0x424840b802c4804541741d24203266415660082007407010343d140a00b416101c1d60496100109068440d4400d440c1010b0300ca03400e524075181c1c03030300c8601c07901010840c1607260051824030051851030b11603a0045100e00f4403104040b00d014034417660f00e06001500c0130070482c044010480140004404d03100d66118004c000066a5200f5091407c10b40c40d440011031b0400c1209410260000610448444403c0394807004500202c1d1000e00408158410038001003002d045803004001083d0006800e45060504d000c6510340b404e030b0103450810114504004d0850840600d00c0780c102080d24088035a00c00d4203001e02c4024551155420b044a04070703001898100482c050000c58074030b900b500d00e48080303201d81402d0042081b41070700311206c0d40e2818011440d0000a2941b0343c0c41c084c00c0440750054a6819002440d903035007003007810300d912103a028081c0008480040c4043c5000304680269444100040d00c1014284440705070754005c59444c010602c101400e0020b11250103050360b44c0c1070001380700076400207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 426843561 1250 426842311 426842347
    0x12150c05090a0e0a050106091809140a0605180a1a0a0e100c031503031b020f060c010b0a06050f031b19020c0909010c0203071104060504020304210201060f0b 69
    0x8680190380042c0008400e152106194071401d05003004106598813540225607041c00742c403e66004554840000300c600c88150300103802140300e002990905032015049500b0200d03c800306440c0c0c1c41e80c5100704a450441c081e0140d000340034180150117615019603498800f060b03540310507079409001d100040c000000540c0324240c1d4042c041c044414400102c028000a0582c0f200d81000280c10003642051300842c0402031801d49a2503115035407900188120001041c82280741a640103111034982d031400d448050007030242d0000b807000480c2d00620101403207000e800e640d100350200001005070000300d00341c03107044c0d82d042008224000b000d4200107200c603c403409080c44408200914916890039641c0000b170300507401205403544040e40d80d50b04038640c00c81d8800c10140c00560003c000202c0040c4d00b10344441e00147d0010000640a500c80d8046000ca8204490442d0032400d1140800d4143d00c0101005840d8035080c8028886181000d191981303441d80e500c02c00c0b000745008100000c1d0040e5130f10b50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 426844811 1250 426843561 426843577
    0xa02072601110c0114070f03020a030b04020d020406030e12121b0f1803070609140a09090f021302070f0b06040b040507020d090501030e150606120106030902090112150c05 75
    0x7441050107442e5120707110340c040554010290320345640d107402c0c10301a2281c1c500c1462039031100d10302080310500a070081e41c007a0200e1410075aa0302c00165007680c076440a0140b03140c8242c0c00585031070618001070201d513090310401c0c1c03440d40300300d4449032182041000c07190000624001d4001a454140e140d82e801055105581182c480208040790400c2180002e424110618141490008440743c20b041d01c40e0b800c0e01807040010501001404241459548400310b6000038001c503143c1d6035580c0c031400880e02c1e2690111091001d000c01d060543c6420394403a0100344813094218903000055a030481c00030410240200004030070700001e1820750350355020901189001e4000d026030f14003000d001b91119032040345800850342c0d03988007160a503c04d10540968101340c00040030300d8410000001e40b4003400130311b116807004041244449a01c01e030303480c29000f0300b1251004610481a44108012090140c0050312507640d54126940400c8111007212200000000001100d000804040f0303154854448 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 426846061 1250 426844811 426844813
    0x90307030507030b06100806030c040b0a080f030a020c06040605180a0e180d030e10050c040f1508060402120415020906121e040b07080601021f0e0f01020a020726 71
    0x4000801d105104242910860080f961015a01c6c2061010f031440343c030540311140c0652200da040c02041c20300c1c1d8020302d007009008008070320150340c50181030300d4815512440030040d080400c0c0e401c00a03404200c03900c0511130441c2c0e15400c0074100341000f025405105100340c08030b8082841d141c06500c0da903100d1005005c0701a070400305898601c410052500003407c09520511440b1801c0d560144a841002411151003016000c5e054900250f1400341c0303805400d84044040c10400021a0080807900070028101100c0c80c105c0741030701140c080e1510100800c10342c0200e00401028800c10708031158240c1c0309500c003001a500003490681400280201c1d1109a00007070001040d003801090b04441078801c03841c1d81c1d20390f000802080c100c2c04451500340d030020580c090040118094a004400c4241d1042c0c061040311580c0f03280020384200e021104075042400340c2d40d07005020080b9800d02c4142d0f0000c20200095140540d030800003981c07400b29115010704080180c015500d402c3c5825041c0d41c0034000b0380 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 426847311 1250 426846061 426846073
    0x3190519050c060609011206111902060108010c0804020d0b07272108070807060e0321100f27090b061c0308220b040c091406030a0204020903070305 65
    0x304000d49141d0101001100620404000505501c0d01480a5041e1407e03030002d0b08140031682d852001400500320180000001808011210401c05943c50911820b540c020811545003000c0c0a08540002030fa50080241d400104000f42e2105061840d1580e4042c221103059070701c00b40200e444c401c01c401c0307520148006070599900b640342c403903003502503a40e2048400c60700b190105038a841e0780405540105081000c0c030518010864510282c0441d60003003001103030b0011074000b850f055900a403e500c0c0c0c0ca842121a15201c001380f80d007110340c01844030966001060820701c9a03240d400c10b5100701504a0010b14a4090302241c4600780071411241a07410b0041980e949422a01c110f0101c1d4040c0c000c040c10f0850780851400030901141168164580c590191910301e002eaa0301c1e100d0002080200b01d81d64a4400042c40d844120361146000f8010042d685050038400c03010751301190900d070750548074042130001560380880d100e000a6412a40140c0c2d8a044202003418510140d001402d02e000d90 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 426848561 1250 426847311 426847357
    0x304050318010c1719091d040c170d090b1305091513050702120f0406050d0902060705060103120c0309050904022b020102010c110c0f03120403060b0a06020f031905 72
    0x21074050843c550b10781080c280e8800017000110b0321001c080c4101c800201501d5036607610b299516503007540007409020360810407900d0751410303422001052000b088903484010a40ca059900035140780151030701c00c450320b1030110500d0008494600c10700070b0764440c182d0000482c40700c002c4800d4445046002400c0e0000e00440d07804148000c1c801120a180036029020034400d50010240403902c0e50f980f403c607070070f06003070800340c4c12030b1103070000b0300514812542c0e012040056030314070740a4914580318a006150542c114a03012a540000c50342180038005411001c600080d040031119041d16415030391000380c2d680300c0c00010751390301c20003203448a90315140d601900c4d00090560341205060003a0001d2048400144045608110b141130252458106850380c200d0361a112616042c4504001d0171140500c0c0318407804200c50b40103a00813140d107a40d0b20384c0c203070300d504061041e000184480c3c00503080341419074040035203d104010a200f00821848031140302140580c0948078020600c08028100380c00c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 426849811 1250 426848561 426848603
    0x605390f150105010c02010507060e072102010f0504050d020d06090623061009090c140d020a09080f030f0304030203071704031406060a0b091518090109020304050318010c 75
    0x1071038010341c141c04101030000c500c550064200700c070450740c183d413400d1421109031035100051403050340748a1540111200000d0302ea0342042441a103001c80d20250105001905c00900022010340c0c152040c084203200400540d035407c1790320124640c040c0c920840700307034661810740c000b404440300040066180c80c03028036548100d150301546c54a02803015043c00d46a03202000000da10712003000c0c00044028005102c1102c2c5a000750070103945a040c260510414210340505030703045411a8010180c4c040394031460302d41e1092444004004040203000405040010701c0c4c0c59208214081c101c551000001c5400c0501c200229000d0f1504081d01080040307202440c511607a00c50310064507042c61124401b219040301040d04ca00a0300002c000704c4e0050b1070031510f5402904406042c50b0f200302a000008a00f0b0f0700300c40144104036600f850b059040328502c0c00c0120601c0180c010301c0a440c41842000b001030000421245903001c140019803880b99100c0048070f14140e0308800034841d103451032440c0c04200c030b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 426851061 1250 426849811 426849823
    0xc10140403020f0a0203031813090b09070f1a030612013210060e04090b01081c11030a120b0418060b030f0a0f03030b09010b090a0605390f 61
    0x1c4207609444100b181100c02c1c40d5207441d0440080e6054104200301254080c510b180184010000b030222580c26106120f00320460300b0000d41600d100c0c45113010040c40750300501c4410003818400b9420350301a4100a12901d0441e000610b004543c08000003240042d03503900e50114644440c0c0c1d00034800641500300f00c0311240c451400401b801301102070340c4103203961600300e26880780d101517404040507440c0060071a01c490b04581c04540240e9200c043c00003052426442c14080c2142c803005142310301d8119810049007503040803d00400c0b807030882c08000c40d4404400c4803420304041ca050007100b011518050004c00d620708034a5809481c2125086400c04c0c1481c071070f201da0740100810410301c42d0300c505244c3c0307600f6410550241908558a0000040e1040020045850003850001054107045001c03807103c0b4400e800c282d180445c04a080c8a0030302c4e04807a035501600852901c28181101c0d8130a0224500c4801c481c044c3d10301c4030302d1410300802e90680405010040b4001103540c800d6403a415103803a64 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 426852311 1250 426851061 426851063
    0x1a1b03070c09270203060a0b04020c0a03260103080d1505060304230c01121107140a1b050f1002010b04062304020a0503060d03090f09050f09210c101404 67
    0x4010070500f101c0c44425007010391000d030040c026000c581d80f02201d0100400d031703290315150b00c01d42c00d01c40307580d070000300b00019408203200382c0f00c0015800700000c20f0401c0e110868a0f11540344850401800002c0340d4005580102e4800c0002003654090300d0103410400d8a19042190414000f0080105124001e00c2130040c0ba0406800c21806010041e035090f00d850281000d03d0210740c51340d411050094190781316411032941e100140e410403505a4990303c1c05614a40c104006074040340c10201030105100f201e00e00e5140d0785140e003a03514545000f04002c3c8400410f10b51240780f8507984480300600030f40100804940007041045401d4944150400c04c0c1440801103031120030348a4003801c80d0506108903000c096880e00e03070a0a5654030001c00040160301c0340f04030104442c038100002c42840e40711f07252000e0b0a5090002c9200e00d0001c0740800d004000420a50b940d41c0b24014ac0d140d40c01006010580340d443e001441030b9900d03a145001442c0c9400641914006450038848507000105204654052 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 426853561 1250 426852311 426852341
    0x1009092901020106051f1b03020606032b08090f1213050301180602090303250b0a0504150e010b0d110f2b1401020a020d03061a1b03070c09 61
    0x801500300049080f14400d000b42c5420545002c0442041001040010140803507031030240d8014500c7d4243c0130b8503511b98a0101c001da8840350078000c840c50705001c2c464580130101890008c86102603800803a4000c03030300c0c284052011080103d45450424021110449000011190541c11060800d038296100c144031140402da200402700d61407806008010303001d2105000c2c10900025030721010300960000c0c501c07070f9151008100d0740c0803070f44416041481d4960340400455804c0c0d45428840100c00009007450f5074103103000f0411001070010101e0804030280054002881300d504000e00340141954a9100d51010310800e40c0c200b00000c1c1c000103000e29406907030012402440005106030900c1041120704e1641070359540c2d1450f000e2020b078001c0c109010740f09540311121403660950882e070003040d080380140c1245e110f809036683c05000e0180208500b40304120010080880038500d806003807050031803540d00e0b40304a030b4400401c2045e29840f039081282d18001c2c2e0f598800c0700c402441001100082 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 426854811 1250 426853561 426853631
    0x806061b1b1e060c0304030c030c23030a03141b070512060705030103030c020307030602030c19051603081e0f01170303010b0702221a0406170c100909 66
    0x80750030100c04503840701440030380042d03032600703204100215904146049000ca210501c00000821314401c420381c000d50160003140d614905000c10b2801a00003e4090b440f41603440440c501d0303540340040c0d1401d0762501f40c035203048078805401005d065031049003000c0409122820100040034004200c100498104603203912211540c066510380350ba50464450011980600040000ca0b00500b6181d0100f44014240d940c4a9169540d41041382c1041c0c645c00e108010110345040c2045004e9020a442d030214180542028105004039001d080032410003401c0045280106c3c2540c0c00407024209405242c41c6c40ba1031505e000703120900350038000d1040d840200c90505051100003404170899044c0e4042419481c9000c1d911703028004014801b950060101004824240da004124450410800c110308840c415174118402007000360749850300304020b001454500b49031002c4000510f08903002041e5101d15004400a0044c0c806000940c440110941003030b08050503c2c2140100014a00042000301c4e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 426856061 1250 426854811 426854863
    0xb031618081b042706150f0512010b1c080408010515090a0501060512190504050d090503070f290a080604050c070c06050c07270b1c030806061b 63
    0x40d2150008206444a0404c0c241c01d0480e096800e511140e5000e00b1021031489101e000400e0700c1c1150354802c080107250309905100c00d01c2c101509400d040d429400034040002c101000550502e108205202d070045000c0b0701004109848090f1350050071888000c1000c0d10748400700290303180c00141c10611860110780000c4441510b8810141a41e1844e510f05090048003801c110400781c01400c002d0520180c13185070401c4020354080c4910407449039010b850f207036031700080217000b286d2030f500b003103110b60000761007440402032420504080f00c0320000c07041664034001c203d1210540030343c80b034403c004000003419a061a00840392600802094a04001c9541d0380d4641114a005010b0010f11141a00a00300480d9110f0400341800650701003d44116560700c04202d000c0d4800c82c0b03240200360000c070050102c000326038400c0482c02002a41c030456107141e507818418402d29441d4005052040c0c0e00081030b11619640203846d10203c0d1040c0000d44d083c58040290360321340c42014406540d281000003a1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 426857311 1250 426856061 426856069
    0x108060603010e010b0901030207051e0714150f090307030f17030103050604060c021f050a0f090c18140c0d0c0e0a05011d0d0b010e09070b031618081b 66
    0xd040301c40700d16242d1600c4e42000f05100495000300b605a04154091010340d0101d64140950182e188849240940e8503000c01f22160601c22254810799448030011201c03541500e40042d10501400d0800d1407540d00c0044038050802402034450312601032080c0007022040004510021110500422114800414000c46442e9501c400d010007803650b00200e0100c2d0005a03650011101c04a580c01602c441c0c0d108071030314074142120140c01080c03180d201e1050011a410f144280202810342e0801030200c2c0205480e100000e494500ca03120031400034504050540c00303075600c04215003450742844140750400d40c0c01108a074020280003600da51a116116011902600d03130300b59540301c041e004030001407503c001581d9403105101e84213032040e044c040c240400e60300ca240035040d42c0c1c411600c0346e000d541480c0350102070020003801414181e11110040c04401d8081d01502d0740004961010f14910401a1044662a00e21103041803c043c0724007012590880103c2c01d4145400d08080c260407a40b5a48208 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 426858561 1250 426857311 426857317
    0x16090609110a1d131d2409070b0f04080610030308060f040f0905070303020f0706120518100209040b01080105090a02030414150115050c071401090810050601080606 72
    0x1d40d8500c40c007000000320281c0583c80030229440c66250b910034050f949804681e0b0303006407401281d00716a448030030000a15100c04680c030b0b00f1400c0c41c000c298054443c1094410302c0b9144250140342e2412100182d00f4120411024026000e400996a222061240e18001c2d80c0c006009078003050003030720f001484950200011004598041d91811540d0311100c0030702c040040c0203800c0c550001d03290b50303d810340e904a034010100720780d1007034006003111455414001d081c4040c8140300f1415810a22040004c290b001ca00562880c4407020009110703114400c110703924800d448004540c4e8040e40020902882c0c00b5400f07401100c500b940e0a00651903440700450790120240120340e400685030011446040d400d80c00382d40c2c8903200e100707204020740e102a1a2072420100205d0940c0c82034649005204e00007504101044952440c14120b0600010441ca0354585101d070013000f007080318440321200c8907881109070038010101c15090750a10060a000c2c10040c01c421100c0c1404a5911004988c2d103003003420803 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 426859811 1250 426858561 426858581
    0x30e0703020609150301030c05030d09180b0d02120601170f0307120e18011d06100e0a0b040602060105121f0b040b040c030b03010e1b0607050f16090609 67
    0x50910903055034204601d507040b0f04007068000c0719451614003144542c1c0015406140101103000d005403a00c401c0501e4442c103854404100000b5000030000540313440020030b91409049808203150401d000030852040f00c00c1c80181d404400780c140c58070908004101c5038140e45045680079042d01c3c0c0d440400e0b5581c0c612890b0b01d0b8841d442000355601003558058104466495840c0443c00b080c1c140b8002210700c04c0040741915080c0c1c9501c0108051101107416040b0300c5001c0e86a100c60b458001d0001305c01c00c8a141640c014000010f0141e12241c3d40e14220801403d440002e294841d502c801d802580c4a000740503c1d4010310b501040b07142a140001840b0115800030300100e404003244e440701d030001d440c3c1c6400302c94200b40c60307280c020354540c3e80740102c410858542d41c0024124510b01c04050030341c0c18641a8004a0700b10740f280b5000482c001e80d03610301420098551a5a41c41307a813502030724214419032081500e005501320701111400200f640c0c8101c40410100784001078860460104541d80405 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 426861061 1250 426859811 426859813
    0x703080618060a231f02010506100e13060e100311090c0415111b420f030f1008030f040612020706050f07110a120c210e0a06030e 57
    0x20b08100d24240310b131840c9000c40801468070b61000414012a04e13406012145045c0d0303a00c007401d8010840da0910400b81c0c40b6000b241e180103100081040981401c44422800b4020582410303080000709040e04488002d14040b03401000514080c000f4103426141400225125000700c045042c141c40e000800c64000c1c001109501e242c24070f080503041840c0c035070a00c58400d010750b0040001c0104800c0c04240343d8914a15056000a810402001039210700450040c03a010452005504007440500310030f201c050101500c03407542180448881d80a010f143c4010161102c0041040721040b0151151400b441040203841309072a1146051502d90254510101809906000410143e881094041d030003040c3c0210041c6030105c43d03180c9c4d0060710421900010700c0c8001c8401d00c4081e950100e80c0c0803d150500c9d010349000140e9940b0503001e070050303002200401101054100610040030203c5110040440807440c0500b4980009404090a0450030303200398145200043c0b654040d0164810503074000c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 426862311 1250 426861061 426861079
    0xf010810110a03022b06090623010509031603060b0f090f0a1a090405011410060e04020a171602060a05010302031e0106080304062703030909020c0a08070308061806 72
    0x7441c210005d4000d901c4c803101440c043c605014410305003140200090178a050b000c0758582c02d02126000342c031318035030091842c0c1d000b00c5213820403405482c80d40321140b8024680907a54091060005e40303400e04943d10000b65240ba9040081007010b182c0c010032030703090181d130320600407081c040400c4411342d03003221070413001c030000b5000a204c4034a0307500c82c51000c2c02100a440c40d00d404800800c942c94012a02110070341e550f20080140c2d4123481712000c0c0d105101e40000031900e0309010005059026020107940140d40105004c06441d009201500d00900c0d9010760064610f0710741c141c2c0840311035007900300380540240e40118440c9a16401098141c03a0040c004040e05040304130400801322611410445075542e0f1003021030620410710041004001e40d540e00401c00004228000021302d20000b0200d01611800c2c0410001e50407004040444075144001611b80d503030034207024103000391500c0c000d011500000da00d100b00340d01710042034003500058510203082e0101c00f03129600340c64156002a40100340c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 426863561 1250 426862311 426862327
    0x11030601080f06030307060207030503060f0a0b07080f0403080f0a0f051e0304020f0a09060302010905030a0b0f0702030409060b070b090601080c1219080720010c02040c11060f01081011 81
    0x2c44072900880c000c1d0480c1d1420b06a0344580d022a00320070700841c0010400000d00c031051a007080505401441114080078052401c5202c141c10300c61400d00915003500410040d040c080100b003650011500400b21139544d801041c12a11191701058419012031180c10060a02e180f0901c00e0b100741103035501e0501803114040100c801c1c1038000800c103e0380452070301540000e5880301560f0740028286104003144c074a085100141045906801c40342c040c3c0d20152221780462020180300d40c00900034207141c84107841740c020403401c1d84140d82203507000600700703003000501c10060702c020304081c0c0c0a4003015070f0070b40706c0f9036405450701000c1c071818620b030380075403162015458148509034100014100b12500b104078011607001c0341144250591301c06030b000c41c000e4140800707200b00ca42000f10880d00d1000307045e100400607004100d801000f0f4002c60b5151600000359000d03c252400384542e40084a41d41e2508855802514009000c2d000c09030059031958541000c190041041642034648003601300420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 426864811 1250 426863561 426863581
    0x1e0403050c0d061d0102030106140306102714011d09010e06040605040603050706031131030b2701180209060d021c0309050109080303180c0a0603020705011103060108 73
    0x701d000703403107141e0b403102040340c07084100800c2c00d21084c0f420005600c961502c0800307040740c8054210714030b959004008101c07283d520b817100c05640c60301c5400c0c00d8601d4000c980c0c8150b102d000300d00750024441010440899000704a46032462500740983e114085515a4403200311044050181030740c004080c2d90042c0624a81840950ba0000001d48000380070b9607907100150568443d544141ca071030300a4482440580d074140540a080328043c1031444c81e00c404000c2c0072402584505a103c03864100450340b4480c1054162210b00035500410030300710394104151800d1401002110028030148450440c01701e460040c011103150a41c44500c4c0c148103000d40c0c00f8462007000080c08a81d02080b102040c00050380c4d109500d8003000200340d440c81d0000250301c3d002d001080c4907040f05050100c1004104125030000086a900000d016045040010309503180d52518501c24401503001c10f044902180040c0d15074080c000d9640104002d0219240348a020000f03403005481850020700600b0004074003001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 426866061 1250 426864811 426864829
    0x40606050d2013020a08040525170109060c0215160f0305060a0339050604050409050a170c101406361e06011b0c030c0305031e0403050c 60
    0x700192441d01d030511602c83c3d03441203078001e40500000c950740009001c2481401c110158100c001d00341d000703000041d081c002104131030721445560303003000342a0103801076506c0a4001d0b001480c1d000070144407480300a440a9222030010705100a001e000d440000c0107007042e05840100720809031a40403516044c1074045000e004010481500034030100c00020010302e0220385200021002035070421a103c0403070301000168200240101d04902022050020f40e1f40d90b4101c4088600441380050702080c5882c01c2070034218020000f030031040c100d8505200c0c0a056100425a160415069400b9101c505507044d084a08401883c0042d02c20381d40010401c4c205030540260208e0701d004e5031031844000400003540300704200d61090400e010781c41401070640f0042030f01c1a0880801c04000034618005000030948991a004824881480d6400c0418042650003080155812003401d00e0384e5074482c100707195290f010484040c010301e0900441100d00101c14155429030303610070050280001c4c00c03020458200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 426867311 1250 426866061 426866123
    0x402060a2f07230915040f050901060918050a1202030f16021813200603090a0c050111030a0f0e03010c030903080a09030c0803220b040606050d 63
    0x54076118003407801208009000005030111002041c1c514182540302100409402030400d03203c42076840c24000da80e569a0b1141d116011960302002000c0020000740500307110890070481c03601d00b406010303d170784064102c034040c0c6e8078a02080c0700c2000d41651a22021181840140040d0000d9800c08005086078105000b075a9485c0304a90a121028401484c580e10a5500015004100d00d42a0850510364240005000c4165806105240c0701808400c2d6146486000b425078580040b68140c554480b400c080130b01e007000c0c040d65101d14001c00d12544d0b5000303450090742d9404900342c0010312980f10740020361040300d0440146081c0b9880719800d54013541010554020301002d0960788845840901c52030240c140b103540c4c0484c80d80f0560901605400000d4001070003203080c05072001c00703c1d80104084a89540c44540300d50740f0390750150700d00c2d03400c40340281000214840010100a001d025808103015900503041004450f65903010401d100111110041c46414008410403440104d01e11180f800c1d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 426868561 1250 426867311 426867347
    0x1b07120302070804080f070e04080a030504172a070501050a0509040b040504050a020901150e0607080408071e0504020406080c1803070b0a09090203010303051c02090904060606030e060402060a 84
    0x42c0140e56500094100750003200c056070140501d0296100e08002c0c940041c07504c546014001d0626480701c20b070510900755020f0501d500c0310082010400900301010340e01e6621420507484901d90a4650078a4030301413424014080c2c0392601d00205c42000c40c3c2032040300ca05844041ca4640da02d40c1c10f07111a040840030613030041e80c4840c0207075151110301400e4456031003540940640390003481000b80e001c0040c1c200c01304444402a442d00600d81000803414903c000300c80b0551580098509503100d44641c3c0c000c24010f0080312000a050010341d000011101074480b8400e055540b1201803000f280558403c1038001051040410547e6061000800400c150550041c0e44645260082480e00c40c03c0da01203000e040c00050100344040c0d001e440390303028120101042d4950b52440d10004e00b580681d00020008110b060149079400c0b5590381100e010f00405080c0d4031a40c50a0b04003030300203000c180700c1c04020030704000060441d0480403d05603c00c3d580182014280060220101e070502000380c003070707a00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 426869811 1250 426868561 426868567
    0x102070503011b120e1906050f010602061306091a180a03080c07050a050109050f010c030603050a0b072102091e13050c040b0d020d0b031903030f060b0a0905091b07120302 75
    0x3081440006caa2142d001c0024680980c64030f804070840d13030010500b0449500c5000180a0b455000c04c02d560001c0c080000490b581005003001c0b8000c1c07540d00c0c0000c00256244c000c41d040304802a40e804d118060342c4440d482169400f00340140c884606800040001c0d040030300095440e1041409405054050402c591415520b80d4a09003101c0300d0780307410b40d40782e03004010005014000b4010256034428174a010311000c0c0c990354505540e0200408005c040040c0d640008204610614140300d180001f080c1340383c640c2d42200800da000398803030000e003402014101070101b000c3e105a4088140000c01a02d1100700303008488517140101801b401e4541031f00e10030400014000041d00c090b2213551100840103030343c0c0312030019100407035201c40c40450180d0840841840620045107201003001d805050209610341c20000d9803000704007a4000003000d00021803860000c99005000c00c1c1a900141d4001140340c0300d0040c1040d504543c400200c1e5070000810070200050400c00f04141c42140504000d41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 426871061 1250 426869811 426869831
    0xc04020708071415060f06090d050102130b030702060f070e011808030703050c0705042c01060e13030305060a0503030a180e01080a030305060d030504031e0605150102070503011b12 79
    0x41002100f0301d0243c2d240c1c0010505607200d01820f002c1604800d0841ea40c2c0740009a1001081c0035009542d003c521428019501c0340500c5401c2d011100412030107642c0d109030a40b91410018141c000703981e144c006100c1c0c0c100140c0303502d0144016a0003000710b911002c1071404060011143c90f040034104d2100035040c1d1500249143d070410161000c0d40c03107901c40300d48a02c0e5800c00309190400076030000d8411070602e100ca50103800c032500351225aa10804070140b00c0021300c9001e50241100d54401502c01109204100d0240074503210aa6654841c4c0e50501c43c54565104114410405000e002e908d60000c01c01c081c00c240c0241c100080794a548001002920750356038510711140001d90082e61a0782041c4150f0007019454450310390b01c030000b03c4048030140410703240103160303020300e00000b06410a500c078103218805032000314007101c80e4005c0c8140b05520307005071081000505600140e016204004c00480c2519040c01100d00c84440c0240f244040c440007001200e4003c5c084004888060b5100b02a034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 426872311 1250 426871061 426871073
    0xa060801020d0209121b0d210314130803060d0611130e100b040e040609051b03010c0903020625051c0f1e0807030212010e070801050607050c0402070807 67
    0x20400324520394006844c0c086500a110725242d261500b0303400780d00729490350040c0c3d0140700e80000c1c1e99034058404043c000c3d5035182040814505805110400b00d041c40c120f5141541171f04409106403080c12901d40c1521000b01f000c072071089102004184050174400602a4100340c079100c040c9500a0320302280d4004101c00409a591050b6000d100c5c01a41510074080c406410300e004e500081c014040d10b008030b10b01001c0c000180298040d409105011001140c01d1151541100c410280c000d020b0b510028003031305000300c412109441440c000d5003800c0f600310745140640c07900390031240c028049901d0700140381042c0001c1185000000310807841d540c5244007240041000c540c89140803151030012015030031011b0007001c140c05d04c1c1c80070080b0342e203d801d94582c940e24004a2051107400d209401ea10f4805003640640a50b035802c1d109404c405000042001c030641b880c034051050307030325200000e03601c50040c000c075440350030006030007540325510000c0b00f410181c4c02000001d002d20442030070818150344074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 426873561 1250 426872311 426872317
    0xb030a06060e06030607020304080a0210030608151006050405150a0c052406040504020105160201051e0711040e1e030904050c030a32220503030f0709030c030b0a06080102 75
    0x50003480c0c2d00700100006400c04000b00d541011207400110709061030f2030f503510368a20a9003802401003560110140e1004e00a801c03a03405050b54009580741d0806600641410140c2100d140f10040c2700d00c0c0300059698062000c0b641030341c00180010b20740060055580013a81c2c4240c501c41c1c20040050001c201150060012001004c0410001000c0e6400b1180403000c800002c3c207001d00c06c1380350005100c0140e802c4811281c6d90441e0b2200d1090078074090005844600030200c1c40c840c1140d40c104201c800230340c14002800300c0c0d84105421045260b81c402840100c9a600240c0030076584a04c850b41c050f44520300140351842c1c4038504030303440d010b1510041015108243c4200b2286403000c41840b101c3c40310b9000e15941c0340050180c01d0009011002d0340109114165400128510150b0100d14403166103200c407541250034000f09540c9922624210703980391b0046035502c4031901e8140101d001b20b4816845507044a03003100f20f100e0941d0039a203410302c1c0440c000d00590000340d618880095644420300207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 426874811 1250 426873561 426873569
    0xb03010608150315040f111c140102030114150c0d030f0b0904120e0619020f0610080706110a0b01060e13060e0115090806150a09020a0c060b030a0606 66
    0x4815036401e00c1903074811140080b0401d540309402c09000007007203640e03101c103d9622030380081c0303c001c8440072820604080282d032001280c000282c600030a84442040303400b00702c85e502c00d0700f032031001210b180b6a2500701e00003809052600c80b6101d0800d0303820f2801491604500d400f0030341540c43c08103c8885a07103000d00c105515404a6221a201c1405500d02e00c22080080710a483d440e2041c40c00d50f81303207428048480a0b000500103450403800440d00e500e03060768610109031507a1590404d5100019541d007a101503400594403a040001f1104030180d114007089403d64401885c01d2400d00c90151500345188041c14800d1203201d00e500b010401c3d5651880c02090544c0345d4403000c41d0300100384841c4401281c42c80c0d40141c1040e43c200012004241c240d8112552010f2040800c800c0e150101e44482c0b255202e90766a2003000e092121400c01c98002c122410002c1340e052022694801040041c0e0080c04e0361840400c44034407110b00450010342186000c1c46004080d1803c0070941e80e50070b800c551940d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 426876061 1250 426874811 426874817
    0x1b10030b06040e0717060126181002070b0702120403060f02091309170a080604050403170103111f0e1e060a0512090a0b0c0a09031509030906030b10180b030106 70
    0x19010740c0c8003201211a64101c0c1080c6489030b00d423108202c1203c034014007480d09074103500b584000100c84640326103d03000303000d001009072843c07540c60080a101075003140c001620161207150100d5072007400010440d81c0010400a00c609051958882c14010810420340310b1038035800308441c800b50342d11034080c0003c800c0400340c00900c0000500700034070180644080002d03081820040650155080f00b1000d80c4888121008683c6945600d01140e80d21120080c140d188080c0703030008001c00081c5140440982d109a03041d07090301600080041c1260141d000c0e18010030742c14001d80300a410680c8116004c60ba030101c040070344026035402f0500c07a5001d400c1440c00606c02251140701c90000fa01c0042d001041c000081c58109015180c0d907075001c86c090842d5202a20005401e410340d03011705a40c00056401110207180300502c004242c01030244482c0490003d44180c101252090013031041d0078843d2006008482c203801c01c0c1106540200160900075452407071048001044003819006601030089a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 426877311 1250 426876061 426876077
    0x3040305130303021e0115050d060e030a0801090b0d120305060a05060409320726040c030203100c0e0402090103151215020a080f070c140f1b10030b06040e07 69
    0x710640b11590b49103d105c0b21345904042070201c0803a00380545c0c40640b8801c445203003075070450b03103080e03001000001050304540c0000300340707040d40341e4000440364100ea82d07040b41801200360410800c1100c48641100800d81010060952a20785c4a64041c5030720a00c00b403d42c01d80c1c6600d031000206240c001d40d00000c503040d12800c1c1071612642060780b00b0400300310911341742c41145800e035030301192410040a071001c0000d09561041038161401c01c01040e094445260189030425080c41450403089020a030300034894881d400d01e100d0b4a80c8201c0c41094020741e204440e54090004005c080c1d40202c03809410503486105814100a96800e0300006002c82000c01804106030f140c04013207600c0c100400003ca610511401d82d00310780000d0007507401140c540c444410390f9034089c0140d86020000d900501411915284000600310000b04803540f120402e0850b03180303205030400c8803074600094880c1c9801456103035403e0b450500940203484051002040c03030b420310307880d0f5a0400c5041000c880c4800029292 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 426878561 1250 426877311 426877333
    0x30319140103200d0c09021c02040806072015090f0102030109020a03050603030c07090c030e060f0a110c07050918030c010632010c06020d242106020304030513030302 73
    0xd500103c0c481401030360b5140b4644000e8680b00a41c00d0309214140310f4580008100300f500d142a8482c004c1030f020850119112074640e060a5940c0000b100d452001c103c03880a001d00e0266254120340d08184101d00401c0140700e4520481d0903040040c1260844c0d2040103c1410000c2080c0090340c00b8110700b0400580702e02ca85040202954400790a03203010341c01c00c10038800782202c00b0070110191842c105000c20407007803a9004800910000b0400c1c440e0b4013900b0b09101c06082c1c00d0f4040f6005080104007400100c200c1c5410740d11912038a1703115841503100d080300f0451801c003480c0c1c40783d100451224100d041087c4958040c25988000c031050010b954807202400401c2d01030700100d485240520944400002a001d945402020b2007010360500201101200070400203404888150345a01c4c01400590030401d4034140c50740b40c0d1265403c0d44044900d0200795200004115105c4041c0c00d40b482a0480064440c04020b50010304181c08124003002a0b20b039500741400c1440056109030b008210b0507243e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 426879811 1250 426878561 426878603
    0x4080a0317060a1206051902191808070611150f1602011505010503090a140c0a0b030402090c03070e04150603050f151009090903050714030408030319140103 69
    0x185002d11441481900b41311608880110b03e0826600c0600024192501010f2035091482002180b100900028140d0404440c8c00c12282c010103103030300d61804d0403140c00004d0016103c44e004018040e03010200800c6114402c200c100c084158070000e4905000045140386440c01b800c542041908030b244080c0840c1c02d03a203a41c00f610140b101c2c07008001d5601c28602050024a142c4034540c100080440850514401400921169513000000e000c942580b2528180c95080d9151803e1182c01d20ba070001802f80cbc2d0303481c11030b44510b50080801400e0303500c5925010170b039000130f00300d0010040c8100d60340074951981d214207100d03d903000703446215083c81c0c072500a0548800504d030b420340030240001d105c040c100030740040310405011605091818040001200c14480d2580320528103400c010015084c142c001c401025800d005003945848090401c0c40c09940b0f128a101e5041d1650081000170001800129600b95184030740102107204032281894812010080e0410340702d142c2041d0044441c40d01c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 426881061 1250 426879811 426879857
    0x7120f030506100c030239120703061e05071d01031503112407120507110607020f03060a0c0206011a090907030b0310020a080604021204020d02010504080a03 69
    0x115180c14095490b220000c00c071568048595101802040d0761200c041500a0082c0c155201303440e561409402c070416080c1c200440010b400051840b2400b0000701d1a04005c103030100040e00080041000307614580c0c0b0f103001404494003240245905401074680d40e880e9005090184181d5600c80600302c2c4d904e400d0701c0c0d910701d28603103040c1458648140b1090001c280030a00084035089100b1403003420200e40483d18400c1c0054144c00000600c481d00311500440c40060410a4000d00d042e8035600c402407410355061103011800760000d002c01161034100e01e42400144465407000d803946580c00100d00c007191414405613125080c5984654444503043c1d410454a03004040c00010000b004d00034a101e00100d100c0c04e00307140c0c010400c6600040600780170790007480324001c001c0c040341c903400540a01c200c000d41040c0d40d0800020201404034815150031f000303440756210142c0c140441e0382c4459003003000231a48420200d043c000188000155440144a0901c0040c081d032161030103800140c0008402c08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 426882311 1250 426881061 426881087
    0x307062619050a020f0c0f0d02030a020327060f2205010f03091a2a0405010e040e10060f0f1a27060a050c06060102010603120e0a0504020712 62
    0x4810941001401603003030241400071401440c000800b070f01e6500410340079205540400c540000e0005400310a80400200728480c4003030882980e91800003000102d84910170040031100503807080c4401660100044404800c031090404c040800705500d1011400c1394111080d0b0980440300401c040c1170703039450441c0280c044a0a07901c244480c03420000081c2c106c08011201400b0590f0314a041d82c00c0042d03c1850f041600f1b601400300c8401d19005840501030000300f511065207a4110401c0c0c44014042020344050f01e4058540003602e40007481400020081c4010f07400b254481d00b108242c2c3c071011403040c0d6010b48141055110018102441424030f11025806002c80358504450f080304081d0900a81d07051044bd494510090f80b440c0b181c0c04107050004030982c0c0d000d140010400030316074104004112a85c5241306482050f6a44d5005a00f21001440080c1500d81c0318003440c903102e846504003150300d0300014a00300d04140c482011500302e800905088a64916051032030381c0181e0800101c58800e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 426883561 1250 426882311 426882377
    0xd050907030c09110909040602040510050703020a02060304061e1a03070305060a1e0c020a030809060403120f021309020c151003081b03070b06041503031d0d02030706 73
    0x2981c91540ca01010850500c01c02c0041c40d6629800e1035901e4200b0226084500700429418090815040000096020b0301c90316118100300a5200910b501680c01e59108580540280000d202507400340019070f840200105c601c240d4600c860080d0664071010440b02c08404440007511444105408140302040c7c81e18074442ea00040301040000c00000d4032a5000f1032070f4501281c0000e4020b20003483c0c0d80100701011110f4240324544603066400900072084038000da8981449807210b2200b6904e03104c040d50098009030b804081511145007903006600081c3d0a05401031901444246100b450303d0703160002e0000c0340d000100017010581c104100e440314280c110308074a030390410004905203259117100c001d00f512804501c14107949a94400f81c3e074010100415240d0390f1002d8a0145002c8108885030761007245003140480210400c2040700040d2903043d2500301c0c1c42e055a514000b118011a00059403102d280304442c1d00507242404048014107003611100036805082c1080021450114102595 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 426884811 1250 426883561 426883573
    0x806031204030b1303110f0313090b0603070c1b03150c080603030d0c14040323010209130506030f07030813080c010c0807051006120213021305151309020d0509 70
    0xf03d0030040034182c01440803020024203024510b820345076861404100b00440c0606004d4aa100d0004030050420704d0500c040c0405140c1c0b1070562108403142c0e00142034120b4001c0c00043e1403203005610810200d8000d501d01004000076560b08040c0c0d001a400880d4110b580c540081d000300054041d115a0741728600744030f581c80c81c009012030303564000c2c00d154126aa03110031a001c0c105018100d9036103000b140c0034070b481d5616240c0c10102010102545880c484407503206501c0c5500106209840800500500341c041d500c4c074407d03041000d0301000c0d01d010351501420040f00c400c42c900f040700400a620443c0300c1901ca00250351045070204c19580310301016008a0118222030380c2c4900800710407a40000300c40c1c2c80c1c400781d0920624050000241600d5a0302d40800030442002d07043d10120318034421125001101040c0c0808401d900a0960318140d5905500e8184000d1401c244041e000c00e00c8a00c00d5070428102c880b20603040b4210340d002c0c000840c0c2c001002106900280182d9031b00c000c481004102c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 426886061 1250 426884811 426884813
    0x60210180308070819050708071106060102030d0207020f06030702010c02070e0106090510031803020705041a0d080702060c0321090c150c0a0218010f210b04030c0210080603120403 79
    0x22100c0310041030201013103408000580c5046288120040c0d940d24983c00304400e15100c2000390440030182d40300c402007420404061405000041c1651041c00c040c0e020f103050030700001e04140603400082d4100da0200ea4888005825150352019503c42c10b4103038004180740581034000390420200e80c2114900340600c0700140115504450200112a002e541103c1c946138400b02c1200242800341400c08540040c0300f00206241d400134070401034603011142040082a10549500304402a92901d50042d99640515000c00e45c0740004d401d0300ca0016010b20b10705101c8240b45030440d44105000c1d18841041c413a03a0b030140b40c10b40381440d4130020310401042207118140c00600f43c001206d581d40c0e081107001034604080c05041c02440100c0341c4c00b929145401c04031140101c0c2c180e10074000e200004030021800214902040c000b00e10105650816204003240d589442c0045030f0014426030900080c80400c40058659600a425107061641c400d4140c1c10410f04140c1070200000c8101402d000502c0248 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 426887311 1250 426886061 426886067
    0x1080610030201121b08040203010501060320072d0b1005010c1b0506040906030506060607030f0f050f0f1819050f03100204030302070905060d030507030c0c030209010602101803 78
    0x3041e030707409090606030040f03004242c00c0500a01c0b041d5107000801d401542c0552030308822014020342c0700301d0090240d80c0e00c1d0081103080f180018540d07100004005480700084d41c020b00102092400342210716402c8001d20991610a14852010480347d15681074450600c0f003554040ca400c1480512040b61407490300e000207281400101c0c014050703401a40c0c440c0c2195442546080003020f000d410035807100d80d204c08160080096210075201d501841000545901c0c115085614503540340d1501180307010040811540c00b86240c00c03100505c20100a00d03a810300c045400f9000703010080321119520115900201c980b41d03449201240208810559070f1211031130003441c80b0030360b0026524072a13005001c00019161003c0c0900460140344001008000e15a000c503984050f00e000300c105201c1031f1075038801e1154070300c001d46010f00094170034441c1a000910410b0780e220924050001085c4040d12078000039400c490030703808100564000503075030071010500d0240380090200c0d549103250208582e01c0c05 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 426888561 1250 426887311 426887341
    0xc030304060b090c0337020a11071a030a290f0307061e02070302090a050f1302180603010b04060b0405181005010c02180907030b1312030c03020c0f03040e010806 71
    0x104041e00300844600b6030007540301500c0c0704030010040f081411b21082400c80d4020b502a0a68000003a006691180800d0340055842c2c1105e2918010398100d0f598000d800881c1d030000380174030500d55124000051002c0102155144540d00b0f20301030600f50029204210001894200d5180203400180042000783d400a05550024080c40285081da0017115812400d001060300000d5121165005001240b001036000600c6801c0c3d041c02941141c0310005151044030f01240001d41c0a286046090003d40d00341d40c04079003111002d0008500c01c0001c0c03000806541c6950407103042c8513400f0508000fa031600b0940f41044141c00f003900c000d542011080989041c09a0040e281480442c011040454032005461704860118043c44005810441003c54484440348001d032808000307600803414800d54108001c61880c0d000c071b102c00313961220520940180c561142584141942485007001c1810180103564994052202450340c507400c140d00621801410703000030216510107000c100a92000c1880 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 426889811 1250 426888561 426888571
    0x60b270a031227091805060c07060e030703020a03030b0406050f3f010606050c06070f050d020a050903072106020f0d0e010f05060306102601020c030304060b090c03 72
    0x802c0b0068861600640d05249600c00001d41414441a40915403946114070307419100071030010701500c070340d0b200c045000030850200038007aa0844030218400901c50030040c840c042c812080816442c3e804525181503800044007a400360b00700b1070850080603818130650404070021201008038600740000b00c1c400031192140140106c400d9042c014950212070003500d040b4081d180038001c0c0321040e508031440243c1d58a0051803540c01c205c00441c81c07501900580380d241c254407009000c20342c0c0310b00c01118241c2c070088580003800820042d4080c084024002445482c400340c444580e6140b041044c589054065404ac041001258501c418501c0d2245c0c090040300e60440005622000d250401b6840c520600c495a4503562a107010161400d0064000c141407000c410420007065a6000034552a0300046a54550424080000380030780d1500c20280c090100c0c0e000c0004001c8035000c0b03510f81c2260b019541e000d0fa80d610104c100420054240540dd9440c002681c68500c241894808042c0a00002d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 426891061 1250 426889811 426889823
    0x50307380310084b0307050106050a0501080606070204110a020a0516060801170f01090c0905070905030d14210103050d020703050c0906120105040303290607020103051306060b270a03 80
    0x480b40300082e000d1350820040c442c04910003005140e43d00a92a502d51180500300e4681d4281500010f241c130300070f400c3da0211001030b1114800c5513103a030104812907200000032030b881566081c0001403c80703c01c0141c40107034071540080c440200f071402c00519101b510140f41c00c14045c500e005101c40d07a8090441303411203030741c0c040d800340704013013450110b0510300c0281404220b03600c1c0ca01500700f8810900400d0046940007401040345845446085440c07107614025250540e20030b90041030100d01ca002c00840d440040d01416003000c1c0300741d0303044e000b5a820506111b21440000014400c6c01000c0c406800e03a0f02c89030004025032032441c2d4900341c0b10f40485031030314820011000000c0d45038a40d20300344100c040011000304010710b4a454082d0013860400c2c28503040c000700d0003003070030050000304054450f020000e01c02d0742801c0d0191b00440141130b00404800401c900c51003d640001c0e41030150f2070260034034011407515030b0107420306582601807040c2c0e0b5a00302c08003001000c030b00c3d0311800120410b03a90000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 426892311 1250 426891061 426891133
    0x112020c0105041b0b03091c200a150e0c01080705070f05010b0a0b0313060914060a0c08010503030406080a0203131211010c08060906010c0821011a0405030738031008 73
    0x7040e69050790640901c00003803118150804c4808000c40c1822031079108500d040c04960303e003000c000450350cd03261154101c2e404a000f00c90b50b0341c00780d040030b41d012200d4a08030340350a500d41d482c0000031000d4001214942e45840810100d85001a070707113000741441c105498114541140c001d5008071180d031014005965810a00d8180702c01225048040d842040031100d00381001900e00c0e00070000c00c0603241c0021058070000c6180c0ca404003c942c221a02a40c031190240c8502134601c0003540050040c0d42c0c002c00c08404640003800c014018120359840d41c903510041c187d440342c0d240c291089407214008002e0700504220b074607070341d001271580c00032070a103032207103c4202d540b44c8441244135400074069151090b0019810612000c4a20340c1600c0c1d0f8440140da03142070002c2c240c5858000c6009003641600081010b004900c110090f800c4921082011011242668500502a02400c001101c508030f000400c20240c8102c2e15141001092807000074480c5442028003480f4800d07042d45e000058050750 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 426893561 1250 426892311 426892363
    0xc0f071a22170c030105060909070e0a02090d12120b1e010329031e0616090f030c05180906060120070e0912030903090112020c0105041b0b0309 63
    0x1141c0e11070302910361002456103085001ca502c580d0340464945041c4030350b0800d400248281065111030740551b4042008107003c1c3d00300411034520980040040001035801c0c480302e84150354811701c0015540c018000c0202510806000900c0220780310560890f050816515214030340350b404607103c42803080c20703d200e0f0031042c0c080124042c0010300701622100c14003020081c049a40c210300f401c10080d00b1400c8880c900c2003c5414403c02c0720007982023886820034400a03200885601401c00c242003617140100301240c40d203a1400300c0415075003055070803ca10040034002801c0c0440c040610320520821035400f481c00080140d40c40e0001041d40f0304000e10810710703034108003d00300031001d03140c2c04805840b482078445201040c0342008841c0c0ca181d902c51544401c04032510741303044074022600d02016515003040d00e001511103000c1601e00a0800e50308203d45201243c00f0702c151406180300b40758036000c90505010070903060705550000e50054004200f80103c0d50800141c003803080d113184049110040c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 426894811 1250 426893561 426893617
    0x1009030201021308030306040b0d1109070203120103030201050f0109021c0c03111c0506100807051b100501090b100e0420040806090745020c0f071a 65
    0x191010b140c00281c3e16040119121601001941c030540c025035007048250a08030402180f0f541d0944060000c0e05407122802c0c040c03e00c5480142d0107030303160044a1528403254014403068409a00540060b5503990a100010710141882e03401400300da081542040c1d5141c481407044503180100045c1941d42c2c00c88880010b0080e041420003103a01c840054490920394000c41001032a0100600840d10384000594030f45041e20650b50415020750703444620b642d0703c04003994503511040f42001190301d03205d15080040c3c030402000320001001c02d0041030b654541811441590a5000c04600c03c0ea41e0708040d0307005d5980700218005660040b5070102d18500e20021003200011800d511410fa802c0004003c00ca0f0940003c00d50302500784141120005541d0b03442070201c0d4491012524024520380307800c094034000442c18a8111a04038407105c0500d03c42040d20412a4441c40401c0b4942e000541051921441440107000900c072200d503101c44444000b088052600c00c10002003120720301710707034040410b1070303 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 426896061 1250 426894811 426894817
    0x30d0b0307090f02071101050304150b040902090a150e071209060b03030a0f080903160308150a1202040f0b03031b03040e0709260606040903021f0905060106080108100903020102 78
    0x9040b5600b00403201d01002400007940c401041a20154610303580040703507501c100d003260300c21600240d0841010179243c5240c006003001c007688a51003904c552014002da603071850712600a501942e40041c0b00f546031408408410f009501040740364004108004446400401d80c0020101d2605c000400101030314110000384413480fa0190103100100d0090700300c0c0d802001c1d840c0710070704a880348a038a03541c004547d960f0b0f02c03e003001c0b440202d10140301c20380024010100590009501541d064041e14030401003950310310140e005000c0e50000004003015410070b1301c03c0d40b05801d50301105004103069000800d94130321568014034591551040c000340b947d2010700684000d080c5407849a0100c0c04e1000b001400e60040303000302080c0000248d03400407902551418520b0140548000c0c0c021903480c1e00c104001460502c40940a40c040c3e201100001555815404005500c0000000301803c05007172240c50030f001600300f142889620401031001c24030000d0507140a6031600c1010600300300c40c1c5000c0380680 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 426897311 1250 426896061 426896069
    0x819090b040806090f01090c03020d0602070510020301090b01031803080c041a09042301051e040608060901200f1c051515040e0c0307170c0301030203120a02030d0b0307 74
    0x2901060101c2e006001003081030241d081d03141110401c05401d003101d03088843e448002440306034025802c100504290a140c0d1107035015200040c00d044054860034180100070100c0d000890340000140200a09481a035045403800c0c6410003040c101251121845442c0340400790a0000c10400100400074403004c48002c6e040c2e420b1007a980740e103004002042500801180e500ca41c1c10f05500b4034041003210a0000c44011800410606901e0300c402e101411224001d224001c0411601890780ba40b2030340152401008041d00905440c64140f01c03a0b821a0b24507a03200d0b445142d6024840a2564210b09450140d0501380c104c50b51f078a0010307881d6081079020204c1018460600042107210080c0702c1242e15000c0d01a514143c0303000130710802c21014491405813005001c00c4802060051081801550f031150071410000840490700003400303030026086580303d1b444200000107008500b414040e00711a40c500b48501410308445180294070b03801145500300400d5525503249041d030340d0820803c0014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 426898561 1250 426897311 426897329
    0x503030c16021c0c060c11150d0606090918150209010c0c0e040b1006090b1305181609060e060a020c090a020a0314040203030a2312010303030507020a081909 69
    0x10081529081c03c0b40c450b841c10742e80700a83c2207001030114028204055115071041e4904001031102080050086400e02920011542805203ea50344111700c991006444280c40c3c4600003171400300c6840c203072224a00c0200b1201565529130300010400c0c2400700c0440042c81000d0780b94050a40101c1c1d2503a0001310280c81940142d0300001e01218040301503005601684c1c80120b107641700103040c000440688074400009a40d100200440c4080c0c1005d010340801c40d14420300403a0b40d490001380781c0100c04000e0b80d0710b034a20a05201d2086a0f4004507040039005051000c0458a080b00141100950540c11070040000046c0b811a5910a021604203810300402c0d10700d6071304142e440c4e10700940000c141c0c000840d24014041c255407a003244003d10582c3d00030b00641c030300780c8440b4007101e614038042c80f41100200d502c01404900c2c548900a031904190403a882e002c10762441c2801001c2d994040c12130f0003076401c046a62804600c0e0103003103a1102c806110140c0101d0340030380c02140c8000082d404550300d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 426899811 1250 426898561 426898579
    0x1062114550c0806060903070803030108031306030501050105070201200f100c0201060b0a1812110114091f0c0b150f01020607170a1b02010e01060b070503030c1602 72
    0x1000407044034581001c460041c1d41030300d0010307051070a41290466041080461002800100c0da440c01100420120301d010342590b40300d139650100c440c0703180c1082e0800030940d08082500821001900481c1005214510b820300c0154907240c0042d006204154010b41041010000610403003010741050211003001d030229104201400816511f5201d0a540300100605082d035862100d80b0502a01c41070342c400a844500e0301d131a185042d24217914418002c580178151000003d0807542c1c003803609599600818400f00c605a0b114001030181c1c3c0c1da00a100388140c41804050030603141d03401c038103090303a5a12044905002188406a514455a800041c07407a03000c4405c01c0081c6069003241d00040c10305a8800300c84c00c2120005a8607501308990325030001c3c42d00f002a00e55000640c04664014100042c00030b2812554800702011302c4400b05100302503919032030001d06005092041c4002040c046c0c0d00c2c136003011050b549050b00c912014040029844001c08d03002034003c0c0e40400c0c1d1005075801411241 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 426901061 1250 426899811 426899911
    0x7020d08031e0a1e0e0f071203090e09030a0c080f0d0f0f0b010503040308061809060906070306080d0507060f0204030b0405060c09010e091e01062114 66
    0x7880d2070034540300c2c1c00940161010504070003460080044a034a41c449456480c5a0218003200a00850f008070843c0d02c11070042c0360204106000c00c0002d0500808602900c0403e428040c18803d615880a0000300382c0004101c00c4041c08002e032424400c1e64540500c001965091042c1ca90241d005030716203000b070020381005150401e6008103101c00e007580007801a401d5442108046446038010b00380420750030400100024881c4c0c0403654001801001e00340c0b620320200b01205114000c491011903030f03102409100300054104049070b4400c01c1c61a09015a07400c143d030b69511095034a002e1414810003017186820000d15400a10008040040c21529035550b8200b03896912001e03201071320b80b0f000c2c10010a41c41c05000040b1a10200181c540400d80007a19090016100004220401c800004070507406280e5030105024001d040300d503502c824450749c0c0e2401e84800101009110507042c41e100c55038000040092074164414103201d0002c8141b01003c0d400180c2049595007030b10000e181000800e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 426902311 1250 426901061 426901081
    0xf03140f060709031a100314010204030803011203020c10091e1707062c060d0915020406141914040b1c050601170c090607020d060b0f060a1407020d0803 67
    0x10110381c01749120f8030204101007034130b244482d819181c011400d046407100b8004102d134040e620308200c0d10000010300c2c280d0341e42c0b1010255042a00a80c4840e2022040c44040c0f41e41040a41c030b48200499100390074030076001e4080d01c0350b0f6040c07084502082402e0340101c04070001b40b0080f40240172510804c00601c0c000c251140d00e602144c05280045281080084007074400c00c6202d45600d10101d19004000c1105c07002c0010301e1f00102e0788401c6894551000d01c0000d40c01c10800c12980c08070300800340e2210b05144019140c001000c000d03011240040c00b0001814404000e508440a01810040c0030481f00b003400109034030560f00f000720518000901020901500038894561100c0c0c086e04014540341c030001154221480180e80540410f00c0000c107403034140000080290610040070a4030f0410182e000c00c0300c1c0c040302d0720151000e9585968034443c90500e041100700c03c0c02c007100d840d4074082c4041000b4088004401d00900c40030b5020030341c1000c42d1516422107807038a800c03102d4140c480c51300700d00803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 426903561 1250 426902311 426902327
    0x1030c0602071a1608160b0f0a020903060a020703020a1b0e010509040807060b010207091d1b21030418020901020d050f091903020d0f1b0f03140f0607 66
    0x100c0052198140002e81400c04159103211120185090741c0b0381302c400a0702401c000c88952080c0c50102c1c040008209804802e2180f40030325114450704041841c01c00e07061801d204008101c0c080480c0104032118455601082c0c555100700d2005005840d0401410200d18201c0240c100500500822000602881480f2084030880381e07554028402030380c880040c4900489c050f9002419402c091083c0400a04c41e41c0000c2c0017440e040c41180c00081d0748e040040241d0305081d00d4460408500c0c00060307040d41e02800940a008000901072042c510b40c00080303965544540e11507010346c1c2070010307902c1c20f01c44148101c1e001064540e9641d014504031810140003507105803034072805441040f0001800da4051004da89030000791444090410006e402401902120401d640401a02078140400143d507151100114603004041540010209182200903094050b1248049a401e078408101031850356600500f500e900295988112800d050754504d411940314008102e4007440042081d4283e2107018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 426904811 1250 426903561 426903569
    0x522080405041112160504050103020c161706060301020a1403190f0209010809060105030d05090f06121b04030b0c0a12060806090706230c0708060705130503010b0a09051e01030c 78
    0x40903400c0c1e04d407003410007407540d485c0070b8075008100c1c00c3c0001c0280d980a980a0801c442c40707e825151509405070750500060f080350009500c500c007005260804410070001264001400e400840c60070744619001341c44001c8941e440b4141c00c00000008081a03d075217040303800000d480303405119030481d88078581c0194000012450001ea55000080c0d55103800142142c126040540605074000c64288116058bd212400998001e444592a41d40d141c07901002001c1d0742128282039051400e060003a4012803508004417600004103200038408100b1030728206401402480006c0d41e00d643d81541a140d240c100389010350401d02d420000a181440801c0c054410343c0b40c0800d44d00e050391208420fa8510f0381c103440c0ca1002c0e10150304540381a4000d84010b060303030552003007244d062698440209240000c02c8400400140e400310b01c61121800c08149080030344001c9000384141240b4002040c81840c1c14880d0302c8540d901e440104a03501c40e00350b4603502c0794014001c0200c0960f124148000103a0141c03107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 426906061 1250 426904811 426904837
    0x40c020f160311010f0c12140705060a0e06070e06030411090f0f07030216062a0504080601060c0f240e030318190308100b0a0806120105220804050411 66
    0x388445281d88109107003180c5d1804c0b521004240b89141c0c51f0021604620b90380310040c4101802038280c1e000015016040082c0303d540101200c0c40c0c200c540c0c509481c80c581b664072080e4048818440902d400456040e21044280c508641340d507182d0800741000451040d845800c2040503090000000707241115900c00d04446031b548009480308001113040f0f21800100b0078540c41000100c0000a40030342120420040f80308205001150310035200350000c030309800f2203021840c0000c081114031400d101c002d0051485040030101c40040f6210603150102e041030013049292280c2da1100c0340107074840203c94030f21905030704200105804a515640c2d0744103540e18102c10071449400c58031701500107016048802c000c011a4003194055a09443c5400c0c06405c0e022008152000807405001d04400fa0015072040d80e181041400c2407001d2003d007000f048070820499050104200a200ca03400c40303039a980c0c0780c1c00c00314104da81d4582407441d00c1c3d02541d0059079110b420140341030708401c001d0002e084403401e520 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 426907311 1250 426906061 426906083
    0x9060209040c140702061303080316030b03061611010f061502070e04110d060216240e120d02040503030409060f0f12060e01020c060403020706031118040c020f1603 72
    0x804180d0f030b041950f07155807411071800c00c040001800d01e00007a04612858018810300182c42e5920101560001ca07041458802e9642052207001d80c140144050000c013900504030505082608201584ac17025040042c8109080150003210b400d52214504448500b0b04014050b2540302e249044840801080018440e1541c0841c448086481c0310b401703242e120b1100411000c0306400c0c015070000102e82610003a07424041b080c403d80a48100700c00715441094440030b40d1820104104900c541032102000b224507120804100c0a00001d0340030008a41100c20b070344440c1c0b4080d8810280c0b03c0c13600141d406000c04100000c100b140d80c3c001c102a41d0300341406100180d15101c982c000314149209070a9000c0d400e60b071007804204154460a110305442c070000d4130b82880f0b284050b1600d4001d84003100180d001200c10080c1c03951502c0741c0072440c1c2c8105404d40ca0209103e014071116422981030034401d030340d42e400c40c548150080060703407030403400002640d0420700c00c070000c0b02d040003a91200303880244440c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 426908561 1250 426907311 426907331
    0x90606090b0f0702040c090e040501050109050a2315060415020c061819031202061801060609030b06010314010e0105210a0b0615040b0c07080d052b0906020904 70
    0x181040e2400ca91003454110b0621a0f15001c00000e04000d070400740c14000c4d0500c0c08181d40c20508505442507019500100303065150000403411208020b250b801d61516040e8000c82210381c3d8000c40340e12858100054890b03440301d407070003070b14641c0305195030f503114000040c002400c0320001e450905030f180580030f6030301d5032110382d05210703c5101e07500b031170031202107011241d111504e8205038050600003160710030142c2a41326550000740b0104084480e015a010300d04100c030011914012500110905d00240110ba250050103010301d50a070000031b0014480e800015030310b910030340c08502620700992100f055942e4404100c5800d61080c040e0310b0140b1412400b441d0440070cc241c196082c42c44807402000b000e0103540ba01c0741240000741c03101e540b100e44000701d042c01a0030300c0064005408140181c1c1d40c0c03503403081c00359840c040840c1c0c4508555048a5450b4151035003000658070402e180100c100d070701455001003542a100c1d03c1b800d140107607241030111018423030140d0291803a0481074900f00114991 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 426909811 1250 426908561 426908579
    0x8070506090a09020d180f0c052d03011119090503031201090914160e0f06010c0b0a0b1e090702210a050c030f0306031501050d062409060609 62
    0x20301c0c60078640001162204000c0c9000356402014880502400014911100e0846185002581e04151111691300f0700300418411500c48032401000d045032104568943c01e80d10b000711a006215005001411082900182c1c500b0b400188101c042c0e502083c0c1e17944034141e08001010440d980d540e000844c0e004020906041c004120f034100820050481007a030b190003200d001800f12124100c821b100c40291250740c01c0810008280090708044007800740340c1c03c040f251595808010302c03072604601d01c5c80c1400f0103030b6005052891400c1d001a00c103002651880c40000140405200c529000806610341058140020950400c0403804541c094060b849080e8100e99826248414038800010040880b14501e02c41d4020301c4901c5103070818a083c025505019801c40d004801c41c51010f40001040002c41d14040c050251803460038a54031245506003404104d42d004239030f200820841d07644080448040d040c1c1ca140708868089240a00031680720103854000e404184100300220f10710884c0032881000b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 426911061 1250 426909811 426909817
    0x615090e07061701120201110d03270213200307090617070e190317040f06020f0d050904020405030a050d1d01081f0e07030c090b07020d0f0519060608070506 69
    0x6024494015690924018070308017000480704905010501ca860700c40c28400340511490440c42d51000100c22500a2a01c025035029440400580e0300300d22a03900166107640e0718080590081100141203081038186030203c0c506464030a904030004420030150307035444640390065070300070303996000e4052080041c0c689084003034458501140d240c200f6030300c20f402d04a2036440d0380001d100300c0914581d607079100c840e5a12003103030503a40301c0d81c40042d0510041d1800c07445c007001480144014150100004005529084080c01307840c10424001070142c07441c1c0d00c5805490190500a050311400006c5d450029500c02505024001003185041c0001c8201003040108078000e406846101050392a4502040a1241d4115290a01c1541c0101048801a820105100d82032a440000d41004000c00191568440b54040180c0c5401003250100588401d40041030441e0f000300001c1c0448024030301641030440e00d0504070005114016403000f40805038201008607040c2d40252220640c80d00280a4148 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 426912311 1250 426911061 426911087
    0x2703011404020f090a020f0c0604051c0503130c05040f1d1f050406020d0507090611030f070213270b15181803040603020d14010f050d0615090e0706 65
    0xc0300032415820741e0130024111540720f0340c0d030380005140c5410f04400f900950400c440b02d403000e80c000001c020130814100589184c1d43d4180d5025070b150480b014000341140b10007844200125558500b03801040030002c5001d02600303005009010400d0315809a1008003000c90010314844039083c82070142c40004900002c0700035a035002d0f10308681c903011420029040c0030340115a51942000750404000480c403503140582c030f9540d03a0250041c0b500c0c030028040e40c8462130700140c2d0b8101300400f0700020f000008a030440380d81a5601d192405181259100a041d000c62220920342c121003c030b0512410401c94881080c89a403032803296884442e0200c0c646441d00c40795135000310303002d05010024503007070b0917256004030040f5140f01c0248500c40c4503400e582281d03002502094000c5080d144a1a081c01841080812840070484542c541a8640c904810030300c5800d0044024082940c144002c4e0781020b080104001409030000f9951031403a0014800b00c10100400c1c011180c0208030303280b08010141c0c3c00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 426913561 1250 426912311 426912319
    0x220c1106060f010807030c05040e0705191704020d230706120203011d04080f04060e01030507030b0108041421040e06030a03120f022101080105010b0901020a08030606270301140402 79
    0x103681d45030701540100883d009030020700c12300340000101c2702642c0684900c02c0400350703038141e241c0c51040c00184649030300880d600140800c0100b0303109486200c0d810185d000c0e070121041112884581004180718442e2909401003400410680c0d4520300005698011100e01c0c3d501c001040d50030204e46400c034082809040382c00080380300c07800b150252000391b05030080d001e002400e282c00c1c00c061030f15404da40141d0200c0085498409140304a68040c443c082d40501c5a04090201e01c1c0088002422224000c000410b03c4050303040c5600350100411022100305000202c0d503c84201c141003200aa800501c140780284007080000b03140740c01d001c40e90f90340140d415114120a5000000143c0182020020921030070350f013400000d02000c0504480100d5101001c6d1203111035041c0640c444c01c0d200143c01c020305101d003c00001c0c0c10390740d001a86044040c3c100c4e0b0003580f20784400c00002d00c4c61040744100404c201c3d00741d080c100251400311900f503d841044000f0425140300c0102554075050403038000e940 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 426914811 1250 426913561 426913577
    0xc03050103110a080309060a020c0a03030e04060e070206040b100807031104150b07060209010e0a030b0a0e010605030c0409050111070503030f0f06010c110a03021e0f091302220c1106060f01 83
    0x1541070030002343c41c0005050042ea02c82d01100000724a032484aa070094000a5112061100600300b0340303d0303c1c001c0c029501e6903840c1850f0041000c0e55a20000c0c02c001c0c54040c484e00098560010f40407000301900c001c0c0140c070601030b078a04150f0007004062055620440c1380203400002280c40e40c404c1400c0f5001d1030f001a06000f40c50b1142c030000c0d04862040c5052003603042ca0a4a199202c1c03941d080a540311358121615824280d0010044520105102c20580e140039024080d6581c0010551070a8500311004103420007903140c2503014200ca0b444240d500d00010901e04100039006c4051481018008068075056403840c45102410300b040c0e5103035022403008200400460f5a0300108154080007400d00c40b045540d950100340304040b90400080c5a05000c0110401d038a040c0115460000088444519070705009110001140101c0c00081c4994082c101000501d01c6e54041e0502c44000e04500304480f883c440d4000d8040c81c0541d000007280d01480700042c2507132501310040301c06120184e449000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 426916061 1250 426914811 426914827
    0xa0e06070209060607051c051803120306041d0a0f0317040308060d1110030209040c050f0306240f03040c0b070c0e070219110f180a0207150c03050103110a0803 70
    0x2e2540c5c44088252240e018207003018021003d010821012024150780d001c2e0355031527201800038402d50a2000600c40e410800340003186070801c1c0300340c03500143c0440c0d001030741039810024248140000303140440d8500501010a081c0f01c0f1401c8002c1c000d600a03124541ca0000c1620285881c20040350000c003c20b1010b800b2950301d050025100c030344148601115151100c0c100001095100040706400029030002422915418140500300030036405040c21404e0558184400c11540401040079004005600300d80001594074041e201014034a200701c5607941e06144211103142e44104c0b000d03204201325040029030051075008a40d20690055240c1129a08114034145a100003800c00011881988a0b02608100d4203591420b81403090b520110444600710a001c2504591280c09106e130221081100074150704040386a0300c889591001a614252890f1020000450009810368145498000040705030541d0049060ba406141c8400c0a010f210040024180b441c0c0100b00043e0404d210b02c1d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 426917311 1250 426916061 426916069
    0x302090f04240b0301150f060306060c06090302010b06030f0105041104050d03030902030f07090f0f0203010f0b0d1d0109061a010f0e0d080f0a030509070609180f0e030a0e0607020906 80
    0x101e0300c40810b0000c1400301c54507002a0942d13408941010305222010340401c030010907506260010843c6050501c5041d14040010b8101c20708a400604441d03140c641c074001b018403c0d800035510900080030b464685c01d0078402120320510034001c060269240001850000c1d1010050b50300720b507001171840b00c41c40c0313407954100c010340113000003280c15200d804200104c1200601800006c0c007400e2a0020b1203c051902d01c9003554071034074406111500c100014402c00349800c51490503100003540d415514190f89440e580101f13100d0f4007605910413110704080900f0010740200307141c0350081005100f403550f03101b00003842083d00100715011410b650240610701d4010320a003002c51000a000080700c0c052500c076888141e100071850516880001100c0d0182501072180d190041d1880d40240390040c201280900054164021000700b104016484030641c0190f4015140d0081c80744000e100300581d03512301d55a6900007507901d10105000301d50110349402c162094600658000388650401e490342e1040c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 426918561 1250 426917311 426917363
    0x130c05011706010c0f0b0c0c01050a0e03070b1b031503060a060b18040e060901140903030618190609060501030c110303060409050a0501020a020a020108010b0a0e0f0a0801090506010302090f04 84
    0x1203640b0480c2172418004200c02d40103580c03103a0351068011340d43d04058407056003101c1c00100f4040f00e081c94035a29100e9604000291400a94000801589178450170b0040c00400c5510502a88110000081000c00000c1c3e407854900008107600f215044d0f21660b8034507094a6180c0526000c0d82c0044c400015020b4441c0d05080140401600c0001c16050344c1458900301380003290701103116911010f41c03800d580d0b030100c03000382d01421841c091400c0d420072200041c0c0344180c00c5882280320091502103040401e8841822840c68840c038000c021003580c0340401c1000c0c0c40c1c1031090700d0200f442c0c083d03160001401a00103200d03c1140b20055441c0da5911410080201032049040c0c603640308081c249400502c003403000f00304e01d01da00e40040047c2c680510005218040c16005082c0068083c040310f041c0540012084c5203041c82201d03484a1000c6440106000c052240e00c03032100d542c01e000c00c50050150208607070b41038a000341c400c2c2030a83e50b5240c1d488882c40c400d450040015450300c1003079405480210385 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 426919811 1250 426918561 426918563
    0xd1409060906041d010b040311010c171b060903070c1701090c030503070c05041b080c0c0703210509030a240c031b02240a02070b130c05011706010c 65
    0x1105080040901c0030401c150040d801c5566070661a42c0c1c0c0036040111002660300500d28004010b18044c00d580e1503404186400c6241c80c148241150340c82c2c10400581122124407040882030f0391600c071481034824828190728018209401104003150821a010049501032078000200140d0203103400c210340c2401d0031042805107995a42d40700d901c001021054840011806a0015915450315042810036001c6035401640f045140c503401010041d50800e401422400500f08541c0b540d41d29000d0a0140c0f103001140b41182c00340c01c801008200c0b4021601d5084008450030b50000d1010400039181031140326201a81940018481000112a07038102c03102c100d0600c0508040340d8001e80c450b8203550142003040c02091720342054980d18110b044000700e80b0a145e10060401c040c1c60f5116481364503101400380c105021101c001214070a6540440e085940d00c0b11482403240b0b407400e0030048044102d0800c40d164003404400041541c442c03030500c48002c940d403108041c60740741e44006403101c10060300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 426921061 1250 426919811 426919819
    0x501230309030c03030112120e010c0618050102160c0b0702031e010f02070606080c0f0603060d17040617090105090d0c4101090507060305070908070b0702040e0d1409 73
    0x12041c1101c1d40d0a00c0030f0350081010013840481f5082914014151041a40d2100c04109001c01c49404c00e030f902200c1f090415803c18070000388850f286020900441186201410940c0001200c248503130004002000c42402240c0c174003146919260192100c0c410b00c8000703989a801801d030b100042c141098081c020a43d0480001402c010b400c070918240d8114000980f8031540d560b008000e0100184a0070a00d60411a00103901100c007900068042c0006050a405058140c10384c00400ca00304c004815444c00d001e500d9900d0701d545003001000d00d0b0b264500d804071040d0780c1d0301040070700405000700d50040c207960f00038011080c40d1a100b122480c60781003095884170818400c0c1718003034010382c01a840110742414002e04452902d403203205480f000c0c1041100d26890440c03000c2c00b0030380c0420b803201520860316001c141519918000c598421302500b0108c0075020b6001f0024801c0030b101c0c000e00d2040e2007a10103002071180c42c1160b640311400000e000c1c010800304054245140d40500c014200540010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 426922311 1250 426921061 426921067
    0x705151b0a0f05070611010903020a030e04180f0c0608070e04150306020c061b09030a110103060b0d0c0315031a1b040e0109060e0405030d1107061b09050123030903 72
    0x2d102ea480c902030341141610765822503001804802e5010440309440d5143e40c00074858800b003603400940d02d00e11702a000d010843e200c1c00e00c1c0020340c4e032600861070b01d80101905801041460070191840d44a100003200c103260300d2074001500e28002c0302414400c851750f03140c1c400b0101300001444054840244180c0c90308402c46004400170301c072407000c7d20100c40060020909490040c43d0b9020301c4c0d5030001c005c110f0380000d01680c0c0700e44c0d0780000c480340100e50202429402c03101e5040184c0103003100f50000e159092010401a40755a810740c01042100c02d15a4181300b041d00b60000040b07180850b00001d400c0c08102a40344c1c6041c440450840d03005000000413030510b982424030020140c010b500b090380c80d80361503001000300c1c11b0140903000c00b038a44d554880c2000d090641c0c603141d803440b80c000f035a0003098488012508ae4a8450180e8204c1030304843d0a10640081000d0a00781c8540b125000d400f0400264020400794401e511100406440d0314072492a10100b881000e416080201340c0752040c8010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 426923561 1250 426922311 426922313
    0x90507030f12090b0c0d11010b15030a05060108011401080403110f0c15040b031303030b1926120f040302120703260f0904140403050c0705151b0a 64
    0x114401c0c04540c080c48000e25003080b21000180041003a074422500d04500f40034522a00c0fa010031400302e03810040c10140001c400b52503440307003d00f000c8150598400d84041030700c04844602d100541c454955203204002d55511040103640d00c88007030040e002d06600c00380240007554040d0742c109800c02c0c02402c0050400c4100b6180300c0ca004050405040607800001502c01e090500324103c082e041311440c000383c245801c01422401c2404020290001c102c000785610080c180039901c160384510001d072144034202030324950405070041500c18105504040b940e4000030406103041a00e0f013944520142805840303084190072140c101104407a10f0800c20000040185d40f0400d1030040c54503664041c001072403175420154001d0100045600140f900015078101d08811042102c14404156882503103410140001c60014840000e400403804c620000f84402d00d50068098051210342004566110741c03a50140f003201700800401c00039445082c0a03403040300b80407200c1d5240301011340085840000007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 426924811 1250 426923561 426923573
    0xd050f0d0617070905091c05040b0d06050909010207020109031b0902161a042111060a0b13020702031908130b1809011512061509051206070c0609050703 67
    0x12580c000b0b0707800b10280d1000b09282400f40140b8000b02000368040101d40351820107152103840599401c200004d60501d0408154044c005132405002d0300121139881e0319860a00c1c200421042c01214410000103000a581560500855410507070695889180318079544e1100c4c4614940c0c80200044441450080b4000d00f49102500d91910fa40d0382118809000b400c003c0307411400e4641c0d044640f884501000f0101e0000201001603842e00d01ea01001034005103021550210700281b0b5581074017a41d802e12100c070078a42c0002c4580c100886111101c0041030b8113000032445a624000c1d016005201c580040d0fa400f4450180c110b0b01034420640303460b04602111144640035001088140c0c1d0100d03210718411406080503d01e220b0a5030501d02550403c120460005c1c004400c46040126809039003111030001d0304008028030b0003400002416802c04405840c4140600401d400780070340740b40d0795034030060010f0028003524440d00c0740080ba584a40350034024102d00c40c2c050710b180c403d1020020010384 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 426926061 1250 426924811 426924821
    0x1f0c0206060a0b120a1b170117060c0c0a150c09050301050907060c020f06030906100b07020604090f060915090510050f0613030f030e03010b0409110d0c030209010b04060f020303090d050f0d 83
    0x1003a5649410200e06850041c030058060b0052103480e001010f490160031000620f01d07400bd0b1340b9200d2140c4400d06280321515003104110020007019114007080e07444841c907006003407002425260454000c2d00e072014542286d800301c421b601d103503001ca00c0030030a00b8007811000742d509001400008120041c1c1000c07940c079910035994400c0341e1b03200d102005101d0248810107005015800c156030300d094031940014409002d14090340c490a40c0d01c1c4150b001450060303001100030314034000e007400a07902920900108001030300c03440307159504090018081040c203001203c16035800601c09007030700c9071034018041c03290480382030000024124440400805d882d0141c5040030b17881f903074800f02c180c1c400c0e00030b15094801848140e03020354244016000000d5441d5903450f8030f034606440c036004d2684a8149000710654a52020b5003100b010000401d0080009005206544958903480b08082403100c0403a030b2071204540f200d000380c20068030600e0720b9110b10020100c440d2000344050070719000f5207044080395 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 426927311 1250 426926061 426926111
    0x8070e01110318090108030906090402030a02070c030305090f030c1005030714041203170712020c03070818120d0e090a110d0b030f1609020c1f0c0206060a0b120a 71
    0x104500a044003031401c9604e25026010000c05982080d541d4004030f801801400c0c0d03200d108036004000920045c143c0d9040d00e6800d0b8124003c0700d400c5070b0b2410060700c04e511480f0401d00540c1c2034900104a800c0004021100c0a03002d000039054100416046807076410280c041020444401c031210001d940100180000d04241c45516140780c7e0701d0724020300300c160704030320000680540904001009800a01c8503007918215080075a4070400d0002450952150345e20040640078085401204a100c003984000d04a509032500d1468401c042103045e0b0b540c038101d0700b00001400c079880c47e40d0182822010281c000002c228041100201011503078402d401c03008000c80401d07a03692040080b0304d002c10010b10107075940d1001d0070044039000c9401490350820300440010507000140d1a5103650100034440980301e481e04015001ba91001041001d002002040d000603ca05404540b8602d84450a1412031301030200c4c140c941518407060a24000d4005c281c002c0342551030303141410840031401541c10a0b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 426928561 1250 426927311 426927337
    0x3090d091505030a0c030209030102040f051503060607030c02182e05210703061805010f1b081e2809050a02011202070f150b1008070e011103 62
    0x46000040c80d02245a000c8100816510350030036100d90054110380d002501040301003030194a5000c21340291107641d20701d581540c40040c0c0052652186040001542c0040340c0c0c1a206280c00c0141d1180d5004c04d540880c0d20080410001c0c000901640c944000580f02524603642c0201d540c5100020010488003a174001c80b035046488150103803120f10105510344040c1842c0524100000715490040301408101490110382d402548072004100001c025030744594140010789010510021000940c035080350290708041e0440038082203400b400b02070001801c814080d001d44c4003802c07584100041d280780c0d0308031103020440140361140a100c900c1800d00c580c6403040b41c41d010b1180e95610103480c1d00c20103081e00e41010080066000b0a141c2500c0b902441c1c410f8192010200440c001e201da00801002031182d1030144080118001080d0305200301041c0400a070310515060000d800004001300c00019001000501000d008541d4860441d00600d807401c03c0d11041030425203964000084803800c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 426929811 1250 426928561 426928573
    0x100305070e0103060e130507090203071e050403081206040905070b09190e06061308070f0e06180109110f03040c05030106060521070e1c02030610050a0510050f0309 72
    0x30154104502182100080c42d0811240303240015135045410040c04a9210f207170780410807030500400300250300103405400421950382c02c01000c00b4103a088040d00c00c40150300705013003940700c0700e0140050b130741201e40050585103080c2980000700c42c82d0300c0061086c0d610503650f945000104008200705d2000e05091039000d6643da002d9020020446021402108058410041401881c00f180c0b9140e030401001d40e00d560301e5aa5040c000070024403039800400301b6101c0d05400203565059000d0b0f82c8219060740c85d441c1036540381c40f401d11600800b100403044e4040134440c01009100380300d5000b8910f00703045880342801c140502d0040c0c078607644151001c0d95011800242803016240a11640004140c11f040c07191810a4030707400d0109200103a5500285070041000054131940151b540500c5450300403c9608944031585010084a03500c00d030903806441480001180554520208070545100402c015051850002080394081e0110f100382d00b006410f020316005040d03184091401040e19030050300f4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 426931061 1250 426929811 426929821
    0xf0a02070e0c0c030d020d09020315070305160e1509040603150605030304060f08040302070b0403050109050d02030301052b020a03290408070201110c030709020a2303070c030c02100305 81
    0xa03080c1c40c0a414441080d504100e0440741160000031544104409000580c86401840040d0028544910060f4241c020800c0c02e01c0e19800001850388101001e450800880e01c0d10049a107000255a02803004500101f50250203850402580c040300960b05800b1072610741d020000c50103541c1c04c0d40c011100d0002d00384030203c100c0b803140600c0300940426002541420301c1c010000f41f00c02c2d41000c0300024003261401050038036200b03200100c06007400006460351182c0da0702d003c500a08000300b040d141c42c0684032140060b54804001c880c100e4000501c5001c1c1c0301d0460004424007801041c4496242c100c5070034480c0180ca0b001340310801180244c41000070700720341004468803000800e0740320000c00e204808000008401006458207241c0a18050b4203420b058100d507884c0c1001011391603490f00c01d0400019000c802c84c0c004040070043e80d91080410844014002540c2d1031402620702562814000109214421003940344440d009280c9a124000d403034003c100c42d9011010450300203602c40d41005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 426932311 1250 426931061 426931079
    0x210507120c12030207030206070807020312030403030c0c0209010513020d110702030607020c2407140610080303040b0411150406050d0b06030402030c0f01050d02030f071709100c03020f0a0207 84
    0x20041c11003200c902c140c0c22495600035215440c41c00024418580454035600740300110007900c1030f1907400340403115494004182c6000c3d980086404500003410160452003e5200d1110b908541d82d000c2c5c6124281d9003000c04001524146a041e4440360f9400d0106040c080380e00e019101c4c0c1c6e000d40401d001d43c0d80d0000d005060602a000341f82000f50340c48440841d03821340f80c416500b868143c40014040055000450125407881200c0010748080c101c02c0c1c9043c010940812030500030000668401c0f561541c1c8d801003500ea00040f140a0280251640040e011991503030048640c12401451455841804030720000310360002d4014800292000c19241c150314403a1084a2840500b2034849055140c6980042d55800444c0c05403800369201800c02c040d140d00071000d079400d00c4143c000543d1031f464500c40140e0a4401207079110b00082c06105070f642d05c01c09000d201d03802521f074007001e007100c40503804000c005000303010120001c040c1e003040f0b00c02e04011b1a00c090300c4180b055170301406071700703280c05481 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 426933561 1250 426932311 426932333
    0x7150221191409160609030f030c050d110105070e060d0e010605060d0c02060601030603120e19271103010e130c03050c040f06080a020d1a010602060f0901021321050712 74
    0x4124042c4c2e9078410700080b5000414003044a5102148600c14440751070100c4096004d400020302500c201c0d40611100c5810003406c100d01103d0100801603980c0707141c02102c0300c950305d1040d1604a4020404004411007642114504081100012404555910105040794002529070000c0b5030346850004c640d5a041c402260018000d02e0b0510505080d03071160300c81507604a05450501840440742991925945048003441d811140200d906950391131380c2d420310070790012580b02e0010000300d800720f204130b4a02c11245d41d520843c0610b41107a0030101427240d4084094900d10320300e01880d0103100041c07906001907018510803400b0b0b01400c4411814041500c561107032580000c0c0c01c0000c10701020303400150440c00d45070111881c4241602c141000f284410100c01454004400ca00003c90302680000714140179001047c4454a0f45d62089003003800c0380182102d04d03401c51180d5004000c40d81c2540403c1c0412001030404a01d840c84568400c0d11b84000c1e07a00600f4a11103904008051180d00001c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 426934811 1250 426933561 426933583
    0x405010b1503090f060f0a0c2a03080f0c0f0f070203030703170702060601020d0e01110307030e010f0c020f010807020f060108010615020303160c05031204060207150221191409 77
    0x1c01c0b11b410004100c05c1850002000181220782e40d80032060070910039015a821004d040b038001070190488041c2c074423031098a40c4240c0201d4003040104010a0083c00ba2620800d0610310141c200541c407100903602d07a01c016062180c5a00600c600c2c03002d03907000d200409032030f40300f500c0388040441d0700740a1400b1910000c02c1c260564200d0020403100381d0b000700c3c0220b5903001d5032620644010001006903204007140109071010312000c2070319800c0542041a440031450240ca0300d00480150240c01c448017040003900940114449e01c01140c1540952004c6401c18410f0058a4008580400491920f07800b40e0085045a45545080280c5104000b408506542d2480030314030b185410280070314028681005d03001049642d818030000c1c08414070130b444010b000b040e038038001401c250415002a401100080e11654419500007e110740036100b01c503c1411411510090980f081d0850591124014400880c0c851488140f402480a03031040d01d40c03102443d84414a1400d01c514071070301e0900f6400e2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 426936061 1250 426934811 426934813
    0xf09060f080309090711070f180b0d170304060902091003110303070209130807050615090610021506040b040e0312070e03060c07240e2e050405010b1503090f 69
    0x20804080307403582150203034064090b08080034031b2920b00150394a00702195210512031070b80004042600e0150101c0400a14001581070250f00008070030400c07204d00d2418010500040d40035181d01812032003000d503078000d0203403000050500c207039000700d204d001d02110402070081d00c0c01014400c20960003086a2903500560007103083c2801c541c00304407504005805003e00000d95901c103010804d464040f240059400030550b0010304198030100310742404041c0052158207001c0000e0310f50304041c43d180d22154825030041104801900c4145a1100003404c81600305464104041c0c0603125405100b100c10403110045a54001d030111815982c00060105410000342514616a66800040039078002103001c54890307803404140340c03019000580d041c8044a21703100400018900c44151301101310070507030900755054007420b00e00440310700c103052039100c1d103200c0000d0b500340f201a604e80c040c07684181700e2000007c904104500161a03075801c000490070740c4000100b001210541030004003240c00c0010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 426937311 1250 426936061 426936067
    0x60f1b080c0a090b0c0f0a1b060206040c1e03020a0b0403060f020408060f19090c0824070f050d0603080418050402060a030c0302070f0c05041a13020906040f09060f0803 74
    0x1000041c6a00703d2485080d8030110b0102c0d06440d94a0280656103800254104039a420042d62802030b20b12070086200d090048002000013841c68004a082840345501460001c081400c0900c03140000b03200900440680a040c14044016180c10720124041e21a0600054031249989440380a031040d1503c00c1c001d1a00502040000840c005041508881880c1d6021155610121002d55000a14003290800e604211482041c088450b10310f0302918416025030b96401303190b001c207104514100590002c0404800e000070700540c403c0000285043d901d07d00585007840e551000350644040b9013080e02d62000004040143d0445007142400f0201e0b01e110900c524138143e0000344c0c0d030f40105081c120a040d118031800c2017443c442d6040301c5006030b015404161201090030200c0b0201200e0240c40c2c001c42c903000b2294411001450464842ca400900388c0c0c40100e02e051342e00b8040d40000f140b6a400c104140400305400c2200090400a4591034a00282c140d10f00401c0408110f440e5100c0e0403240c100b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 426938561 1250 426937311 426937327
    0xa0e03041212170a02030f06010e030a0308130203030c0c0405090d09060e0d050d02062403070b36010905040c02100e0c1e04061d13060f1b080c 63
    0x51210441007a0010080303040590010015210762041000712809100300c24100210b1344003640c080d50280b0031601e801441030388d4000055804d40349144c4030f00d9055200d01074a00000340f25a03c0103601c82c0d0504900203806901d60301091558100c990080480d8115048220150074988a10b80c1c0c05282e1100074800a4420000a4011481d50207040d08110710300c1ca000315103071030300362800000d9940f180c21102c014010724002510f034881916414039104503600c4001034454070640d1000122001405441d00d40d10f4544002d41540c400d90402d8146510880c2032181c0d8490240c6075449001d00c000d800c1108503401c000107021010310340003240704510b030103083d00c9101d80c0001c088107410910a030018805003158600d80c40e10501c00c69a0703a0050b45040703070700ca030300c503011540443c80300303041e1418440341da12101459200d11400030344481c1e102400b00080c0b0300508541d00e484d5064062200041d2284a018042064a10f500c41c0100c44545003902c400500354403600c0c46905c00004407415080c0000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 426939811 1250 426938561 426938579
    0x4050c0d0c0603020d020417010b0a0b04050307051215041b0f06050306220c050a0e120c090709120311100e1905122b0509280212060a0e0304 62
    0x1d50b004100c20140d000c10324602d0002d080d8121805060000340000041104c0248180030780f448034a034902510100341c00141e044030800641d01595030080107088603906000c01d0144c2c0c800303100303900ca400e485a9294092201e80d0200701d03a0045004402100e0292a2040f85000c2072541e6480340511002c00303c0100310300c6511805503500702c035040761510421040d03e00024400200c403144a04421b01e441d405818040e001802000e00016544410485007442e13010401108001000c0d45103036000340e50580c416180000805601022500382055219108e124800e0f42c502902801c4000c00e502107107109200d6070400044030021003610042c0001464441101d40b9a403141c2855203884244104040c1003140030300071a03988010360144aa00c64020114841e584c1d54111403810510740804480d05c500c80990141910814200000300382144049040a800d2064604511740311400b0f44c0780b110041c0e075103610400d114041d02c8001c0005007030201202c0c1c2181c22140c2d0030003166104000801c11100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 426941061 1250 426939811 426939833
    0x21030e1e010224040f020f100509190302090a1503080c01050a0e0a0f030f0207180b1203030702300d050406150f09111605010606090f051c02010e10050304050c0d 71
    0x15004e0810f0071201c2c05440800c0747d00d60003400e060b41c8402c0c144001d01c0f08a500001410a0313a50440318044905038242280d02c8421306400007a4004008000051000c03d00d034018045103d40035000741c03410743d620b4880f02519004014100c60702c0c1d4403001800a600c1850107804d60020b01035014000b00c051310303502e8501607c0d81c0c03100241842903042c045171405009100540080c02c00d80403400104c1c500754840c0c1e005010700e050a9118108910b21200103e02c0001901c1c800c0040760014082e64100007440355280c05c0e140e030901410a44a0541c01c3d00c00d84034400342c01c0101c000712000c2200d0030203280030f5080c0c4215407800c41c600150302d18200140c0f20046414411944042c2000551441d21400c80003d48500d40c03141c0c0c1c00c00310403215041000310540c450f004440c1c4030341d14a11400c0e224102034a41441c07605c540c641c403025240091501c0c489807071210f111181b050400c1901401e4148c045000070840e1180900032440c003100304414440140980003e0120171285102c03209166964065090 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 426942311 1250 426941061 426941063
    0x5030409061e0b0d1a06040909050f16090b03010f020d090b060306060f190f03030903030311040509070f021c0314011703031f030803010e0106030c080121030e1e01022404 75
    0x7a48450461017140c42c2e6072a50184034a000d04034554442d118132541001e441501405c50b0188940d46c80740c503008c0404188584840c601745d80c0b034405245812a554054510601115807555884400c07584200710b03813000b410916444e2a01149801c0da072308061405440081056010f42c0002040105a645d000b05a44d250401110091410010740c44d008615010640140c654419a0b02d000300034150401e440b44101c1b031281e6014002c03007004c007804020f00d00940c40f031190820a0381d80401d0945000c4c0d851400141403920447e01060100307044120019296400000800d583d0001c0e40040101da464141c0500301e03611455500310090300466030b491000808540c000501d0b1444c89060303212003010b401c011500107103a645c407544c44840100d8082340038404c0ea004a07286c03400050700b03903024901d841c0c1203510003c1004c6000848000e00d5907807007a280c50450400c8070b062085403885c0d564041034bc5071a1041003901d950440c908001920b004a106d01c048040004082c418801d030b100f08103102d50007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 426943561 1250 426942311 426942337
    0x60f05040e1005031b0f2101020a0207051f08070807120f0c1b0803040b0916030b06040605030609120a0302120109020c0d090315090f020907170c0f031b040305030409061e0b 76
    0x1d020140040380b9114850045a40e0239400040c101e50041c2d0b000400009071201114101c1091480481a081c020482c88100011542d8103000940700c80c05058610340c000c0b154200801038142041c040c0d022902c11109050b0042da50b606015241540401c1403442c0340c1810b00743c2c0d4140e000e9030303c4000180c04010401070288054a001400803036080c06044a18825405440c0b049500c910380141920740440c0c0c0070703004901d050000280d9250000c8c3d030030300a42c10301e0b002d04540a80b26141510a6000030384441c1896001c0010000e1202000305940c002c01c0d45620058442d90ac40e0f42142c02c003180180007004210980d8002d1010502c6200b4102c0c103c4403030302d80000c0c00403452500400315840c0a03c040d5200201da000c00c0031a5811900004440041c8011829180e50f5071200b0850b9004610090716071120074000292078140c4203045503440c0506810081c2040d60302c0d501e581c80d59015411000f111a00e42508104030700740702c0ca8240b168042e09010b070712524140309401c0001c0c01807040401c26 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 426944811 1250 426943561 426943579
    0x6090602101512030203040302010e0a12022b030e03071a0d020711062209020412060506030c030601120501113612030a0e06070c060f05040e1005031b0f 67
    0x4002c40b240d44020050658031010184040541400381d00c0b5080703844260301060070100484110301c2e0218078501581c0c4940d030103205c0d0030070035000d0004250400d030340c4681240c80750456805c8100b94203c06a11640b00e50b44038409501800203060401290703500260170381c06070140691001c1500740c1901c8000c1240354005803a0405402c242c0c10035140906110b40010703000401c0e40b080c2c1100710200c242601c01c4065180100d0340e0710041340492143d4410a452244880c03448000580c80b03401454110b00c0c0102100d070240c690400013800c1800070380c4103408407180c44c5200000c01000f8041e1038100c2440b0320340f040c00c025513102501c0400640280c9001411003501409560642e108002d01030200d0243c01c070b01d400c0e07040c20051643c0b80d00000f800380118003a801c04564616100c0110764100780e00c900c9135801a0b262480c141d4030346440440d4807040c803500b40404a00f4110292005210704814495503281c50b01c2c0c041031500f4100e0b942d0000c26900d69560700c081d076541300c0210790340d59960f041d546001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 426946061 1250 426944811 426944831
    0xc02062709060d1205041e15141605010e0607080702070e0702060f072309041107080708090a0b0f0a1412010b0f0f040f06030501060503041104090303020d020a0c0c0609060210 77
    0x6131445950000d400c100c9407403c0c1f90880b120140c0303041c01038604098803a1601d41c00c800060329104c50360300da002c3c2005010443c42101c4002c0b400342002d50f501c1103001040010140c48540d05045048405000043c00c0d802000789059040090400901014500091070b04000800070346a200003417143c989207030600c003c40c07103652041011407400700410b102c0c0311f40c05003040ba40290f5035001c0310f0341c24491801d01e9070b2032981003a50f200f02c90009030b10040040ca46001a80c618010750840180c50f54000c4280000090610f0380a004050304e80d501d031551642c8843d0300d08041c101c22030800041300090300c140440e9500c0c001c1e84181d541520060030b081d13074403215030800b10542449007241f1000c4c010408900020701e54a0311341080d00340c03211501c0901c0243e0f01e4035400c40d0103000031280a85020503e0f04070304018105640101a918081e240c00340c94241140e010200b6130b80481030010000360b019000105002403001c3c181d01802e45890401e1910349016402590356040b80002c045d42a540e142c860 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 426947311 1250 426946061 426946067
    0x50d080421050604030e010f0f050d0c0e100e09280b0f060f03190902100507060902040e06090d1803021c0203011103011403070b0f0a0c02062709060d12 67
    0x84078441d482001c850503480d0030300c4c0003000e00510000780c901086d00380d048004418000c1500e12074078145035a036107051610007a680310242c401c4494907814450440e108c48010b407151702102080c0c00032500c61442542c500d030b040c40030105000b0f200012041e074000c40890341303680700c1071154810b03e2200340c00715a00c80400002030403142d0840409a2025000038940a007104803000f441c42400a00b850f030390030364050900c0d401034a330b00c03010007913014181420f00b02d100c90007040500412800b800000492000383e60103d0101e44a08110841c2540b100042100340c00c010000401480f10303e240000c80c0c24041110504039451a001c000e1046501c0000c1d8034035a81c0e00a03202c00d030550000c000788806945421102e2403079000b03008180041e10751300c100311118100010020120b405102a45240281c0344581440a4101c040818100919000d4840140e40e0300405403220f8280c0700507054000309001c0842c026900c51900b5103000701480c0341000059540c540d119001150061207440450070416011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 426948561 1250 426947311 426947369
    0x15090f081b06070c2103030501080607020a0f03030e1e06150a15020c060711030708030406080115031b0807091a0301030b06120f011a010201051b09030703081909050d0804 75
    0x60350480d45e00080a40200305d24400500c07080e07000762030422a1317980362a06980c8030743d022114500986e001005001c0010f60940075008400c0c02131900180350030307202c00e09074140204804000110001209d881450941c2031059a812058643d8002c8400d02184c0220320a00814480c04400c01048444840868002d201e8a20260401007120795501c0952500010002e4840a0303c0d0292088010200720280004115420b80f074243d214100316038a841205400700d032401100d60201910742d07a000c108800d00700c0100c2e00c8101d00d074031885203505e070860380140102610345c0503003192021100311140700ca14110442c0d0540740c000009004e00d54a000c0801c851680550b4003104601c1800e08091a41e44190311140b09000b070313140300200402c08013004900b0307240c081d18046104500689100c0c0202c42e0034004100b0290302900b500d918036a07071b44442e01030b500b01e8201902c2802800134049421640305542c0d001038101210500c84080c583e8489400302e00560040c045018260300d003c11a01c083c0d5141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 426949811 1250 426948561 426948569
    0x21c0203070b180d020303090c061b0303091b060a09032603010b0301030c0603020c0c21030714190519060f06030807050c06040510080c0415090f081b06070c 69
    0x10066040c030546030f0300c00200c9110000700c0b41c002d000025640300d201200716402684a5002480c881ca80c00041180303e80c40f01480b03000a01409103e541154030a00103540301d444451f01410408180040001c0c2c15042440007074443c0801f0030101f00842c0d00401c4410a0302e40001d14805243c014040c004020300c0c0b9500340300c144403404000010826080c40045042c0e83c0b1030f14041144940c0c804040e01680590b02c1d01000c141c2103c0642c00391814454a42504031009031101c8100040028002e829079008a0b02600c40c034105002107042c440e401c11511403900c0b590908400c90f01581d0701c0d0700d601d6484043c1600031041c40750381c801080c030240f1340140102c68482c078400c0060554a151101141d8030060089401c1d00503c00f2214051400c83d0a44003110f001070311114180a000704215040c65004152000064041c400803e000c0c881078050032010780652075040e041030810300c05000d542c2c85a0700ca60160b5000511600e40c2148207031501c1980481503441c180c490b0564035000d0204085608 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 426951061 1250 426949811 426949823
    0x6050408041a07060b030304051e030109060507110606120a030f0203071e060507031514270f100f060509122a150405360103120f021c020307 62
    0x1041c008120b201004166882c0301c0c2204001400c071761000c1c140c90340214410740354441e81c14000840c840360101041c1c5807420000340001081e500c42d64605003102c400b17035801c0300020b41c0e180c00c04205440402001ea0880c00460b600016940c40c401d05540d0303484480d10007010404100000310420303000b00280e810755076102d01d0007940305103440801c40517601c0450090703d0160400003c50000360080c8942d460720071051184110480c1400c0304c0c403c0600d204c07885550010360344510108002d58031400c40c5d00b001300f850024207490400c410b06078007900d009451311072251850700081007500d0301120300740d080f80d4dd1402d14136212006031001401000c90980d00e441d00d8010030500d0152900810304105141801c0070150003003c40140c01d00c840e10109412074406e07007400b00810b21a43c90001d00c19107070303a030b8040c8000b41c00c5d42d207280100c982c0b84800c00750b001c40004004014070801012851000c071241e541c1c40c140300e00b001c001c0d60013075449927080e10300f80c40305124008038001a0f1080c401c440c02c90381c01c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 426952311 1250 426951061 426951089
    0xf0602031c0b18092a0f0f010e15040603050117030409090c12050d03050c07021509040b06070506040201080c090108060904170a0207080d050408070e1509040807030305070206010b070605040804 85
    0x5000300d62900c0e126038002c1d1132481740e421080803001c200300400d150308801030508098108444c2c2881070301c2c000340001a041c0600015980300c1a40c6a440740c0c03040a011004082c1c0741c519000015040d5001a0081c0e040515408040c0322402400001c0e00e0032100100008505062941000390611a8641201480c0c806c0c80b4100300c00c1c40303c0081e040b5101e003040d40d02080b107580d410469880500851400a502000f0001036040303408684018240c560401000041d43c030000d40d0004d04030b40d008400884458003c0c1c070400040d9a080018194040b4812400c1c038540045140003e150403c001c02ea58400c0c26458081400d100d201c450156402c411802d500d60b4403188010065919801c510511003544102915050300307034411019981160071110050040c0c80c00c041c08441e05400041c0911030211a401c510300480e5038000c0610300590107980016500d4046040040603164000d0203c0c0944d071004004000540900e011640b40b80c0e040301c400625a203075441c2c40c550710b2203154488205d441501c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 426953561 1250 426952311 426952321
    0x40c0b03130201020d0801080334050a0c090b060708030a0f0f150504060e27060f07110106081c02030d1109090907180b0301140703060f0602031c0b18 66
    0x708a400c0c0e514001d800b105c0d6070b5a4646001c40c0c0020302405456043e40051000b102c500c0341454001c0c12813140c10307188904000510b03000e03941819103031800350f440c0d44c8003200e043d040c0a1000b411102500ea101d40503c4042030030000b0408511940d00010945840080044c42d4a046940701d04400141484140440d4940030340d010081e094032540c0f00c00407a11598009418503084c4904411546003444510095503a403944104c00b81c001c409580600304201c103000201e87c42032000c24402c8a94010442131810541d10080024410074032200c00b0b689022002d00c800c1000140c3c1c1c1c0d48d4141c118030a80c80712030034840100e0950140404460105d42071400d0303843c00c458450050054680e0681308424155601010507558040c5803003a2034203401c2d03140c01a61003034006d802000d40000050b0020a8482040d40d400301c4100b0116007071000a941c60106100600082d000c80e0005d0060788002c5003448082c0d40310100c1c4004200e601c070500350740c0700000300d06a1640011a0180e00210700c1d034550610306 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 426954811 1250 426953561 426953581
    0x1c060609021c090f110a0f0e070f03020c070b0904020d02030f04050c09070c0809010c1b0812090109050d020d020303030405030309060708072007052206050a0e0f040c0b03 75
    0x400c00e09032011600b025203041450700c00348985034885410071249042c1c0461a02c841c8401014903510b940c0200101e000800c0a4100c0c000c514014180843c0701e50840c60034890040040da400b0000200b0940104460480b40000103018000d844540040981d508150800103000741b00d204041c3e46998004810000d070941d50500c1c0390b2140c0d00440c1550440b8000300d08001240d18100c88660205240b0401b400100c1c10306000341407581d8060500e400c2000d86900c6640300032221050001e0144413068045c480303c034081c010700d80003202c01d03114241011300060000c0d05004050082600650a80101030159078450301d85086a03500601071702e6403800c0a0401d00d0b242c0e4011913040c0f40c18400c240100354035074030a90b180d030322030a40ca59a1001101c4083d03400052254890345159591207059004038099a50541d01c5c00c0051082d0303441c102c200c250706152802d0b5006035102d184200c101003410402c02816840b019400751400500c21665030b15807412010508040d0031000c1c04070300200400c6800e0403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 426956061 1250 426954811 426954817
    0x204030210030209091914041211011a0405040503040b0a05040e06220b040b04230c0a0207060f03090506010f0e0906012d0b2d04080c1c06060902 64
    0x4000d40d001040e18241e0a000d50683c4203071070260b50401c51000000d0140b154144da8440c50040d00300700804c8030b100e00031301c81c0d80e500741c180ca00780c8951910303501708007506030051056003404d2580300081c400c144078504403440300c080300b004003801581c850000038204a03040c0304590251074585d803d5a21007031a88070003485a0000c2c003907600b0000118001c2402c624000072005a0b080550144a1800e030a06220324041c050300724010380c000b038036030035035140740d58580c05003c130484031000a0284000e142004803411071000303401d00e034000d00c04102014107103901040050580306c0a0030a0601208984030440042039065006041406501d00109405032403c0d1550f04594510811b200030b5240e1111f29600c48400703101d543d40504810034002c040b00500240800407400100604c03074115903650070f2100c50384c000550040c8039a800d13a01c1c42030768456003140c060070f4031188030344500f050305000c005d07541c0e120402441d5106a07120460010060003140180380762941c050b4060100715900c000b0803020750 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 426957311 1250 426956061 426956063
    0x310060b0319060b0706110706090302100c0e1c0c080115090b10020a031b020301180b1803030604090804051903060b0f130b0d140c180c031f0503010f020403 69
    0x5100020315802c1c4140900a11080d145102c803201e14145d05a501e0200405000191200c112401c0c01500c011441500c5801c14a40c001e8016001c1413490b031050408a1349002c0c086014404035134480822500c13030526508680c0b09440d07000e12098564209a0000441584001d83c558242252200a4121020b002c81220600201404682c002c102003064105212102c43c0c0140d01411001c8013213440b40b08050300055409c0500d1650050a0700440e00b92443c200c04109003290341c00404080080ea0640e2a03406030001c9110712400e107001070250388130f10020300700912a9403911407203402d21400350100c8004000003010a210a000c4078022982c000c2d4a1009941007403400d9600c60960601d501401c0642c8401005190860751200c0c030b1100510404a80680004a0a40c0040000d4004e0384890390042c00c04d0081407000c1c5503804000d90301d03188098500d40301e203030b8209108181252000381c13604008841c502840c42e510000a12401005d81c0e070005070315600300700b5181d03e22120f6078020425a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 426958561 1250 426957311 426957331
    0x80a0903110402040e060108271b0907020a0b09010f18030f03150512030d020a0503040c0f1401030902190b1806090a06110a020411040501030f050c0a0c020310060b03 73
    0xa40190041000f01d014038400c01942c034117a0000104150310486600341d0160b416100034111502030301145904c61114882648994042d0884000c82e140503001c1c0c0080c1d8108890b1843c913440c003000000c0d121002c4110081003100c050000c605003650030740104010f4103c4030400c201ea0084020714201c4d082c0c824105a0114010301900081c1c18400c2c06449035525139a9403424031a440c00080c046c800c5800342e0300b526140002e2201040d0407145000904c0e03c554550f4070591a4203141c01d00a21101d502d42c880208009014010041c9144100c4074480100d42400c00182e100201c0c0003062504e401d42c5900d04003046400c00104007102c450f03015080303400b0a45c81185643c0801024064240f207100c6031f9581c42241d8200c00c02036180b24068a180c1c02d2561829075003ca00701d5400b1409407032011001250304240403406000c90759043c0329200c6944540842401603003800c02e42c1c0100351184070403100c104a0002144010741d00c0401c0700051744000403400300141641c55020f209941c105450310066 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 426959811 1250 426958561 426958583
    0x190c0303140f040b06032b0c0b0702010209150406020a0b1e070f0e030f0304030609030203120c0a030b040504030c0605220506041e0c0e060f0301020c0d09290304030c080a0903 77
    0x44e8100014040200000031f141005410a080744503e0344550141405d03040000c0c1c05260743c000307100c10b42103502406140c0c0025880d00c40c48010000e000c440584084a407020500042041c42c0d8005450441030390400900c1016450b00e0003201058111a0300d07040c03040d0000c070144450305c3d5000002c4a0301d0b07651a03613400e0003030003100c081507241d400404100c89154801c0c48103202082c419400000094072a00440e450215201665800304c8011180b501d6207050110320042d60740d806001c0e009003404125010041807406e0713500a0840d10850001800540c0d40300c00103080c4140c2c6000188614021f007500c0003e407010f0b403412a030b842200703c8040f10001c8915454800946403038641e030200c142e2090b01900c5403400c00d5680da848083c0141810340c861182540140c46490a10003001c054030f11001a000c003404440c0042e0820400e540b0540d5050003056045480b0520f462111a018020350340080da207848605088840d014030000103410244000790605034140c0000f080e00407203100c0c804581c0c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 426961061 1250 426959811 426959821
    0x109151805330f07021b06181311030103150603080a0c05120c03070302071a09010e061e0403030906020604020603131a10080111190c0303140f040b 65
    0xd4241002400901c0c40d88a072110034500009105441440318180b030340e0180c4000454420140c0c41d405881c030710303116001441445803965043c402c140b4840b402508456000c0300e45808180240705603103100520b94031295080f1400c0d07407100c0701801b01d090404d1003031007458a50140300406500a00c42121007045060700200048218003c0104036034114000600380085608140d450304190328044a650040c203107910354054109000e803049250301c40056803980709524003e4545900c03078112042000586410f0031484e10710074200c5600301c0b020300c0d2040103540202c2c04500103005106800011011910a151894030001c0143c0101c80c020380e600e480c06980c80d00c00340c1e00d030346068401a400442c100b001445c0902204490785070540b00b0380140110b490300b055968944035080e0761014035000c41c85d80404c104902400703808801c8403a800c2a41ca0040c980700c03010848506110b407a800e00841c0310005081c0b60080d4801484a01c50350510714081c90082401b03003542a0494003218400b011401003a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 426962311 1250 426961061 426961091
    0x40f08010603032304090207060f050a0e100e030405100203270901052b0c06092c06010207090f06030308011e0902091215060f10050913020c010915 65
    0x1c000c0380d40649610701c00c02240801c0900a2070710358041d03c01454200000600140c40e0b00c01030115500540d800281012188001002c1d00c02c0030300038850301c4c3e08101c4404103407030000c2030f680650040c1800014a45907015865400c60103a03038041640310014001030701e00560044014202c405000000401d40070034003403001200f045560601d80c1002da0140103201d02d00740300c03404080380e04041c0d4010282e8415100d1f1880e064001c0c80701140c000070700c2482000281d030000c3d180005804048441d294920081c2c01d43e9204403140310f180401c444001001c80c40d09e0340240000380141030702d86018810482e01c80500c501030140c03440110005043c2c58000110858562001aa0045042580007401c3e1920a80744040d400c21203c01d03902c4914080c2c0c000801300b08002c90721035270750703c0070003c900c500d861001c104000c1444c01c41ea074041d240103e0b02000155002c000c840f12900100c51044440c101e6441e5140240140c03070b800c00940d86041d4090082c0701503080c040d031031039200f0901440907107102d00e964 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 426963561 1250 426962311 426962321
    0x60106091e0317120717060a08060402040c03140420010924021207060b040b0d260702061206040c020d0f050d14040c0e090d14030a110d02040f0801 65
    0xd101100a1600d06000003030a5007108100d40080e8100c584c10514813000c45144801c00391170150215500001026054502103200c070380c400e0003103807441156440d00205a844400c01040240714540d160784072004107000c0e90144d201c0f407000721010720507840c0070310f085020b0005145810026403801c400000c021740c880c603955810f07034400c105100e8811071001a41600c2c1c2031000450402d5001e9003101003003d03001d00003d4501d0a001b242d0120391006070800780411241003c444038011084080c07000b011607100c1001c41d00c503246049000c1d4a540e00944a1440303070048400003540007000080321482c0e0543c0301321603400b51004460400c941221b108050b0b9540344403406500114194104621286000307401501000b07100d0b01011644803039101101c0c2d02a44c08480441f8240003942e410f1050500013803032543d01c2011100246400340d42400081d210a1074890322128540d40080000d20f5480d064000481c8000c0384044036458483c0006840c01039002400f5888140f4106e48000840003414052 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 426964811 1250 426963561 426963599
    0xc030703051213080a051308030a03021b030315060705011b030e061501081b190206010f0911030609181b100201020415111908030f0105030a020108061e1206010609 72
    0x5241d203005c0060106941c9500066500800b2501500c40012003031404d10060104040a5030010381d1510f41d85012480300c41c1d0140740401a50041c000c0001e00048600414140e48044450300d45854880c9000c0d809400c103040600c100d103c0e1f00c10303450869030301078000242d903404080541c2c203641c2e102c00722802e54034020f020b0715000600c410081401d842003403422040003440506220714140c02c1401d0f07035045c442c10442d218016880000100401100f61003000007400401c1000d00004030421180000f5001c06000e05104030103203008100480303080c529030401d1500900070744510610440d4100c061009401e116800342c000d2039036000b0894410310807207054034a21903100d401c1220b1000c0c02c0752050004110504c2038131a110550b5103182031520328462040c40380c441d10380d8a240815a12407134650680c404e5000342c0c0314122040050307030005581ca07030040060b50109200c6100e6114400040c038451126074100b46405881100a44045440e42c140d481d15221107684c56a20300da4011011803a101c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 426966061 1250 426964811 426964823
    0x70b0f070e011403130203070b030a05010e042a09150603060501180e091504080a030b0409050c090c0d0e070e060607020a210602220f0609090b060c030703051213 71
    0x50784821030f030b0b40d0303034055500a00160702c0b441492165034040780ca85049600f1100c0c02120120400c80f4401d0640140c902400580c1703185151401d19a6850510031103103d01300ea80d03060300c0c4000f49003c4240603c1c8030002c0c09441414442e1000b003030540e00743d00509002c1d44001034107140d00420a54024070340d400c2990341e09003912060318030703000700300310281c002401c84503203400388071010354101080c1d248540c002c9004001044e503c20340c90001070116416558001d02076802c02040501007000400c1d40c90141c07000380c480000f00e0ba1205402d003520b2040210300c04070307240b034100c44409030900021440103132048030080a420340c89031000c01c411070040c41c500070341c00a104031003448114841034002180c0212411110610101039481c40103a8010070015030400c0d14034200d210242a070201d02c0c05c02071002c5000002c500c3d0501c5001041305125000c0d150704d10751075007201c02080d207031041201c0391115240140c03a02c845007450b0050142d40b2820016941301031007000b1500c9060301d40d041c1500258403407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 426967311 1250 426966061 426966077
    0x20f0d09110402030f010603060515030115140a020c0315040c050d060b06160302151b130f0603090b0a0e0a020d030309050a0b0a0608061302010e15070b0f070e01 71
    0x144124040c0410240440da078000c04a19400c40c0c2e11140099030091042d490800502c0d070504c0001030450311181d00184c85451030509105150500400716070544604503166000c00382000c0c0c040d150001c4201c054401070600050180c440340c0d020500308090388044065944600c521141031120140c20b030307405070481d00f40c01b100300140d19000003010a20744c4908408551001d101001400d941c2140c548218052800090300c810994188403410b40c6483c17030f03d01e2070802c1c03d04088003c00c0000c0442003070a03203140050382c002d0301c00ba000d00d14030080c100501d00e616229103e400003000307044c0050b02124034500c0103000c24141d2003d4000c80d01d004d0307001c6000b0944031301c3c15000c00240b03041000c4190280360391441300b1303004241e0074090383d00401d009014100c0d00341450f2a48900b1100641d0107440721b600300d00709100e141c0c40b800c00d080c00059024649403045804150010f403441c83d01d0310008031521400a11f401c10848401680c510800000d86100035941c2c640400f684ca0060340061180020844 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 426968561 1250 426967311 426967327
    0x7050a1e2a051e1207060506040f02032a120108010c0f020a05061f0302030105180606123418180206030f0a0b040204030311070609052d0406120605010603020f 70
    0x2016654800c40041d200325200302c404c0c2038456841d6800314006450040e15082085140c2c200360007000083e915140b411882e6141c05c2d0680308106003850030310740042800100f02d032050300104042c3d0b4040c4480500b480180d50b51401242c0c02031000c4504040880d9503c81013003040d6002050401d041030300400503010a54030700343c207074a0030541040200f45807036241c8801b00150b1424401d031032141d060800b21220a050341d02c06585001c1008000030b100792440240f24610010106680071100540500801140f0142146a00d41c1c0c20400f80d134501d2a00e005d40000d80805c1035881045d01d0b2810308410400890510340d0071206400300382019404c410704101087c13134494610145c40e0703c801114000100c4c903500381e000078140e03841a4019000914a41d00c034030f03800756043c00160b0050103141400019030b031901c0301040001003483c807407801c1100c641918205803050750350038002d8058024800c10031544c4940820100094608050324a05d140030008101c090103803003290025a41001c9031030a103810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 426969811 1250 426968561 426968593
    0x6050a0201021908090127020405041106121506030c04050603090a14150a060e0c070503040f0b0a180503121303020901030f1b03030807050a1e2a05 65
    0x40004101107640c00c000700b002c00200d50001c20031108890b6070300112401c000c0021402e446102440c00d95001002c0d990302c1803400b41850880d201941035170040740c1d51f606c40c180303a00c484802690f91900108000b83e079144210221811501c12201c4200425000754181e051040d540030807142244044800c00c0107126a28000020b55406960201150841d0000d40d13994681c0a000480c121826481038000c2c0385010a0340361203990218004108000561034002e40070304903139000d801e1a203003480000d001418041c0520444014001c40c44c0c40200c12641d8a619442c65800416840001042c0c565191080034006806e501151030080003080a9020908151007980c04288a044166003581001005881e0722141d01c2c0210b001d03402e451440750075400c20304042c454042580140500010086c00026045001141c1043c02e0f4075000ea00c442202c0310a4800072205200c3d26913507809516400c4039164040207000b10b150154081290501803200c0e4008d0f43c0c0c1c0e01101c01001601310716105510852 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 426971061 1250 426969811 426969817
    0x20111121b1e1b0102030906030601050f070506160f08070804030809150906011a19050d0b040f0e07050a0f03080a0e0a1d07050f030a0902040605100c1101020304030c0605 75
    0xc0c0340c0544032445001c4000702e00484101500c180540c1014038640307aa80303800603100c4000103080c00550301e410f40c1c2d900080c1051100400c800d06126010070342c4000c10701700c0e40c241c60030654003a0440c0c004d0306084c031401071004418000faa002520004000900a218101c01e074098403081d05c0d008416112a1307019101c0110044c940c80c074520980919504010f0840917030790054200c54060046941441143d41e65412081078503040c2c40c0080140184800c0d6410701e204284106140164a0301c1c04140004050314603c0075032503111741004001e411001c0c0355442601000e42200031955601d0b502c4060000e03d0b000b5210700304000010031000c00104906000620b42c4686505d48044034208140006100070b40700c0d00590901800da55900c0e02000f0380004c0301e50032203018240782d418089810301a640520004004c01d40d04c5459003414400c54485402403009090000c217902c2c400d41032610020103901c40094280c0d5001040c01c44c0714007650000c8219016240c01003180c00ca024101001503a540d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 426972311 1250 426971061 426971107
    0x305011d0a12031e091208010b0307080408040f0803280203040e0a020705061f0e010b040501050903010b03031813020c060c18090c0a020f0c010912110607080702011112 74
    0x1d1340b68611003042c0c400c240d5543c0900344540c800003682c0c10b100c1c1000c0c0c03220143d1503903e405002028005000016001e0140d0740c0c05032161a040070b0039621484c00300040d0041d07a024400040c000400032455141c040302a000380342c41c003455520b880200d60707280031882032900b030200e0140e00200030a0100c0d004910a032a409a20004058503081c1996038076481c1180456500040216112100c4411400048907000030590608811125410512504800c2c070a91182c4d50500c03100141400040e2806c0d08202c0d81d0b1034009003940d40310442002560701e03080c110700036203101d1100720f81c450000075110302c2642d2400944130001c115641d9034103d024015031003000120a80482c40e10500d0030340e561444400c0c85508013a940703d8941c01031f000042c0c82c00c8056040211b07503401ca0725411a650b40d00c810241c048401c580c01ca02041003607070030700000740761f40f00040980001d000103100e024012244c1c010701e41d151003a81c52075100b40824030410345403488a08030340100002081101c40130408890202e20780b03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 426973561 1250 426972311 426972317
    0x140c100e061312060603030f09051503071806050301050a051e04090f14031305030118021302090a0b041e03030804121707080f10050109171c08010305011d0a12 70
    0x11030b250800094140c1000008aa00d141c50706002d004140e41314090723010840c1c55043ca0040b031814500052140071003111700441082012000841e414442c45400d0411141079940080d055148d1600800b55402401468010703e280030002903030b41040280e10b4120609501122103d42554041002a2105100503184140045144400b003280102040100d01081c8025942c4440c607003444461440c0c180d200c2c0c0e01c6640342580e154448548066a212407a9048030200c103007941c2024448002c1c09421013180d0004681e03000410074440480040c010340310222240e040d48a40013885071440e41840c0401400a105d20b8003003000100c0c40c07845041d142c403060400080c003225141c24000e8450007201e5980c0000d42c071030140304c401001c41170200d4110100c1c107441d1030828144400079001501600c12191214081c00c0034101c3c1c0c640512031180d13030942c4050b10400500c0c0458004140c40028002941c0075440d042c07161404440b10810b2440481600020b800000950346900c0040c142d260a000c040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 426974811 1250 426973561 426973597
    0x15030717031614030a05071a04080a0c02030120031b030c040b07030509090705191e110717100506010801050d03030203070215010b070611090303070b070e030604140c100e06 76
    0x4030f14414809065015400d50f212902c0705030300d05000607400d54896060140d04490418000803840b501c048405118050500110500d810700c0860b0040520900210700346898050800c0c114110000860260344284154000d45d00203440d500244d03c0309507080d9072a00e01c10841003000c01d940e0806460b40c14041e00305641002c3c2942c004c24000e04d002c80710740f000102c0004074010001003040c0c40351400d100034501110405140c40000c07603d14044d5440310103014510b0075400c411501003101c0b00180800c2a4404100e40b1080c3d10180d441035000c40b60000c650070f050000341c6d103520510281d4101c980c0103007001e88405141c3c41c15030081d030010f00094118080d02c05078510441c1e600305018000d088031a00d055a030882420300074126541181c5000452108100d401c03069680041a258480c0d00a803400c8a02e440300e000a0f18400c10303040c0c16a405010320000c120510a55450318440182c0034000c3c3c422804000c0b02b00460b2003201c1e048400420b582c0d02d06400d5604020b03000d011030349a00c2100d00c01c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 426976061 1250 426974811 426974843
    0xc09120c03060609050712090c05040b0301090c060509180705030604021803071707050402030f0604051e161d0307061b02040608010507030b010c05070317070209150307170316 77
    0x4152103c68205001094a4105100105071b03c26a0382e079803e28600c0f000c0150034159030780c0e4143d00d5950f1080601c595202c101060070350740c0039070126200c1c66000b1000707000070340d40344806001c1e600022101481800b0b010040d0000c1648142c8030f52203a081e607a6031320702d5640d450741044000e4206071800c280441d06294800d010751410042d00003c2c00514182e0002c8a000300388213841d041168111034082c500501c2400380080c03c006049801c0b07041203c01050617618883d01c05a11115038183c2046900410144140800440c6448000600035501c0c2c018420001d1065a060308004040c160198055002004040c2c45032030358581c030b010f020102000c000410b40006050b5111500035113066507580d014020800c0d0188201e031010502800c2c4540318218175201c00f03031510458800508007100300501c2d1540c91694408465080e0790003025902181054a5651aa01c1c454030305a80640320b030150100311540301010109194071004c0003146884500c548071007582d01d524004681c1a155180510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 426977311 1250 426976061 426976073
    0x16081207020a020301060b0a0804120507120801050301060501031b0c170f0c010b030f070e070c0c1206050c090f0d020303040f0e15040908040527011206050a0c09120c03 74
    0x240a00015401044002c10500405085448a034054401c00c80200700b2603980e030390014090303a031080d004146a06500388608003541d13144500c1d90003d0601c2c20081c03031030205035084100c1d903068440c10760003008000e8039880103604542d006444404d42444090034214400e01c01c250380c1005900c2030b982003002224a502591880c0c0000d0140446502c0c04170784110700e00024421039407550030480046c10727000889009a0788420050041081149210002420b054041d16660f0703e5654001c001130101c6984920a9410442040341141e1381c60910010a004080140603142000170003001540b00380b280d08200220804400c0040b40c06000511000a140c580e002e860802020014a4820f5500c3e0101e030705402000d40d114018030452a0403540000302e49040d058a06445050b941d241005280084100420084c0010203c1e0744140c00004030745410012502100c0f244212010310058907002c44803001d440c14020204000f0748441c41c00c21401841d15070b505042030083c0080b0120703d890307403141 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 426978417 1106 426977311 426977347
    0x40c05090a0608031308190206191b06140702060408030103120309021201060807050f09162c1201050906190617210f1608 54
    0x200580321540c00300e40509002c1d0120b81e2600717407002289012000038001c00c40c180c021004035040035004d0004030b03c4103d5000341241e003048402020011900c4a0380440f008214200f180216100e170607401e1803c4850051502085007e0130780c842003045080540000d04560010701088041688813056a0540303920405400384006a0310382200078040c110000703507109150072840080840154403000803203082c8001d9a1006684404000a4481c403060030707038104c85003c0000d80c492500142d501a845c060381840b000c69054500000a10b240d40160030140340c840740485e182a1420300031000d45004010002d01c01c81c0b62501c1280d442d80409088020200040000c1c0b0290b40c2050304404060310039004014a1b00f0600d10f030880d0750b41078012414141e07106400c040b08244080741d00f12030300c8070b400d2407076189040c0340c030010310003080c04a603401d0740c80301c1003030214286440e0300c00d02d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 426798561 426978417 := by
  have h0 := BRFrame.cov_init 426798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 426798561 ≤ n) (h2 : n < 426978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
