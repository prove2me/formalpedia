-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2020
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:58.822965+00:00
-- url     : https://prove2.me/submissions/a8adc723-fcf2-4531-8d0c-5eabc5bcffc3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 363129496 ≤ n < 363309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 363130746 1250 363129496 363129499
    0x5030604140105010804200d1104060510050906130e0c0301170a030c0809030a08180111010b010e090712090308010e07090308090f060903062814070f0c120509 70
    0x800100c010004098401e65050310f42c141c6454a680c2c40d0364030342000c41c00a00f110050701088025003405256074000d0124292072081110201500b0911700f40001d40d03405910281c0107040c0541207000303e07600700701507582c4400e05503595900da11405010b585080031550100450720440024440900c0f02000118160341c00190070407501050284100e558860042c0040d0001d02000100800581d0090040020142c001c1c11176110400d541c4406031301c1d42c4038900107501402c61800522095802481000c03010304110020030071000004006440a111015182c4c80f071f00c40440000c0445000788807034003812070400c00030400e1099500c3c01501d02d00c804c2c0100c1c1c02d20f40f106800545101c1c440d40340c0c46c4c01d4030392100d040b81c00c003c02c0c002403281c1c00220b2a041584803500340524890742e02e007004501d11582100d010800c4020780410010b00c412030388403081e1289801d00b9001c800c1040c05194464100e040c0d072811280360400d03414102d6156259400041401c0409040d01c50700546c81000740036030341c10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 363131996 1250 363130746 363130751
    0x12100f1407021b040504081c020901020f0127080d050c0414100903031d1e0406120b06010f0509030a0308070f1110020f0408071d061e040905010b030d05030604 70
    0x75240d8040e607884402d001154103c10148514120318141030708621380181c4941c14883c04c010920b04100e54504404076617030605680810031242e250b070304001c102640f08450008115420100301e0303c24030b00000450110b8200580042c040c20041c481e8112104400340c15000c214600300401c0c500c119500c81c2c8205001e11300680d4012540b0702d06480f4a014130030b80340e02c84641941c030750307a41600d03035144011542003080e01c0740e0202c0100d516203224032481007156100300300900082d82d0030042218044d8001e40c0c070302d8800385107503030020307110003916500154242404010240710f600b045429100e1100c00c40d8040c0183c642d4001015007007450b0a00900d001d0b01c851883d4101040121448644801c0f01d81065001c3c603603501600109070300070711001c0c1c18084080d2405407070702075481c03030800741c1c0c3e200c0e0061030621030150921503500040030f500010204c481a0b0412080e880e800390641a107080c0741e1060343e4481c3c00e0010054254030401001c83d01070255881d840c81d42d94003416540003120b465002c0c1d070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 363133246 1250 363131996 363132001
    0x60f07051516090e18120703020303010f0605040303140903120d05041203050910180506071112040311060a090504061503050c030402090708040312140106120501030203060612100f14 80
    0xa025020030303c166840410810156600c00080c841c00c8400f03038000403068003403601038403000e2070424002c112160003a0015580c9515003070826038484a1036010000300f010a00050000030360244806242e1014000c1d082c4d04c500c0450000b0341804c190019a151512000404514010040d0000d40c440e60003940103a00c3c0c4546407030260207640c4101c0d06c4400c2030b008018200d102d4501d6a110300803510300107080c003081e0112980c41c289410030541c0e50a0109a803e241b0f50030314103003004002e1500900c103c05904262443c0d90b0101015011034016100d800c001c140015102d10400c4004000d00c0d004200b4001c19580b036030803540780040c00750798034002400e0100003400c1d041d2000c200c9008560240c80007030a603442d008120780b51100074004404003c07007000e41c181110f80034000c040c1c00a440b031480c18215450b1800192006114002000300107042000403c0542d602041041d03000340140d03200100807e0012200c0d040c0195001518121171520380c040782c044205910010040d00b401c0725110458 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 363134496 1250 363133246 363133291
    0x100f0e06090d1b08070b0a021b0a2006091e0310020301080604140f06010602010614010f17060409060504050309010e033c0d0f02060a1a060f070515 65
    0x40c00088031900100f40c1c4a060045903c88401e040d42c050740c0203a001500340003441c6d4808000060540e81e10444030380110b8100e100c4248502c0400e510b040030746c01030607001f0442d0784101d0f641ca801c8241500669a80f56100e04648071501141c1e00250000d106c41240d140003140060201a000c10060081c4520b4002e880fa080c01403086a0503035007120f004204540d15590b400741e000e102080e0702c039031034028803000c520a42801c1114601800d81078001050a6040542000404d28038650031410400e414000c000c549812829001031054883d1004030140d40361800f0601801c00ca9000416081c0f03800c0800c400c0c0700e8040090884050300345d03107042c55100c980c01055070714036520119407421403801c03d5041c4640c001e500131140c04e400b480c070361440300d030850701189042906201289011502c5015083c003196030501456038009400d450821401c14400c514480da04c0c00c9042d82d038064403001034210940e0450200b03884030a907200084403c0c104c2d4041c11202c000c2c0c4240d9080710020700c3c4c0400e10350314 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 363135746 1250 363134496 363134503
    0x1406030102040f031104060f090203012102130506030f0d0207080d0201060308160f0b07120e03041226130305010b041b051c1802030624010f02100f0e0609 68
    0x2c441140c40f40202c00f41c11a01d4140b000710240c014aa40642e43d40f5001070280d1592100a0081244107401a00c1e9854603c511600051100003109055107104a8900607500d03c803200d40043e2540000045559400000c01d28002407201180030314401c40701c201070700c2c03613000900005640c000415500100710741038003a800d8521a000c01408448103001e0b41d00c0c4c0c031114603a80ca404034001c1d0000c102d00012501c2c7c001307001b00c060310144000ac0b40c4139130311441c1c40c406000b0820003402000045103007900d4004442110000f0401c0100381041243d90459609054030300c0400d900c8032000d2080d5210562100030480b40014802107420f0b508201561001d031600c0d106101ca500180e45180e80041c1d40f4250407104cbea400006681484080c0110a00400c44203103c0c10801d40c1c0c6401045110490341c4c010180b40401c000c041c400180c0010084040c16032502c048003034400001c0c00c20328106c045840c005d03418a04141c0f944c0000510f0320f080009025400e0700300c1c006003244e036402d541c02ca8440d0302a2648 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 363136996 1250 363135746 363135749
    0x180d03140a02010f020d060e07110712050c120f0610060915020f01060608100e04050705210109050a06060803030708161b0b0f070f14090121140603010204 68
    0x422010300103048092a408018401540e142c80005803220900402c103089070042c1a8540c100c40d9290b10134411200c5528655420000c1824107030f585254078100903a548c42c0c280100c1a0742e40c0d0f0980c0080c02c01008124207100c24400500101e00034529050381c541d2452a41e00c05081c41c420703030b400305602d908004130003400d0300c80c0fa40e0740c0c54101d4100301d4588010098030040c2e1f03003180302d002d9001803503000030300c81d800c0541010340c2e50f2a03050424440365040b91120780c020000c44252032090100003030740001c5100480c0c0c0d041c1d843c4c0c0032035480e0b4071050404030701880d000b000550810034007070304001000c80e6a070790300342c0315280402c002ca4440d080b044d80e07808101c0e0404003081c0c10302c2c0801d4680f081106109814031007032504000601150300750841e9129401c0089501c02002c50034000721007503c8403150340c0440c030b500c3d1620080c14002c2c0000c2410344948101d03040c4000001c1e0603050f41e482107040d0420341c003500302c984000e6450284c6000003003208401c0390803c085440040b0b002132406008070380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 363138246 1250 363136996 363137003
    0xb060105071101081503010903020c0f22050c0c070f081501270204090c0c050f15150f15030703150b042d06020a0302070801110304060f0f0f02180d 65
    0x81c002c2d45100150b5000750054842210700503688200700c81c039a42400380400b4248a5409840e1514411050003115196105003512840d5550311f0750402d002d110710501c0c11100d403203101041ca500da0f0200030a40b0b118011078140f060195007804140481101c6094046070210070031280b0410084c0104084110b00380610342902070200007140b94482d02c0310b00c5c440c0e509900c0d1001450141d85800200443d00c550544601040f40003014006100382400042380b84001d0001420b0200300490f0401d011540087c144ca002511042c144861a00c0c3c0d015828903080024103030102c900e10400007c62a500300f129207a0000342000d504044080032101803104982d1880c03038040c2005d00304002074000c07103c0ca0450f14410b889011440303500c888210946e0b00100029000b502c10500c0905000781805015040b02e0340a030b04103440d030a1003411203002c40e6801900b2880c00030f40040b80c414190080c16002c00c000710b085003440018802945c1d00d5008051100b01c0d010220700d944c1416040c0846100b29032000f4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 363139496 1250 363138246 363138263
    0x6020706140714011104151403101206020706021c05090a02010503130f050a0b0f0c031306090501142401020601120305031b1303030822030f03140a090b06010507 71
    0x2040000c2e040c820103100482540000b060101007110805d040e40c0056011080e8034062400d21580650015840a22041d20810b02d074503502c1c01e031007030396200c403218400c0d4141c0c0c1d450440c81005200c0316034191010035170302c88c2056507914003440840751401a0205960446450705001c20360301d0070001154806254180c548604540c0d40d4008440071140d2110f0649400407084080c20001e43d00f0712804c81403c0c490410181c4604044100d886403c1c0c4c01054a004a402003042c40b00b01301400c0c2c19255443e03842a800b00e90110310307144c0b5601502201c00b0b10104100307140305006115003801d81040300003005464403820940e607030004a0703840c0001c1c840c401f0f8040200e140d46000c60321410042d41c0c080361628019005010f035000680d22a030183c204d9000048c1000c0062042590184e8100d41240c5540c0610000468030042e0b0a400d0100200c010103120404205d8220701e402600300742544000c1340c4041c0b1051800380700c0320018140c4400c0840d241824030b00020759960145041d00c0510307400660a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 363140746 1250 363139496 363139507
    0x1060513090c14030906072a0f0206040b0c07080c0f010c1b050303030103080901181d1018090c0b040b0f0306010e04050403030b040b0a0b120a09050a030206010602070614 75
    0x1d6100074034a8503444070030060308006140404004000950003040098010326240c6000c1030003c01d050807800b48000300c1c24502411034410f00d4040c1d04ca440081e000218840103002620009500f407081d43d10443d049080814041c441610108003541201c4809041e20329500300c0d007003000301c5c4600d02028140400d034a2030600380810762690040440200c0e51b1020600d49440d500020701c3c2d5082640100c031541d2000440400070f50380140f9170101c0b134440c0d9000514207810418558110340300503001d01903910b8804002500e001150301d0620060a40e9100300c45481d462961607000b90024107000d0310031150780e02000420a0486003100c0441758050340050400503460044940c0350301c0640100d04210700c440448129584078403541d03008500c0307518000b41020103130f42480305555040c0f6a040c4100c400b1071003080090024030499030031030b400e4903d141c2d0030743d902c00a11009100000008d4018441c1c0e04031a0700701600052558141c41c4a03401725051166100000c44030703541c0b00700e41c01c40181010300c070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 363141996 1250 363140746 363140759
    0x2a0b090d050418060902120106180b0720040c020c03011b020a03050a020f01050a02030405011503150b04180c030b0a02040f03020904110d061e090203191a0a0209010801060513 77
    0x4554518442610b001308820b03644000c85000ea810140740039510541840042140eaa00100c80408200b1241e0740c401c8a5450000c90220074041d0340d07005000d540700d00046064100340400340d52442c0070000c00070072240c001504c1c000d5494042841140c040e600e4000540135004081900c0d0030242c84950080c4403940055804880355002652824194131400c802d01c100801c00303006282c850051001c0060301c074941030400d1401e440010707080807070300442c0c940140041003e10101c91103d04d0b0450001c600603540c4004500180f5460700c800071840100e0001c0c5003009182d0504408a900400410003143c076030041c01d80492240b403050300280390450000700018200411810340c000e0041d400d400060f40810045984405000070407124940c0d50b035030905941d80c07003c3c0300340c41d0304540cc48108542c4031030b40e020039540d40b804200307064800d078581014400c1001070401980d56802a03034181c907003030428421402c0030350040c0c42090f001c04d01140010408a20a03001d48440d141c6c05515001243c0c940340703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 363143246 1250 363141996 363142019
    0xc020303090d0f23030a0c08070c021e030f030306040e06010e070309211107080a11040e0106180b150f03070806060c011805011a03030a0e012a0b090d0504 68
    0x1140500780a404d0040e410450001c182e00003002041d1001d1641c1c03032401c4840b880803203a078468a4404d01c044a03050081c1550f02c40c40e0751031015416107440400d03080303480e100d40340150417020a951602c0342484002810700f010000e940619420303030b81480403014240b13009031189400d020f5207103402d54500004030700e24030a40100d1a542d000b00440c19070000d13480e01903a41b00c4c04100d0080301203404c3e603040c0307581c1410400025000b02044005030400c000c0c81c0d0360382d4408080121080b403045440790104008020298481001842d10302100c0c0440400050701101601e528001a4412a03202142520310fa18001c203c0c0d2090001c0301100d451503407818800c1e1032039000070306041c0d0090b10612400c00441002d1042c03250b004004600d544020139680b8010f400d60f0b03410b650725000340c0210072000b51903841c0001030359210001d40c10100c19004000740126091a40c81d40c0900b5441018840e030b00c25020782045901040c0c0c011840e00e9001c0e510f58900d59520b409034581c03100001c6040104110103000356 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 363144496 1250 363143246 363143267
    0x6020325030507080d14040515090d0f26010f08070f0302150a0309020603011211060403080a08070509040515100c02100c030c06050103060b0a080a0816150e0f010c020303090d 77
    0x30001e0300c250040c2c1c6c089071428040768211000ea002400e05422501c0c007184080c0d00031800c500802002c1d1100400500e4004171604c04424400400c0030008100349150000e605100100512526580d42e000e0400c44145540300c1c090031405200004580100b00d503c01000303507500542080e00e08490407544100317a80c8800030240406a588641d18011b9441000443c024041c8100c1810f941c04903060a8102083c0500218850b0800300810030020300341d4026207261a1075030030800031555540703206491b948914a0f03442e60003403518041281c001e180030928422100250b0780f41c141d10002200039100320600d604003960003400c0c6000d04c03500c644a8403011a1185c0b29240210348107141303984d0281941c1e400e8004490701902c405501c001400c010b48507000030840302c0c00409503e003040c0c6441d00c3c0780c8201070f0103020140c059110b2074240490f607101c44503100c169140c20441d04030a0203c26440c1c03041ca00d000071265003441070f0518600d20010030b0720b029400384170280000000ca18410344000321503 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 363145746 1250 363144496 363144517
    0x609030f0d0e06190c0e09010303032013030b0f360307050d020f03030417030c0702030319021014011809120804020a05060406021b06090a0602032503050708 69
    0x16800300000a0b8003e02040303001e06800764451040c069002449815a00c82a003039030304100100d0801061980d030f903a0501e04594142c24001a42074485a224400500d00303000011049400600d0b00044c07200e28500c4e008403030058500c1500f58a4004c0030824003035054940e55074803540d0701000920300e45100d5101300c91810020644004104a80589007143c0010409540c030780c0010980070302032501030002c04100c0b11000055807641c50725550b0004003a01c23403800e1400003040400001d603c00492000c464503640c0007000c4035110501c14060350b00000500a2400041c010100c060600c40900c0c00b0b001d204000c40405070030f03c2c0c0c0c2055000d403106051000301c48880c07501c411014003c42c4003464201a01c070925542e0ba0034504d004d0041c025240c0c0240e0016014060400040000c0d56010032031540c20312296442c105058001c9001a6003806680c0d40e455220954078400100103400100400c04929000c1d074105c02484240704445140d442e00384050049401000f101d400681484002c1802669 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 363146996 1250 363145746 363145751
    0x30c03060509040210111b0a08070e240a0b1306021b01120204030212060a0b0108070c02210601091a03071409070302040e070801031406011a0f040801021315020609030f0d 75
    0x40020200c0c2c80c0028140c803012058400700d111f1106410051b40d41000b809000008004861810380c80d80d018203002000030035441803820b00c1191200000c56280c40a00b070080c41c05201c280c0f903440485141e4031924225440b40710740017000400c24000301e0316510011080d0200c1c2003c1c100c0f0001961411950324889840903400c000110060799643c00d0401074150b600001c0141b840d003110004100e900145c0240d060202040410110f5540404608209035050702c12190350750052000c1d03191400d12510b462031a0189200100b003040150380641100300502e403001004907012820305450324a607001d00500104c3c10403a070794031814484c06141d04038a051400510745581c0d108000040c4400b03650700d90014030781400400902c0301c5042c800da5844003680203040c040d45400d045980070301c000d40c00300600e1440400c2c03070107851030700e035040c0c074020080040290364480102004084464a500a094182901120031040d00e4400110b0318070412010005600d01417000f041405203070024240390074030b1078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 363148246 1250 363146996 363147017
    0x80c180907030e06090705150d0b090a0b011803080307050309160602030913180b06030f01090507051503070806040f0f09060b0111010c08040f0302010b0d0302030307030c03060509040210 82
    0x322280442442155581d9000924212620700d107030078000d015040c155103074000032080c00b0f207a40d9810300014040021b801d0395a030380308410884014103084010241c2c8602c8107410013500140c1c5800c00c401e080707001d03038804a002c50125001c80000000340006000c030101840001c9105000c0c00c02150014900400c07211400307029076980302c2d021966001320005804c00300e1144850f04003101c0f400c03c40f403c065014000358000300740c1b0340c060741f0811101a2101000300f01144490f1070134410451061002c030000d00074040d03039082c076542d5030000744180750040040c00e610200d600d2290060301e00510b607686c1c408500da11060100000b4101640400b09820b503503d01808540000b84611095203104540c0031803103815440024012040e168200700c05641002c040c652850b82c0508541d40c0f060b070203013078008034000d00e04080340145035506c42d4a0b04618031800c0d41c000c0c15000006103110300d626a80c01e0140d401151760842c144da881303100c3c007a000310190005c907006151030504141c0510f0707585080c04904 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 363149496 1250 363148246 363148249
    0x907080a0807060b040605010c060c1b0b040c080a1a04051911010306050a0f06050708091009030b13031d13021303020a05040902060405010c21110606090403080c18 72
    0x41080c200c1152541c00005010003040001d00030404201c0045400300015890704002800c44502050020071392a50b0303103803e01c9414010000351003042404018440c5506903031070000080c14040e1400d4503840c040210009542c0c0c8002080c2156540c010b40f85520210391060000f000030014108459501038402d028140d42003209289095500030454449084d20210000d011034500b03820560042c10501d509002024500c001d0004585031440c14965402c440e0a00c0e408034003075991040d0303019170b0000b011002c031076012040d481501c0c05071141c101c0644844004010580310401c004011441100c0001401d101303644039010490006403000c940d44280420301c40c201e0f40a42c0c606424550b800704c0a00940c28841c03503a0018003000d860411081d8910b80010341c0e28000c03440344a04018901c1100070810040328990072140c1031001403210b2441000b08050a07034020203d04030f09610441c0009441441d0807400340c1d00482e050340341d25585803140800c1903a154020300f07140d03000d40f41d00c007800d0449 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 363150746 1250 363149496 363149503
    0x80a0614120a0503190f0e220f0204030b1e09070510021510080d210203060d0b01030f03030b0414180106030215040602060705030c0412030903051b10020102041d090708 74
    0x817200e00c50094074000d511000050454070310a1500f4041046661074a0703426102c4078100703d84440c43c6504091fa000d4a9003102000c2c0000e400d001441c44d00200340042042002c2c14658003d00c066400048141040f000181100328200e4580341c8940c04218200400d0400f40b40b203104000c41441500d40702c07005603038203000c0e480b0155680b0a0811042030104100c03001030040300307907046140c42c01002c10400340b200072824500f420400f00030954004042001076503014000c10b1000c2e444034070b215096940c0e0a00064503040c3c0001900801e0405154010f04d142c18480c1c454501c005080c0ca91207900c07142c160240c40c50034581461190365948401001598031f00c03501310740784421001c0d440c0e65a42484d0009040220181c1040281300f014428800a0001c48080d6826a84c4261000580031000d0900f1548100654005000ca0207039503070101e05407a030030045142210050711a41509071042904a080b0700c603e1040c2250751850b0320421447d405047c80d129040121501181d08142d2548040d506 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 363151996 1250 363150746 363150757
    0x5150c1810090518010305010e01090809040c020307020d080306010e100c0b0a060506040e18030702010c080c072114060106020c0103110c060106020615010c02060706020c011e0c080a0614120a0503 86
    0xf44d95081ca0041081080c24060b0100d040600300080c0000203440ea107606541c000d1034034262081e0b4803481c820228601c2081500c030b103580c000308546840c910078148510a5803060b40d099000507640c0b1913482540c01c02c65800d02611200b90364180e105079150f1941012801d000e4a0303548900d1302ca5000140d1662088007030030192001b035400d441181050010301407101c14085503400140c105025101c0540c0e003003460002095000321400c0d9072010262600c0d8100880c40d00200d0884510300b0343d00ba0310002800da8801510b2141c0e0580040c1580320101c80ea440c0001d1003200b005034041110b40c080e41d48250000c00300300718020079843c240202d0142d62810140f09801c4000141c1c170203001c10051000e03591140802010a0801c651101c0141e0042545440782c40b40c0505002c0e00007400048040b4258000b500000300b00710015a60b202d0248220058031910100c0c40c001a4486c0105a4615640c0b107000e089070541a0f40c40001140c40c024010070355182e00351b0b417010340a800389580201d50140300600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 363153246 1250 363151996 363152029
    0x9090c050a090e0603030909071803060e0d021606030218060d09031d09040605070203120c130906080c0d1e0803010306060e09120915040305150c18100905 68
    0x6858290141c401040d0340e646a000c0d04580c0000c1c0d0a0150a03100841100c04c02c50040c2d81481c3c60f42e03101c48040d6080b94041c00020040c40c800d100002c1841500d51102501c3c0300c01c0c2e41660a601c0817824126505d0550406400e500030901004116480c02580101880c0306888030580c003490300348000407900d411002c0040b400036200d00b191020140c5c02810070565903051081d07441da01d152103020540d0302000400c010b02050b92800031441c0f01340200b0941c0c00c1046044108552071916020300041b60b04040b1211090840c039800101344404180111001e50b20f15078010050300400c142007003141c1c140b03410140c421a00304403035049003000d4500044400c602034825a680c9500d5072030440c0403942c3c3eaa001e8850210402e082c440000e10106e8100d001ea000440b0345900e80704654000361420036014040c106010000034000100a0007041c441c00300c980c2da1003803c0b00c5580e0012404594819a440240620004104000285440b038003484038690b040c5007180d402e50315000419200811000d025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 363154496 1250 363153246 363153257
    0x5041a0405150d14010e1902190509250906020c060a03020f042d0302060a0305040c0b04061706030607080a110409020f1e16060b0d24060b040b0a0f09090c 68
    0x43c0d2411400b402006c0940d01e0311340c02800d140c40c0500c4154040c00e031051000b403041b900803004060000300340d18140080d040060081c0043e0520000c9045450000c2c1c100c03032a0850284c0d4416000e9002c1c81118084038a00e4000e1328040c41040c0801102d544500000300900d6401c0c80350f481d0f000c5d00306001d403010b40703000c40718116044e4900c001c0840c03100031120700040b40000c50a0034001030712583c2c00c0d28280d00940c00c1c0415180c545203400102041903800040e41000302150015210b60310684140b18645e48a20001e00351307c44009154440e1300450b0f01c2800308154401041c807014646c0c0c40301901d560f4a010b202d0a2a4480100d0300917680f06a5a01810950214012828426031040e002c1401984151f2500d088821940c110403180c00f14406440c4c0c50340c94110154980750f250b00700c140540e0121202d1100c0324000d1103009654004905140c0742407401102044001d0001d046030107590500b1360060514030074200c11030729094000040020043d151500049241260240c800c1303114458840c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 363155746 1250 363154496 363154523
    0x150906090f0307080d020c0708010c02150901060b04271109130c020c0d05010f0f02070b070507030234030501020301080c0102060114040903090b0c03090a05041a0405150d 75
    0x554506249007584021a8000b0803900b400501301404807408000411070260b101d51031140414284400340e030184485500b00032421f03820550214040d09007510010804107552640d102c00d508945450240d00d42c0d141c4100014040740c5980001d41c05580e5000e200040c1c50300541e0a00c20036203e985017034021900d40811042600c0c1342c41c003002d00c02210451010070603a1182c0200a558000d80040d09000f1084484031a0910500b90001c0032102c508035011703c0501098004100294032070700b0180c5076044801c01041c00d041c805d1088801890f0164010f0170241c0501e01c90651444414842608581502e07403d418400a44002e0000460090000607165890454030310709000b49098a0750454001000501628003180001d50304d95030159800a51000145015150307074069800203459801c0100e00d5400210000008012507801940d4071181d0039500c0341400291a40d54191501c0400c0c010b84d03140700343c12f003688525400b5500004001602d002e942c042040640c4108042d83e44a0780c60b0312 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 363156996 1250 363155746 363155761
    0x7140313090b0f01020a020f0315190b0901030c0603051302040e010f0605030d020604060e0f16031502070f11011e090906060f050a11030d14040302070f05150903150906 74
    0x5410703900c0c40c042d150f05156003201e0340002e4869010740d100912941d101c0e800008592020410b1034a40600320241110070306200b5021224008450354658113541000a00449800c042c1c4800b0304030796001100789511030030044103a01a14008004403040c228466580000da92180507001000c00100d000044074190f005401e82074520a0304454000d43c861201c1c8070205900040c0303554840c0e0000800507640411403629401c1c5035a80a10708410702c079031f44c5558500e4451480755000c0380d208511119520f5992100507080e13000361600585041a840f200202154445038080e06a440c14582410800000c80741450204040d0600340005101140180141b0840f03100b00c031301400c5039050607590003020850040240c89603440c200304003c80c240c0860246681001540c41400d47c11000380f00501c2d010b44446030f03040089a0035030051140720400108055010f2902060716406403100c1d140090080140b00564003c000a603014400c07401c000160081c0444090301444010002d0180d9080822 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 363158246 1250 363156996 363157001
    0x71a0408090405160903150603020406151205060604031e05120d0e0f0604020d030c05060c0a0e0118171002030c0705060106050307020d080402030f071e06030b0603010b0714031309 79
    0x1303100503c09140b1300e460030203a540022014088070f6101811310407040002032400050b0400e640b00940042c10080c002c2050810a07c80d8146140a1b0761812001500b021458041d80c2c0150307055a0405400c03c81440811411a2182e465400c00003d020001960b03584a40c40e05940070800351607a240411a0881032081d070180c402c803049110b00400c109400380c8022521a440640028030a200140750303001010701520500341800d41060949006181c0300341602050b90046e07048500080707080f4618107c1c1e602032000400b8203a814a03c580046040648940030b06c1d40d011180a03040c8912508a00d280c880790000718800c45030300d05000d0b00d45070946030030781c500f07041030f001202417081c01e00400c502eaa40c000307084030b0080c005d8a854400b80e100c0c0e00200b4200008100044d04174099214040f1745100d502e2400900c1c1d890b02c5c0704080c6202d81e588000c400312000c3e8004960b0110003000100a01d061500203042e000380201142000318102c5100689198800c8001174110569003404000c105110f1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 363159496 1250 363158246 363158251
    0x1e030327010e030a2d0609060b040501051909050910020c1e03070b04060203100e07020a020f0a1a031f08010e06010f120210120c2f030f071a0408090405 67
    0xc0d8000d04c0c11010a680b0520705249480c00b41d155156002c26100807810343e0400c1001d466080303541042128140e0030840c2c0603000c503100f0140550708203030001a91b81032a000ea85101d08035420083c00382d0b42044a1207000e04000703880d581a911400d1b4400c2c100112078401080d21004200090280170703a600009940303c10b0782601550075810900401c004100e121240766406035200c000166690703615914400801401c0d00708010514880c0700f000074241d000584080314038004c40310ba0030401c000308200042c01040f4050103014129102c0400b0500c02004083c47c1c20219440c1c0100d03104880068641a0041c542e2028840d607464070401211408144480c5001d4101d01d114200d88504180d20850526400c0380c0003030190300c200d0340001d8203d03c5903100034403c20404c0020b001d0101d84250040140503540543c0c10f00700064911213911b10480b100c00000e4001d4000a582803800c20f05000405070080802a0380164016407986544890f01e00f59a01c2640300d114110b031525100e009020403501d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 363160746 1250 363159496 363159499
    0x30804110f0411070605160807050a14030a020d050903091003092a030303060905040206090d0c050603010b0c010f050601170c1201090f050702010e06060409020f041119030b1e030327010e 82
    0x640c14a000995102c8c1c06540d01c088c19051095403a081c01000300c8985000c2040084488004014030034041000e8008111500e0010001c1c403050301c603800d466403203205150105a01925071038003003450754045d400c4410b910340119110403d03110700501580203642012000c0c03451a01d6031006104154042c0b240700090040307803404200914042d03010940701d00c00c110318203103c2c40d0401601d20400400b1005140a04000350005807203503920015150107401c0b03000d9120703155082015040c3c112000e803103894800c1c40c3c1655443c82e0343d5046115104030a0b80503007242c124000402c04515a1002400000d0003400b00c50b000040015000d00d10b0350840303601a0080f021a4103090380071002c0480011038581001044900280c0003140c6d00c001507420f64007206d0107030454201280088018000e80c09410007c4961140f006070744403401d021021141668078130fa5200503a121516400740e80e06080d0088000080e044a2400c008010141211503444011032061351070700daa80102564000b03450520b03c0e40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 363161996 1250 363160746 363160771
    0x402090a05070807080c0d1e11070c03110a1e06141603210e010509010b01050301030f241401050a06050c030301090c02120703090e060a03030804110f0411070605 71
    0x1042000180f18a002400d10010000d843e408583c0d603c482e0340444002030703000f1a04022480e081ca29950107580440b0400e103011380380c80c0352000c84540f0b490440d5009035000445040c3c141c01d6546201644584000d001d411040141e00442d14400034011800501c0a1440f0600c42074074008004041c1c40b505241c1d0b02c12850f00340544815800000014103905034107080806070407101209101d00380084440700411542000380a40d1843c0066120301d00071606c450003800154074050040d10075120031700c0000c00c0e0704215002c003c00b0461240500342d4028442c0a949946c50000031000e099904800662401c1381c60b540c01044a40740c0300c41008010440c50030443d080480001c4040e032240014441c0c0d040761034540d015003810390301c240008442141607141081e242d4020f410002c010060314040d000022401c0c0f0003003051031500d504034804507075140d55200c040f41d46545d01e404002c01500d90880e0004d08203101c055940e962400b68020001041c0b5846440d218281004e50a40707a029044071800704 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 363163246 1250 363161996 363162001
    0x50601050712030903020c0d1a0702061306023009070e0c12131b0801050709030f060b13181b1508090312010e0603010b0102010c051e071a0402090a05 66
    0x41d8110840c800360740b054100024004e00506040e410011403840326580154084901c82c10002c41c400013928000d040300448549585080f000e80ea1070310b0a45030700414010b40300340680002e015800030014000800c1641040000c00714043c2001d4902c100d1403c4080542020441540070070004100240031005501c00641000e6242c009144503040c1000111750070480040c54000140d50303c8081e9942c08454124880818040030345a503015024401b101c0d402d00300892a040d101e2641c15050300d401c401c4500004030944d4410380100002c2c14241d41040750504050705451192040c0842002c404000c0340c141c200500c2c0c420b0501034060751401c8448018402445540c0520400001c141901e052800c56612040c460510710701170310750f2081c4401044400814079140041c4001c2c050700c0142c0080c003a08142c81c0040e801da5452842481c0086e00503c00b1024054141c0d800403550300200c003c2d20b241c0001515a2010558000c145201030315549003404114145146200d612070002203080003d070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 363164496 1250 363163246 363163253
    0x512031e06092a0c0312061e0a06030b130608060702012706111209150a09150f0605330412030302131e050a06140d0207060204030b0a020408010506010507 68
    0x940480ca40f8030104010920001114000341040700e440700a140100c030f4481e00100c40300c00d50710504640d044d0107451001200304000d00d94504c1e550a869000340110581303401e00c2003c0740204080a400f5038881d48840b0240c4118030540710b0140508454000f80425151405010f400d40d019000da4018400b407440201d060504040c02c002e45103035102e04007050546120a041c2d05e50702a1842030003d614103941031008a40c0001030181d054080403480350041d036101d603450030803942c48620242c15511002c1c2c4114002c14203500038480081d40c0000000d500e6182c101192501c055040c00061411510820760542c03c844043c0d00c6000c3c0740900300d585440d00b08900200d1600d040440141810f8020038010180d4040d0b02d024806080e5110014808020036a03552011f400c45225003402038808400100c2c5a521074205c0c2c41540718040c103841d14210030701c41c19500070360141c40c01796403650b400d0102000241030740c11424040c0c240c40c140540c40f03074100340e5590b0845802904c00d80c10300c2010806000003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 363165746 1250 363164496 363164521
    0x1002070f0501090315020c012307120507050909040213020d02090f04060f0902070611032d01120b04020a03080408030a02010f020a091202040908030c0a02010b10080c070512031e0609 80
    0x85c201507000168489072484843c5024000c451190600084540700200402195042c1340d8810760080d5140f048980c03148200d8401c0b10010340c1c3c09000582d08005c140014200b000007650050300c0a0021000719650507c0740003240c120380d4500c544241c00003140001d525240324104aa040e04a80810843d071074030b9452820151a4071516860f280c01040e0f81d0140b00d2a41e0010207419200050f107a66490b14003050805640701d46420300003804c1d058011070700004000c2809041c0c2e41401240340c20b01581d3744030000d04450040017240e0202c0d81080202c001414a00500020001e4070021911203c44e503074041e0070b440c8051014403440d81705014103404c05500801c0c500859100d03868005200d181070011a0282c90606405400404000700344811a1101d40c01010102040e03402000490781c118204880c108102c401180050b1019010664401401c4000c180f81e62086e0101d441950350240303c06a03e0300f00711500341443d107c0c505188000c182c29042e080d4071880448419034140b0701005401e00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 363166996 1250 363165746 363165773
    0x316021512010e0703090818100c020a090914070f0302031c0e0f0409060e06100503060408040b13080106030f0b090613110d020307032108090a030305151002070f05010903 75
    0x100c2c1d6800000704d1a6580280d00c00c9074110340002489076503081c000c902d0280d03161002d1500340900c1c018440c14102c00e101e1148107031040c0c0e000f400307520998600301012001c2e029604080e1103007042c1840905101101300504401001070400310341545245004141c01d084454040c0811a104c1080a48159902003808a0104001c07520081d41c152a40003040003400582e800404091034104011802c020010f21036200b68900050038040c0303030b141c0c810b2689880041e030b0000d0035044d080c8014809442c00360054001c105140c0100034035507a0342c2c281a42036418642c8262495a412604181401181c015003540448090010501c0c1d0924080d080c8075041005000703058000c0030035144c1915510b12284454094000b011290b00644a00744010704000c0c0c1d000c407080c0e034292080c011000d5402000d03200d10456445001e0300020710661001c0d005002c0007880f0b00c0000801414103c8299550803028034020200c0c0d000b004054208416054500e005402040c1840a14681000001c2540004e0603 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 363168246 1250 363166996 363167009
    0xc1403180f03180108071715120a020f040b040b0a0b1903020a021c09171b040c050d0506130f090320100e0c0909030703090f060c0b070e03031602151201 67
    0x51960b81e50002210403002c2840c2c030a443c60500d8080c45842821236040c42e800003800c40799082100c5048588607660003e80c40c0003904003106c441d0a00e050b2070180e00c80e0801c9807000c0c00100305c00802c0380011702548a2504501440500403c175001c1a04800386814103400039428118034141d904040a03654079030103402c030a101c0707010b0401280c511b8401d100c40001042d1140c05241006103044015072540701c1032501c0d8141c41894169284503150a0180e000e024100361996031501c402960b051029210007403400e40c10295949801c0d02507000c510480300f034030742280c500007044401d80c83c0080600c64001e02000e10700b070310310030030080030300021904025003080f8503400941040401050360401c6440c001d070381da100d42c0140410010200100043c012a03102c1d6860f104899103c9040c66900b88281c002e800001d1104820b8000147d61616140e420003140e04141d0414070302980040d00e50b5101d01111560225444504000c40c1030090a0b4140001d4082c1054180065001c0c50300c040d800510582 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 363169496 1250 363168246 363168257
    0xd052112060d050c100c0308061008070f0c05030f03010314010b0108011403100c02060906010e090703020409050c030a080d06080a0503030708070c080a08070909051302040c1403180f031801 83
    0x40410608016028082d8006400010028402d040180c8600740b601b20030f401180e075844c0007580515002490488940b00e5031194142502c030344100303d8840020300850014810100c5200000c20800c02c06081c0e2000d840c1050780d0384c0c0d815441d10300c110311035122131140d0f00c0c0e040c81c0e607202c000e03038100300c01d84d056481c03284040074454a0074001a25111381c09a14440103868031f003425051740d5010504034400c401e01c1040340c0e0103990750780d8a890300e1030017203803c038400f03402c00c680034001450190403040e803150185048903144852100068101101003c007180d100a0008642d41102c10740d0090300028022a00680080759680c0c4540d1307124840140014200964500064201d070b000d100d4000380b043c2c0015a590702c900f2035040141c21a1010b50300003000c41d4280c180050700d4141ea02801303100d210040400d402c440720782d909000207060054940414480302c1da40c2100710a003100091840740d075261108140a0f2840f40d83e25062150380c8a007140a40c204001c407203030003101c0328100e404a0500317180c02c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 363170746 1250 363169496 363169519
    0x3060902120c0a0e09010e090c120a0f03030f1503020f0402040b040e061903030309110f030a120318060605040b0f011b031e1706060309120309030403020d05211206 72
    0x490314084e001d403503264040d00c44400032500301c01e0304070301138450f540d544120f80c01000640f08000195070301d4603110348182c2c048004000001c80020802e45a14031908000c2815071203280e81000360368002c1c25500960010348405c01c10740ca48142002c140c00ea0580f42180380c14189915208244a90300801170300901c0c2c0d9012610a0303c440d01401d0607245252200702000e916454018041c0403412001e4503040120324880b80e41340b60003052403003545001001007100c2c1e0620341e264800a0404c0c06a001459540c2158803040b000786480300c18010b100302c0d07001680c1810141080115000c0d60721207070150362800d400e2403a40c0d8210400e808000604102d89015203a45e2808442f00d02c12805c9200700c0c4e51081031002c06158000b180c802610901440701ca0042da688400e101160008981207282da60107a400812000c900800075600b250003201942d240c00c0d120f8010400340381c6600380c12905a40010f4144850034610101040b03114039014003945048401010070b0328000000d0b014501c40d0590350031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 363171996 1250 363170746 363170767
    0x4020712141305040908042d05040b090a050a0e07062111030402130b04020d0b0f01020604080d09060b03030309030408060907050102030702100e0904050102250506041b080604060c03060902120c 85
    0x1918000c1c90034800001034440034840301a84c1c480030300b2482c0300340c035008040401d4600d400c0c012f40100c1c001c064030b081c1580d0b9030b0011900c040c11010b03003500007251340c0380503c2078018414400340029120985079224141c0301c00034074a80070458402d0087c0d809103090b00041d040b142050403a90810740403280c0c03000c014044800e5000a108450610340d119200241c6020170900ba9000300ea0b0f4018115103925520540703900581c0c9815045400030103000c1c0c20001b0828101703c540c4034a8105020f040e001400d0540c503800700e407455200b41c8040e00340ba0b10120b010420f040d8100181a4401560360142104a24103000030f9564000d40c900284500e184010818080d48580d0386041c5203807009051229504250411074000d5100d50780c000007414603100600303014003245106100d010360080040105aa4544501030740501c3c40940c1d2801008009000400b144104136081c0214000c91001480e080524000f50440d900c0e41c0c0701660300c6006210000900451103034066005118000e0706070b84408505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 363173246 1250 363171996 363172013
    0x1608130801060f1d1e0912120906090f0c010503181c0f141209030702030d08090c0d0818060d020403110301060b07080301061b02040207121413050409 66
    0x100400c0c125031a0800005158101d8140ca900721002c12a2184590840b0b142030760b0140780407070301c1c103034010300d50072103481c40c884000b89580d071200c220400e0300e2041240c02802d4036244c1c072408000000082c14030a0050609061143c150440940b000030103003081c2d18036249484082c40d0040505020001c0000b400442030340c0040c070700e80b40b03615090764502c0c0090070300c01d120031041e003c85070001061041c0d180d503c00c0c0601a403455107454094901d040c01041800c41d82c4140c2c0051a044035400140200030040c0c0f801c0007420f1242c0c0c05502c1c1c1c0f100b1860460750f0b80789441c400308c40e41c1d842154207403072070f00200307410a0880d50021844580c4801d040d200c000456003d2050660040260344000380000c103200782c500c40c00c4400c4034100c00902c11039694002e07032581402103ea02600d6080c2c10070040209a0040c03000389407100408441c501c40f5080d6030006000ca0300100402c2d00c652081a901d510304e558042c81d01a0460000010b460802c0c40c4154070064140c03007800380d40d02640c0c1e25600d0a0a000c4841d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 363174496 1250 363173246 363173249
    0xa0201090b04080a12020a1d0609100c0515060d0605070e060d0f1b020c012304030605010801141614090d060b01090b120402130912050a0e06160813 65
    0x1c84441d030a0074a49451441980280b44a000103005180c1c0e400031141c2d03a0007160080382c02682d0300100d4031012200c3e4043e82d1003a54a8640c4070707004108041c0f464803410b500902e80d01c5651281c801408980c1070050804d518a00781080207550700042241ea03a49106110010940040780080c0e56684c8860903240c212910290950041c40450007080400e4160008148038400c203006001d8504248608074000c8410460000540c2001249894a52080c140f985120400c501030340b506c02d480c01442d84895005400903a641d946460040c001c4440074000c90200700c007580d04a001c0d13450b249441d50000c55000c04150100310700c8101c03042c50b0039404820345d0540f48004151182555191510301c00901a03000700602042e00c8c0100000c40e0513962003900c60250014040c00d45a650b42d508001a0040040d40d980040360348550580101d2480012881c0c90901c94542c83c1d50f48010840c0507006160250045116210800081260098070071410588030341c400c10300c5440b4111300d14038401400d503a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 363175746 1250 363174496 363174503
    0x1b0109020307061b050a051b0405010f09110d09080901260a1107060203090a02040605060a0c03210207200a050a050d060b1f0e04020c030901080a061707030b0109060e04080a020109 79
    0xb040121400c0c44400702c0c280e104d980310038401044400c111000d020642b04248620329182400b403408015076092a0040350094840c980c0c61850b041c4074041c494110b0f0700222003a1074441020500c0030095810520407140741100346608529240211010402020020315059440303403030310746090a2035000d8042c0c914503070b402203055460f0316221828075500c40080d0420f07480350342401ca000a0508003031088401803901c43ea940c0d0030b0115541c80030742e42511414800f4102d01c10b83c200c403080c408140d101a000d0684601000c1c0c0903160300d13000081d0100745060b00544601840403040013540d99200350401280c01c183d541c40300c2c0384403e0400b00c0041000c4100719401c851302e0440d01e11141403503c01c0d00c0b003e51702501c80c8401d0100040904c0205e0040a9044120345e20403c04031100c0d6004070021a4130900703400700450615283c0340401010b07100140340240503800018241f041000c0720304018050240345004010312071514141c460358a1010b00041d004032270028140300b11038030079000b107592941c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 363176996 1250 363175746 363175753
    0x305150d02191a09040b010903031704050a021003020a02010e03030c070b060d0602040b04060305090c0901030221070f170c01020a1b080a0b0429010b0903030c0609031b0109020307061b05 82
    0x80f6140c441e0550b1200e0005407145190450104c40396008010300c0702603079019503c43c0d1307030028001c0c20300d1541007028005540320701c1107012050051fa65189c0300c4110107481c0d6800740c1c5407003c610003c0c0c00c5d01c0002654004c10382044c01046131100c144410b6948d41034109061052584079007000c40d03600b2086000c0904000e00009010030b8038079001000b00115001036800708100ea40d50120782d52681d080200b941d80c0501c0d100b0042001d440c1a07085007a480b41c0601c1d007410440108060145040c003168800b01c0f80381d020020400c03109046243d2030750313a50341c9a0054550380590200003034513024441d030010013040c000c1b03180d1050780d030b90900c1150180060500320b509855003410650481c2004030f42c122000060341c40c841d52030308050032620f10088201080c00b002a402d2407000b00e000d400400302d881d0036100a02044071080301c00c210141c081c4e5965405103603280c40104e110041d00d010704c0c0307203100c81c1d0b81000d007030300d0050318000741c0030040300d20601d000b0082d180c4200043c02c1b5000c450001800510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 363178246 1250 363176996 363177029
    0xd03021c14031812030408070b090c040e010c02010b06190513120b010f05122e020d0614030616030504060608100605010e0a0303080f06010c0b0f04030305150d0219 72
    0x41e00301120705054440c04c948010140001c0440f0f544403c0314010081c0c802400000300050080c0b00040e085403030030040d94044d1000f1000300d411111040003110721a910b4030140d062140d020310900c0002e038010341302c01d89080581c4440100314005003400008008002030f441e100140040d8940014103488452000b0a649908020b00d1700d0702c0030b01a60041c000402000a21482d05485109810848101030a83da28440484000d54402c40702c2008544107185d05a440484480c801800b070b041602c0c81c0090844d042425191041c1c0580f20020b0181d4046814044001c04000d4081401081c0d85000b052903550740c6011005001c40380c1c0003801341e115003a90740382504220381044094800c02c1c0d803200b0380c00311017000300803204105101c042c01052503070020400e05144c1d040c02641c0001c2c103050a4124840a5079412110b03a0300711882c000118041c0140020540e050145036009034410000340e904500100c001900609040c038028030489500107042c000255071040040280048002500d011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 363179496 1250 363178246 363178261
    0x1f030e030408010e120304031d150f0c01060909031e120609050711010209010f0516021002100509152707081621021903080a0c030e0d03021c1403 64
    0xd02c400d000d83c01d0305009000c0284500444038007903a07c550382690b141341564940640d0143d03449507810840341c000002510003001801c0072401480481c440640321507880e00080232050840b19a0b4116a01c0c0302e04210200d00801d070310917842880641020108080c03180c4034142a074004000c04140c14025047c001c0000d4001441e40c04144034081640b00c01c40203d100000382400c03803049410b00c2d408a031038019100305a0b4404d90280c480105900700c2010034074860780000342c004182c4409800140e00c10516810354000c0c0380601500110400014409846482003035010f03400020046640510554999804032280c88a150340d8903118509442c001030716500c0e80303034035003048102420501c00e0304000040c41f102e0200e10303140c2803884132045000c164555800c10a2012094040320803103d01d203240440482c490000038060704160303441d0104140d84030302e005090501000f614a120b031803c9603d10700403907004030b20000001c2c4142000142d0f4004003006a8404c01340c454441c4103c0300200030071020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 363180746 1250 363179496 363179501
    0x15020f0a1103011a0108070e03030405041d07090510060c05160305060912120609040c180902041118060c071a090a270903030209130902090705091f030e03040801 71
    0x888800d90080c130405003000a014102400c0020130340c00201154000703010248180301503a444580102501d1405654a0009d0140e504030404942608500c1002d084404420499417000b0001444284080d14051011105c1e0b940b640c07062030f0600c030074040e855081081c113210401c07403c83d1441e000c00046849040c090703541c02084a500a09101c0d8246140b40c0003064070507102e40760001d07203990040e03640348020301400c448040d00450b04103046480204d582e181092750201101010400020b200401d8010001a9000103c5070054124204200340e05e881d0340019007001d000d0203480b60f40c4d8034044254000d2030080d1980c04003900c282040420f59195600768000c00266000300e4062003115119071a8070441c074200742c450051840751040c5003c086000350401d1007001e00070300740141020140030104403802a5600705051640e51076042c0011803a080407010707005075092501504140d051008a6450340301e00042d100d0b851030440500c0d07840d91290700002403c3ca5008103036500c41e130355840010701 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 363181996 1250 363180746 363180773
    0xe010c29071103040909020d05030a050c0712110409020112060909050d082403013c021903050405010204030602160b0703050403050f070302070b04081006120c15020f0a 74
    0x110000350408201c8491040000038480c1c16031201842ca050b10b42201080100440d03407040b41c20850340040c08000c10b0050010f841ea518031034070341b1551a00c0c0d144100f42082c845030410001055a201c0c014081030062143c01214081a43c00092200042c001a144054100c08051082e41001d83c042603031240b40d04860f041038412002c44800e8400082d00b078840040c21a08030300e0301404d90350806d42d43d982c500700080030320001a00010f5840006460401c01001202c06000302d807610312300c19602161100344840041e915440e00710700f051440080400c0740c5004940d5030082503258004178091040c2941120002d6900c042c04543c0e034a1200d44001c0602a031813811b4480d2010300c000910f0881c06800b40600c5942d060342d0340c91a051109402d6500764000010075030031842055404622000e4081c002c2c4003a20004004008404c01d0b00079010507103115400854864801c1c901800004400321140f00644040801c600c12491000e42d00300d00d02010990403002510074217003003009100a0016480 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 363183246 1250 363181996 363182063
    0x115050d0603060e2505091603090209310507120c050d0321110409020304080c0d02060a0609060503121e0f071406130b060109080a050601091404030c030e010c 70
    0x5005071750454041e0008107503485071540201d01040021101821940c00109051050500080c42c1c0c00540100e6004003080b268102c0a15004040c40c02c0c0418600700f06001d408000b4401440e6240c0f03503502500c50000c1d10420307401c140390b090940c041028101c0b1410180c00007806400b41900c00b07040090901551213803401100c10510641c034503030000b40c0502d1a00300c01e5400c0d0349250a00e81000d590003588010025924200c0511981c2040f600500107032000842c580d009005505045500804070703a46607100c440c600349010780400250700c02084c070064120003800081d4880d59100001103200382c0114482c0b00308440003404030050402c1c100580070150090041c2510081d4030540565900402e0f1a80040e40144e000410001114903400da98014010b14040081031350b01c0c2c46080c13410500c44021130312034004900610002c00c051041500707000303030a1641c1200b42416140640307103182110020f41000612114041d050340101303241e05005521080c17400c006021114a80c0d8121403024031070303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 363184496 1250 363183246 363183283
    0x90c11011b080c040f1a0c01020c01060608061804330504060c0309111e03070909140705011b110904060b10020115170a0f0f0506010503060115050d0603060e 69
    0x850701c40c203d605031819200a00032100802d401c10501e00013091044075210080700702000407501600c4280003605801d84000004107299013014000391800800401d10b50281410640300808a00c501000c83d802a4024003038001e003148451401004a800c5c020000c920340c011170000e08844640d07030055102c0ca0184000b040320625440b011401d580601502800c002c0000c42004c440d450035120304e0500c403060a112180c030a400c0700c0440d00707004043d80008043e6556880c902d0a114035100107150543c45074000d00040c0c2d003400300281c50b00180515030307031810224805900400100c410300402241000304465203a18291a15002400035403038440c1c0140c1c030b0000c88080481c01401407030036012138800754003003070303070810500d401000313000000c0035810b01c2030320300c2e90f0041200b540710400c85d00d0040290340345107081800c00078503001c01a44094001d44c4560010490981114003159542c8000d1500701d907151584884440600829000542403e25003a030306c101025001640981240405402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 363185746 1250 363184496 363184501
    0x70303180c030b100b0f0306100903021513050f0d2904290f0105040e0109060203011205060f0108031b010b0a180b01050903100b0117010e0103030e040213090c11011b08 74
    0x4216a50145448403901c2500610102d603449c03800460b880308001e0203280031284160780b9000940340f00001c1c41c00080c1040002903070308220030011001405000c064480e94419050ba501180c00000c8914014007941c442d40303650090094481402049039145c07001401c81420f041c20120800e844d2524000c0716190304004003103000b24404c0b0382d10300c1360480310701b1848160302c0d04081c08060008120241481e560390046c07040016094800303903003e000c80c083c15001c0a8803510b4601d207000d401400035076080040304010005220000304540c500d801d10070459502d82c01900c00280074017400c288141c1c3c0440041ca01041d0b600c0c00201020b101001d8038000c1c010440d040005503058860110201d4041c0c10111150001d04000e400c0081001da0600d815400f040b005c4503d00c09a010a81002880a404d200100203042d408490703400002400c403821403074903240ca400d5416046031881600100c0c1e450381174100c8201e0103940c0c083da052100900a000460241d69500c1d01068481034500106100001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 363186996 1250 363185746 363185759
    0x607080f090a03110a0804090506031203090c130608100c200303040209100e0903090906010f1704030905040e010203010f0e0103170f2a060705030c070303180c030b10 73
    0x10103030040e0304100252000712043e44003155000611549840544103032450000002c05410081c002061101800507141c01c208007018200322404200480d103090900500c45181d9011910414100e01140d4481001d60354070314000107054590702070025802035511180101500340c00015100710543c2c1d902d10b0520074600c00368441401506094800e0f401031000800600b0311510b034075080007081d08800c480d6580c07500340c07940c2b11000f182c0450054001040c1d280b054103004001f0754000741c0908218980d110f11800081601042c11a58000e0444880106041c940103480400c09802c0244c01807010399012442c55010790710a10030b02e400025105400100c0c08000710041303060340e0303100c8400b80020304616100f100d01e41251914600300c030000c04c0ba8504a007081c0608079507010400441e85c0b0900364449016042c0140200300c401400313020000c01609a2920044840131a45800d0011340840110000c110410100000138070320082400c010040c03200a000052164150b10301c0580a142c80d00c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 363188246 1250 363186996 363187021
    0x412020a090507050a0e061b03040911090f0d11130605031006030809010f18030b0f0a050712020c07120c030b090a0308070c08120c0901020c1801060806060f0c060708 73
    0x3c41001c0001c82c14007244040c984100d440d01603110303004050a091034100c42c564200c0d508042220b2000c1d500004040010015038010700b5055108078003083e06000400c00815403200740c141d81c480c070814103502c16004014400d484400790600260815083e1007800c0704181c010301050007843c0c820700c2841484100c0030401d0203118266544501c10701e040c020310714015034011000500c0721040c0024144005034003c010b01100e4011401180b220040f0304280411240c07010f4003030310200d80c1c0740c140810001c1d401c0d00000b01d000000c205000040c2d640140051349810410b00e03400150a014820054409005c02555841c090764011b034071103195501c802d400140d40e9480700d01e000300895500400100d400f80214480781c1341c05d0242100da441c0c5040706031881054541200c03044000400810408810350307042144107201c480030340304902d4406070704241d00d0348558140b1030340e000c006000c80010215128041517036014440000c48940f1004220300c0301e500d0b18000c50f01e0000084092001400340000903 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 363189496 1250 363188246 363188251
    0x1021203060d0206031305011103270606151e0c01050609041509030504150314070e090a0b150d020c010b09010b19110304080105090606030d0f0509010909020412020a0905 75
    0x410200b0041c6290303007403011a402c0213064501c2d0745040034030a00411828001c0c00c2000a01030165a6245040c075100c1c1000c00d041074424201105001c25810302103030008030141c210808071891003e0410410092100d80300700b41401c141c94042c4903100707800d40c805102600744100310000a00c0340741d68400c280080814121780107808503a1503001c1e00e00c9000e0079130168200a0081c81c02500d026101d814004283d41c900c101c00d07001a070b031000c0640070040c514000e80d800003420301e0144401c0b50140c0008050307441c00303070400306102d54400c01c0d200680d035258a404243d0480045858484104900c454025007000c26460480c0d4200364044401d450084606d5041e100b0041090b070a01d040e4107252031071110565501c0040c40710b890036652130f6490410140008051403030010406180011016040200c0a05040d000341d0141082841803a040200e140548140e40f0302030f03445004000c0100c4940c42c90b0761103400c0c60b52001134003040300354856131611610b0380207840b000c4441c2e594000403021107804 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 363190746 1250 363189496 363189499
    0x30903030307050a030f02030f0405060f0903120a0612080d0609051003030c0314030a060512030c03040510140307030c0f0c0206180402090a080307140f0d050c0f1204050102120306 79
    0x2040011002ca020b50060003c030300b41441c00042202202d1410b030100d0740140c0f401d00711035102d402000104034080003015880401404041d0640c01c1c218003540ea04e028030051b90013007130a03080006071542a160702c1900140006441003030191400d08200856078485040300744c80f41d081c4100450284c81c2400f0340d0303004021120b40e09007064515101201c0300301034080d0440c00c102c286d40d107480100211401650081c2040580046e03194075000402c000d14944c3c032100c44443c0c00034045150070f00e002006031812200181c0302c100c40305070300700c01c1201c0c0c54120542040352882e000c02440010b56041d4808448040143c035094500c01d0740d80710950b4040c0c0c48030b90081d0700c0501000302160f021031603130b0706890200e40130f0f1005d420103001030006003d0341e00039048112140c0c00400c41001340310702c2d443c1010f090912080944000c8403101002034503010308464000c140600001c00210a03103082080021180e242c0080e07804041c0c48081680041d4400e10410f40184281c40045803203504040c11039024440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 363191996 1250 363190746 363190753
    0x90c0e09192304120305090705130e010f02041502070f091d0d020604120507020d060b03030d0f150f030f11130e010605010f0f1b0305070c0b04180606020606040f0b0a0f090509030903 80
    0x902010400c0440740700d100200ada540305c00401140000074010394060000703800700980c40e0341c00d00650000119011505008551004004009001d40060101d0943e4100341002ca110002181c501d00c1d2503110895070030b010720441c5928000c545d40810803c0c000c1e885610f07074000f0280300340fa0841c1d05000d04900a9404644031070b510000400e9540060b50140f0040c7c1500d06080903451004116410074119080c5c079a210221040542e0507011221701601e1900450052281503441e100c108494400d00100341c5400703482520802c6e0382c0c64000c44564a82081c1c00e001c410f521240641c064000382c46140d02041c41080c03c10b400c94007a803109518030f05c13241c0d5424051550300346803c03560654000c00707500303009003081180c0102e41c6035441c00c0c018081c040d0300c80744c2d62440c1920915a4054003203200403214074014080c80750543c00700d00d45800071411140499004030365688080240742d802c2c529940070030745032000150504c800310264121034600000b04000d599021019440c0d10800141d280d00d0340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 363193246 1250 363191996 363191999
    0x1709040c050f16031812060c030606051b010b15090f0405090d1b08030c030f0106020d08160908010c0e1203031012060f0213090c0e091923041203050907 67
    0x143d100070705507503402072403c80c1d11403281c614039181105e0580c02444c81d000003c203809042c03011600030704404442610341048540d1401c18020720b41d0090034904401050803005847c0314041c00d4102054a600c010040c442c0c03a990489019180e61100180900911185400c2d400d140352501c1164814040103000d442c1c1c150102c00104c41050000508140c921340c040301d80790104100d28041e600c280c1041c1444c0360b590070824145291100c050380f1420440d48a040c2c10006154000300c400d8012100a22445114480310f00664141015410a003810344c60200d050510940c000e548960100e801c1c1c03980f034007001d440c01d8816128030046840c42c40081c410305040141010554140d40c0a6004400000d44c55007400809170a0b43c1c0310104035002c0d07808250082c0508500c80c49a03204040070b604240861100c070700c0c0030504c07000740142803614945c0602e221040c10b00c240d8112008400b03070a245140212502000340c120000162010303640c51501140410160780280b0481c0d000341440c000518851303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 363194496 1250 363193246 363193267
    0x60604050c0906070c031e020a08071d0601020a2f0405040210050318011505100c050d0e042a0818030405221b020f071a090d1709040c050f 61
    0xa03031060401300e80078245904000b000c91807050040c101640751f00350140f0142c078180104204040e01e03421103d000d070428a0100a1510742c28035a40c2591000090804160b0381c2c0f00050b802c141111201620072032480c10700e110004000d1195215150048600d51003040c0f0b0034003440112001194029048120b0f4403084040d81e006001543e03114280c40803501250102c2d546040c29038034900300c0340d00c0c0b04615080921880ca040e080380e0403000400d10b040d180641e001e8580c541d940e860130054000b0700207402c04c00724650b02c454100079018004034030303c440841c45109403c00303618142d8880c40700103240900800c541c20b80c0080082d401d504200020b60403e0700381020425000b42c400c0039050401600c80b40108052180d0140d681040025107800c11681c0340604080d05001e44441c0203d0207800400051010401d202c40c0030140c4104914103607124160840825480e503c030b0f00001e0013004581840301d011700c0c6614002c2460307910a8070207010004182c80151294080d010300404e0103002401140c144 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 363195746 1250 363194496 363194509
    0x70302040b1b0a020a03140d050715050606040801021b16180b0a0e0108010b03060705030610112b110c01090b2d3004030c05070801060f0305060604050c09 68
    0x1d800e101410f9500001040d4005241001254030803142c000b2402025110f4040501ca1191a07001c1410400d1034103c1d2961012603580460700b05410882d9141c012800c1c58940c441514080c2800d00000c656030840d44440301e04860300700002803154440da0f441411030341c95010340d0341e00700d400d03081c0201191040118040c01500d5404042900038016001c005001c0700f15940a0740201400000001c01c034111130300380f50800ba001001c1100713000d010014461207071208031070300140c01c01e185002000c511400c60704e542808410030301541100e000c40103980320441c0030800d05108000d2910790704002e90040c0c0203291035041195115010407180b500c01c1101c00762040050401003850a00790111b00700901ea2010b81c401880d0440700da083d00440c0303440a1528500310300d903154214070203183c055080c24545000301440180700508100403091808108201003203200042e1400b00000e1012540350302207850340c52030318401520240318900c0810610308007031107901e024088000c8642d01d4000d004060081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 363196996 1250 363195746 363195787
    0x1030b07051306030e16152102030f07020708010e0d030b060c060103120e121e0304091b1412070e060f0d090b22020907091206060e070302040b 63
    0x40c041d080020b20003000881d41500050800c5032000945401140c8075603103044040d65800c0380320300040d0011b008100d40501c030011954600d15040c4218200300181c3c41d10201d12021444901d4004006d200455618440051051049500315070a1954440f60ba50903141e03200700e00c20340e54112010140d03081f842030300701440c00c400c0500144e10309a90849072030300e0118240e1040d52152180740a41051907448400000713400350845a160400d22070f4480944c0700c0e0104100468070040000c42600f074118107009403001010b10740000c01c0300640e8400b100602545e03400c40c1d54002130b0701900c0740c400641030342c045e1200904840703100b030450b664044064a641c0f00c0d00302800d5000100b40083e0845400030802001210540b890204e1518a2880c02c1c9291301806040802c0385484400ca0000d5401c04024140b40290110348581482d2102c250603244040359801801008208034180304c117120003600000d080b50711100042d105565081c50850803400b4074080c04165032402c02070080701c40c0600071901c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 363198246 1250 363196996 363197011
    0xc032404121704030305090f1f2007030801090507050703080f09011b02010e0c031c120204030f03030902030c040501080a0602070c080d020d02010606090308040512101805060c0703020601030b 84
    0x10b07030b40c2494940d0506101142c1c1100082d032220208031880c0d0b0700780960380c40c3c81510340040c162030300386051300e20360351000d4044a80165995030b10004401e0300c0c02400d10380404e000007820781c0c502190600400c55202402160141410300d40440c40c0544120200c4121702e030165200c40306034982405038981c500f00a40001005d41d200d404031070408070a0104840200000d40000801824440700542041070004426100c2d411020501000d0030030404140340040305071520103008509076207218001d018540014280316411140e0b6820076405501500f1060300840031100c000c0d03420b00c204800e1f50024041d0b403200f40c001401400001d8065009040210322800a54400f40d0b1503080b5149001c1200c03150b840142c0c41034603181031003902882610050700031460702c1e05031141152103050b03c07031250b880784502800302801f424070041c10a01c00185500c80c2007000388030f5001c00020900c1c803010207900c2941d00303006400114500a030000c0031518002c3d419009482941e2130750b00d07804906040141510b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 363199496 1250 363198246 363198257
    0xb010c0203010513031403071407051f0c0e040b06040510020a060c090f06030b010c080a030b0a0303050c0712020d020108090f030a090e01210b09030702120c03240412 73
    0x4000695080c06814420720b440f02c2e005441045174180202241003007142d82c40b181d42e00300203101c29668440303000c1c5c28041072500300381d6591040b8a000d03442d01c608900d01d80c2002486815800703100304650010b4655800c60780d156245000c00238104001c8070384901c11282d119200f00810441350030032000c2552100400e0044e9a6a030b4601d86405c4103030340d0822a064001001c550b010321803041d00c051010041d042d145000c00000c440b400c0081d05008014501403c0083c010031107203000303440780d00000036060000c6c2920540c5590707440d003e0103a40101000050a00130010702007996041007060324891500100004403070720b0160015200c40310050060100b60050601201d8050000c200921480010f0354511005c41e180044d10202d496042e001501c943c0c80c0e050425003c00510a0080c01503034100302d4420207500d510001a02c1d40c41140c0000b50081404000780310500800300d24001444000d0302998104200304c0b40010a804c0401400024450094040340118150125074800480c0300d0502 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 363200746 1250 363199496 363199517
    0x906091009060e070f02070f03081b1519091e080405100e0a0608092a12030715060e0a020706021b0f0106050f0604060e040204150507110a0312030b01 66
    0x4038010395803580c12400c101c0043d0400c0c4100d2a40c0210142c100d95800d00c0603204481c1480840e9448030000d10001d044000046a11641e1101c0140c0f081400c01080d41103030f84040c0b40d29004090b0400403140c80500c00c0351a1844032080c122802401045540050301c505403141e03428411030b050300f01200940c6c42d0314080c0710226907511441c51403003240e0101d888080c003001468041240f00d034019002a0100200101400781d81d69000a03410740060300340c034422000c14000c90b00e91201c8003a056205502004032446d41e016541c0100042028900640101c24444000400c0301c09880c00d51207081682041c0c540041c050071480d60180101c80e1048201506e1b007611f120380c2c1c04d42e60341e011206481c0d68001a1001541910900c03504004100695480741704a1040c000140c03075000324850340c024800d035038800c1c115a60710790341254041e0911341005c0303441c03102c0050000e1441e04400000c840d1255810151480c41c580f03000e08034216540101044003a4140d410304070042c0164018003810700c00303007442 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 363201996 1250 363200746 363200759
    0x70b0307091e050a1d090102040b0313030c0b1006110303060f0105070c03150203060310060509070e040e030c030c16080c0f030a0609081c020c07050f0105070602040303030605150909060910 83
    0xb01380e005001e02040784a907003891721039034088140701901d003007004da104010811603102c445090b00d52060040e521029800b85a06041da021703903203250004c3c4080300c2841001440e95680c0303015800d07101c0940d103810810b40c4d07005aa603501c2c8800d803521a803189000701500800e6100fa0300801440e40300e1013111200d036035280e40780543c0d14520301020500d650080304000b07075400d041120441c03500c44443d00744001860b01d40815031040010f014a801c001d90908907030210744540d00308d01d00c851282d804680d034480d42084116240c3e0408408101503009454401070300c2e119008071103055074400e0000c0c111141004e4100807224603601d01143d01402031824040105045110700220a0b02490b01035a030b8000080c0204502201510000e0351540305100d080c0d1070f10300014441d4107580703064070707000c500c20502001a50381c0c1c050040002c0c10240001008410151315070082011a502501c04007a4410502c0c0c0303610050185c1c0d800c4a1304104808005142032074640852034014a143e01c0b075200391529000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 363203246 1250 363201996 363202009
    0xe06060708130302040c0c0c0504050901140901150f0b03070c030e091602010e03070c1202030f030a09060206070804050a120302160c050a050108010821120403030e070b0307091e05 79
    0x150040b0103820b00075410419400c0901810070900d1042c0f501c00e0500c00c0c160360704400821540501030160ba13480000400b030070005d501181d1030105803480d0880c1b070b192070070f1414040c11150043c004400c54008002035400c1960320100d00362807494001e61f08640d101c1004444060380c0d24815000c00603112207020031603c51031006401502c0501894898070900c480103401e507084d040c020102d60b801000210040791070000000240e840a60507074449445500000340342000742045007495010003d030210305c1c030390011402e200b220b0868003a940c031aa10b04005a5100c0f0301100e020b030a42e0061010280020fa10360442c03483e8080e24200142019504002c405510400ea02d00b100d034182c00030310501003171825490501c01001c09180a0284d58140314655448404001d4454049442c1d0200c03a42c0781c040b200c1c250b403199941c0c81c07913046480c58141002405072a0120303004002c1c0c003440e6008208503060030100d921030107140c0c0b20032841e00d180c0320803202c1013000121116a05168490085500c1d40c0300c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 363204496 1250 363203246 363203257
    0x30209090607080c0c12070203070905071206090c0e04020304021915030f02040506040b0c07051905100e09072001060305060f0907030b01050f04020705120a12020309070e06060708 79
    0x310003440303540b400440103042c40c031000d00928440e0f00240080d58450340c00007121008030704451001134442d074003803011924102064004101d21070a08042048555004039150f100001401c41884040d03507520a1004070303100001c02c030002480c5030602035a24145030300110f41043c800350407809040c2ca0038a172442150166003000000c40b00031440000106d5060160502c0f241e1215011841c080ca4100041c55911484c0b04e042c14410011420755880c55042c451030b001000060318010302413100c103000c04e002c40110b002d2644150f0b200e9201608041c812080d103003044a002e00040907689804e98151460214207007585101120031110700a510401c2c0510001944114010101c0c4c6c1070500245812a0004010380b0391036001040030000b0a145c20582c50440f002990b203000b05081c0324000c14080e1183c44405422445845018444041c070303c40100350340c1e43d0a60310621115090050031081c0e21080c0c42c80d208651051030f09014001140c2076040d000703e4014003207403500c0007942e9003910300c0d00704 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 363205746 1250 363204496 363204511
    0x30a0614100e130210050c01020703020a1218030602161a0901110c0a03030506040623040606110a060506010c15150512061906050a0902070c0f030c0e040309030209 72
    0x4403040c404550034881d544405444a071500442d1450012040052150070910192196813060104042c3c01d018a080306c0c080e840e044000d660740c40c40380c10060364404008078200c44810410740b0502c01c02e0321800d0b0309803940b01049040a10360345140c5a02e0003942040c40f820030003083c41408840001d02c83c1407500881d40c00c640124a861030075010a50031503009107403402c2400303000c01c6802e22200021621844440c0d01d400c00188070b44941000c94000d0a86404c00c81c1d459058115140c12500d02d002c0b51660004201c6d02401007684640313046521200000044c041907005200202c002129500050391092040c98459400007580c0c640030041d484070208038819540d42c2d0200d007101c0c96188038100113880c00395451610304005199943c0d6510006254504a15000030308880394805604440d009000c01040303035107115294005030000b0751000c0c0b01202e408505850006d40344445500400c01c4a80140b24055400d280502c03180300e80c08010803c40030809030301000702c016030b5440c0610340179001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 363206996 1250 363205746 363205781
    0xf01060608010e01050103020f1603020705090405101505061605210d05091207030c0c0e1603180b010614040506120405010c0e10051c0f09021c030905010509030a06 72
    0x50102011000f140c180c0066040600401004140c0b03034030345044904d482c100040c0d001c0c0100382810220f003410541e400143c0c0c400d13000710500081c40400100603503a001600c1c1d080045a680605401d4a00c0350303803080c3c640244050082c02c18401c40c1500c506580c034010070544410160400e0b00100001801c44546c10000c8003041405421140713114240e4031182d40401030001c6030442840280500a0010003020004400700078020001101c105600408240582c16074a040c8100c002d03800075200c01590b00000d2800010408022040c1e100f07000c0c180e003000c6e01241503403e01c8030465801803a80c80b8a13503600001c200010300c2d6100c200003864031091403160744509091030b2402a00750340b030034000d020130018221800503242e5905000641a820700f400c206556600a00001250109401a00c240a03146c88820f900204080d000350000d00d00c21a403289040214089030781c030a418080e000340009034292000d1015501410080044200003000c8641400780381ea036500a4138a0b400c0a00702410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 363208246 1250 363206996 363206999
    0x1804170a050f0a090e0f041109060612040c06030c08040c21140105040204060b1c021809010311030c10050a050a0c060207050c010905030102070201020307061104030c1d070f12090201020f0106060801 87
    0x1500100058000504052242e51b1b41013544501d034101d190f20300443d01c0707040c80c40701003032559840d6021100d00c1c203524000080d644c605402d10000d05001031280d4800f203420200c103000005d2140c0140380c4190f0f40f1004402d402c1d070038143d40b0f803849100743c3c41c18100801c141c02ca1601003024a60641d0f41260500b00202c1c2c0c5241500c18041520761030350002030380c0b04090202e1032003440d403408548805200d101c0300588404c600e1132050741c01c0b42880419a00040d41100100c240000e100c00821800c00640441d0300c41c0c0803110a000c0c07059134a121090026406000d94071080e0302c94030017821062218070b0042882c0d00c0d146c403818100da001e08021a8503903c40304640401d9604070300040d0041c10114000c40c1130030050b80006c1e44901c0303440d100405488d51011203641d50100001601c0c041e540040840c2c0c03450303840340300e00d450040540c003008806924400004444c83e210f1011444828401d43e500b911040f061440712000d041140012415806103804c450303074030442440b540c002041e0340d0f83c1d200201e5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 363209496 1250 363208246 363208259
    0x60408030a021e1506011b08040801200301060804020303071703090106230f060c1f0b030d0c030507060623120706020706081801050c091804170a050f0a09 68
    0x140c0f5400074094043c1c883c0380da440d02c105000c83c9200c0d03030758610250124140d56620040300c500c0c55440708242816150820340c0c3c140034078240030303005482c0020020444200c240222a10741e40b184030800391020803c2005024441c17242c40710f1a0032510240403a0b0906416a680700c030f0802550201e04001d2401008102d02c0d071209000b2080102018600740035040d0a0258088001d41542d421500840c100340e09403015840d440201da034039892030b1054954189640242081c420203110701c11000f541411024007007840c0210328400781c451552907a10380b500e10741da002d94540d0011002a1140307a914200002c034040c02d5041c030303601400610905400b5000400c200180d07011400010b9801d40d0045c00e043c84920b4001603044251080b42c10f000304a43d507030f0708482c03814000c45802c00c8415404d01040c84548240f01000e8118000102c80700610840200d04c03040054400b1076010303080c0c075800742c0c1484130754010500902c903100306807030010300d410b00b40804506164844802034002071000322041080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 363210746 1250 363209496 363209503
    0xd050705060304063c0b0f03120a0f0923131409070b031006140c01020715060b09150a1701030f021513050f0a03050a0606150903031407020102010b060408030a02 71
    0x200c45003040800a00541c040c3c0d45e05c100d07551602da00b10310036500d0340c8100c0159605450079445160081c1120038030450b604822006030401200f0601056520b4602c14505000700d44d030318103403180c41d918640d06a120032400429203800140c85900f015502810381403601c414042c0003524100c2100e00c00b00350a006c0751035441c201c0140c1c4004c4500d80d0500510003586001301d607107c121001e0b807401c0407603222801036041c514030480d8080c404d01e6200144100401c01c0e20184000e00d440f522508010307075030799948500d903030b449070034403666000049404c992055001c0c50003a00c00108140340410010780181c0c1b0b07001079088281c10a581c0440340c0c0d0700880031890080d6400c08141c03410281c3c0d17410b00c42c02103541014100c05000f03031841034012000316000c1d5140d404c946070095400070111402c01e9a5410200c0041c1404d0040e1307030710590921843c68110303024030103400c1165810760711011960400a000360040d0003000e0124119501c940207104039640d110050000b404901001e540d64a0408074040e26 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 363211996 1250 363210746 363210791
    0x6030c0801090305041202060f0301030b060405010b0403260c07060e03060a0606090e0703090606150e010504050a0905100f08030a0f0309030e04050a0e0f0309010905030114060d05070506030406 85
    0x503810301ca120700020b13600c041580d04880c95031070300c00c0341c094013480002c0740c40c0a00c0c02c0507074110360003200004c140400203481e14040c0034103a41c100403076621050030740300744e00c1b6500014121800c6140624440d110340c2d40070070411410b0030410340c00e1400050900303052001d80c2d03004500143c85900900300914040c8100d540214020004000641c41c080c030140140d6003078030800c0c0b03440c8a00800180402e001ea0485800700da1301a40c100301c2c10381c603a068008451300f80b00101c400554024184203040d40150206c0d01503a00080030941100c1c90420084040c12009003044d1501007401d40c00103281d0501c010900c042c1520401840e00e0b1172038074800034032000c6120041b0f070425040900c8003000c01d800035044a50b0000c1a07402040e10b540340c40b54000036010701c081080252013410b58010b60204084007614100c3d00903a80c0018242c0e89070201402d03034030030049401d544000a40820070300e143c0004040b6807503203d601a40c1080e0740d1500099840d4004440648050303449020700c1c0801400c2004040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 363213246 1250 363211996 363212009
    0x50a0212030103050c0909190b070f090f18090f3912030e0d14300702011106010605070605060303120a020c01060e01030f03030507020a080f250606030c 67
    0x41c25503245440380c1c1da45102120710b45005402241c0401c6c008103050207040c0444d40520241340c0c8010041c50305402020048903004005a00c0500756500c403841840307000100d4081c0214640e825081408801e41031071001c140d68940c50303403070300480000b40e02d800384980d50718012941c1c0440302d8a2415a00383c2d613500f4075081d540190000705000c1d0700c0c502080310f050a9079a402580010f168152038251a00c001c1075142076400b0130312030040d03000c004007851004a070007840019540c815040680c1c0001c280341010325555000785030000c0780d201e0f80c02c81c806003a426005240c540b030361442c2c04071000e04012081c1c00020000f48006107c4043c060345000d01c54001300150000c40c0344c4813819202c0b01e803818014100c900d0154001960041e20b110941000b406030048010b25800e07560340c0d25018195009009040700030074203000015008500216282301129000400d0ba07280100c003068002241e48a102020307500324241001140301d401a050900381c080c8540e01c001003603030460406098a000e02d074440c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 363214496 1250 363213246 363213283
    0x6050102150c030c070f05010b01030c0c050a0f0302010603080a0903050c011407170c1f0e0a0210031509090f03090b04121112060f04060c020309060301031b0305010c050a02 76
    0x1221540c01e00e08070329a00026800720396441e0303250648682081c1c07050300c901a0035800814464814440198405002840d090302c080240c68490882a0b0320085903000161060304034104502c0407c4170704800c28141886407000003900340c3ca07a0713203d10302c0c0d400c03020a00c8002035007102e090003008810809450003010034240230b44d0603a80540c00b08a54821088010041e807001044200501d05081c25100341d0b4004c0001e8802c04400001c4441000e06045d1002d0007081c20305035607000100c4040340c0e400d2044d4001d0504080e49a04050a602a1070300103500e0020000501000600c10300900c505140b49104c3c58481041d0205030800a22030201504a031440c100104401c02100401200c65081303154044106980300402e00d0015840c106c610802030814000c4804200003500d811030741e1445107210721820440b00004a4049a07030f0700034800d166400c03000400051005c42c03240d003200c0900c4416440c00190840d100e03074032607007074a14210840020580c00f291005180d0740510007505e0b40904800710 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 363215746 1250 363214496 363214513
    0xc0303070c150201060801060902121006050304030807020c0301090f0506070f0503061c050a1109130f0308041b0602030a0306080c060d0504030c1407090b061801141e0a0306050102 79
    0x1821030980700c620410420b80607a11210000c0c034000e4020320010b100d250000c000d00c0e551051900069445508030140b00b1070310400080e00d111417280f0303c105440301c0c1e41e281400c1da5500d46c2e0030b645600f400b8117440c00350320541544480c156001d0085c03d450720b21034401902709400c3d42c80c0280c5400360203081c80301449400ea1804020a0b40201501c3d88000c0407100c210100c10004214421300031000805005801009401000e021142c030061100a40595908c0b580756181000e90b481c141707440f00003c1c1a1200804540042840b90a1184e003041c02040711040d03c18038290320206e41d601d5a40108007581012a0f6850303682d0b00b52080200404a4401030300765551507070b001808520604009101040d611008582414814246c0d024000d9010404a00b000740070a0400d0f62204640300c4c1c00300f05030404000134540e040c40c10a44042603100070110415003490001074070032564407503692014aa0610204602051032101e04101400c0500801d0ba2641c805030010140d400c180c01c901e041d580300381e84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 363216996 1250 363215746 363215753
    0x1e010504020f090a0f0614011107140103051503031603110d0903080304051e0c030c0402181e040207140d110d0516020a08010b10140f070f1b03050c030307 68
    0xa040d291030b604440d2941c25540d400d840300c00400b482059051034903d00f82e40031070105211031191100207405d0700c3d141444043d0343c0c01d40790b03685220301421000c10328a80a000e00d65002e50400c6802890500740703080c1d01409070b40824555002410400c1d444500f4070079820615030050540981040c044016001a0580c0701303014001819030311006000140c00800a0240700d01444015400a0b1092600842e07844240e103171661104a400c08034441d026007001030b96180780c2482110341180d0080c0140081110100401402d00324603929445a91010100c98086a44610040c0301d1a44106070300801c840b0414a041d240080340b840820070301088000d10380a00c0c20004807c1812251850701c030769108082d24004e10524102c9038000d4100c40550004540d289043d04054050713442034802c0c2d81c4442409030f04550f44008240740b21160001003154500181e20600108030719409205d09084c040840d40c0c902c0d038100c0016910040c2881001d00900400100707000000400000b00c0c01103041045685 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 363218246 1250 363216996 363217009
    0x41209050306070f0c06200318010b150c100510090b0303070308041401090210090603050f041e030c020d0b0106120203060303090405070c20240a0507231e01050402 72
    0x82988060042e1448544104640381d040002c2004c1c07030726100342c1d043e5603034207100c5442d820617240d240c0c009040c144880711840741441503c0010500a014400382e910b2201c4075190355210b8000e807101750140f508600c2c10410240a01c80c0100c08000b8090c000340d291040d25012180030a440d00d21036001042ba400210b0392180501d6085500110540800403070340c01310302c0c01040c0503c402500003410420180110760001010411281d140d00d050055030760756800e5603440102294000d210034809425164080d502c0b609a9072817078804d060240e460412030300015609036030550308594604103240144101544280710300d01c802d0ac0040e003503055042c503000003600c0f801900901402650b0f91000074207090701c42c0c00010011604044078030480c0f105c0743c03100c110095117080780c240151520051010118803050026500c41e181511043c00e2090b502d604680726030014200359a1031248101045241070b610f4002c101204aa900519403140703c0384184440354404441c0010300d91402080001685689 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 363219496 1250 363218246 363218267
    0x1120201081e13020a050f01090b0309030c03030a06060e010f0c0209061503130b060d39060504050a090b0904151b020a020901092304020a050904120905030607 70
    0x900303110358256207126264032464a030790340d07042e0a403801c01c0500204980c010410700000e4001d40d41c80c1100c503250001d01c0a20740750100e400740040c121030420044150410007440d08184030130103032031802d207005007905d16580090710500d1040750f6078041080034035003090031008100000c5c01c1c44900c1500030407024040c14498000030f802450036034002455a92105003512201803d80321403500ea0914400501100e101c541c4215a1800da0b940460594641005d0f812040d035404640042404c04010710100c400707c41c2542d41010f22000f6402c0d00c125840c0c00980d01c090725569035070a80b1249000c0412403160340543c80300d0803880c507000c1640b03219190182c50340e0740039800107401542d01d03400803180300040c42e5150310180c991250815601e220f40d408219409143c0c02101d04000b980d80707402c40340c011100c42989400c5003041085030002c002910420181d0b0041c0003c0c610602550348001041c41520b0889084601c40040c080701144980c00c080450003507c0203400510a900d8050805019044603 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 363220746 1250 363219496 363219499
    0x405100306150c020307180506030106051507060b030a21080a020906040501052a07050117060306040b130b01030303050901240605070f020312030603060702010c020c0108040203100e060618011202 86
    0x3e038203814003552001c104201c02000310b00302c68060f4680c500f0f89440140f0301558082e11035420034100244928181d8007881c1c6d1565400c60b114541051039842e00018130201c0f40144d0180039156040003c5041058031507031100c114032001c403104206c003400a000c8440202000800c2d0320500c01c00140b6180c4400742e400350b903020309102d5a1a40c0b041c005c580c94041c40c0b42002c00f0032001210203003103e503021800700d00702c80c404c0e200e03031000f11820481c2002002003129a19050740c410000a001306020320348084d0002070517101c02d90201c01e15110040c0c0000241c00c1a00429250350078808034100c00d10540c2e0004481e01c04404680d01100b03901541d8005d41d1081404204000c1b541d0411300800e400f1156903950700400b2501c026128034072038201e07a04207d940e80d01c24001c410000310f500c0d0040c091683c81c0c01c03075035025019603402040156683c00f0007900503030f0988a4010412400680c03842041d403005c0c1024000c0070140f40c10405c00510301c2240b158009250320200c01041000d81d500d1311105038990 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 363221996 1250 363220746 363220757
    0x708060705070605071e030614010c15020703050706020a05030f0601110607080c0c1b0103140108030403080a0c0210110c04061424031617090a12091208040510030615 73
    0x380c102d0100d41e24000414800e404620703c0307005046d8107406038881d03001c4507581000e5140c4200f011006580700a80071030081c000079003a013031500520809a0080052a2017070621900b0078105440303480c00c981104000c2400310b0b2002060003403030311503451140e0344600c0c01d281406c107218240da104c0742c84420140c540710070b11285901190002c103840060310402115042210f0040404004120300c04e00901d15043c00309241444d051110b61204040d503040c1d03141000110301d0039107595683c080719440b0200b064200b040e20580c107130069030b414131070148000441d40c880b00344101c0402c9070390401c0600c04c8014462480c0640c10418280c220b41e00c5542c2240448140154145545c480c2c031846400300c107010810074000040185202a13502c07080d481c001300d9501e25001e0b00f02407a840307074611303800c1e180c0861980c0000710720b0b800185401c0300303004009158034003050380665130910b000030401070b13003021502044045030512a07824040065140c0006030b1a051110f10300d0701d200c03081404101540b00e4200030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 363223246 1250 363221996 363222001
    0x4051510080f1f060803070b0603030f03130b01080102090d060509030f0301030b010618050a0306020315030303010b12063a080f1b010509250f0b09030708060705070605 74
    0x14004251030000c24038801940c1c4418400c80340291100754901d24140c05907440d03121850400001d01c100d0b000d07112a00011032038041c05440380c3c0340c0310500a140175894481086003205401005020318001c8501700c507401c480b0405407520034000c00c2c0c143c10040e90750f0b10600010030280d0310348041d0005d80d90070080c001030a86440c00d2003030075881110b802d041c560200000020801c40d030725003464125042580d41c1048060369030602d5110300c03030b244101da130300821712001480402ea00f80d00031a040801e48005624035480d46000c80c1c00c0d504245e014083c0c1c00800f04104000b900e034020103560001e030071101da100082c1c801e80c10801503981c0c100494100210304080b04004a01d000d82c2c040242c2d003119403107071070303882c3c030748014100340d000c1d41035044003034114550000d8002050144034000d88801c4003038200006004554080c88032440e03d228600044c4c003400113260000f80348944054403041200781c0c1c0c0e6009a1041c03600d040c801d40d0050900e139010303c0811020076402000d60704901d90054001c903107074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 363224496 1250 363223246 363223261
    0x1f020c0c0909070501180b040612150e0604110f07060209010c0c0312091e0e0a3806120615090418060e0c01140a020304150e090a0203040515 62
    0x4088004190010110418000344107000120f1004581003680d0784503485c01c0c401a0b00d50120668031070700c0582074040c0700a01c011387c0111340380d007040010001d0008482040300f0b007000740500140d2005503802480d60510201d400c10b03000c0d901400321800b40c96490080e128040e1885071207a0348025040320b6011a002c10641e1081150a074540d810424032024a512801c220b0342601170460701c9400700700b003070380005594400d00805103990360b4802c2030034003054580710b001580c0000040c41e4604a0303030759100b00c2c00c0c40c00d100c45500c02e046408031480c4400c85001100c0d4a0015010030382c40f403040e00203004159440d00680e46032030740032000342c0c0c44841081c49107620101a0003000301c0b042e07100b4140110072807000c0750701c8080c2d079034180225401e2041c0051b400f40e16854803d03040c40340b0300003651880003401c01c090302c070000d001003105481164a813030358071403281400daa424404035000601c01011071540345002d00388039402c1030300590b0443c0317142803030f6803a40e69444032403003005002c5007203400141c00e4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 363225746 1250 363224496 363224503
    0x6100f0b0a0212040305010e01050f061305071107140f0301021c020d060308030915060111190c080f03031602010203060a120240090201020c010804111005040501111f020c 75
    0xf08000003840d0310340340c4a00c3d119010303102c0340705c69410541ca401c0000d1580ca141c03013452409200060452000074049d411039a001d0070008010600f030244040004034000c908210b1b00d4024020421500c0044805004000c1322140031481c6920a0303005104d030a0160000741d4601a444a034100016901c08801c0e01c3c5601800083d8009000c5940220421100c0a80403a48011a200750031303002030300d582c0302c00043d00e0002c1d10804040d03c0780d0004074a1600320104000d41003115010b03081d11400d0581e901565031424098104550b0113030004020f015000340030302e69200020281e40020b41c19440e007400410032103081c80c4034800703035404034003058819912030321034207100ca040611915280400341180300c02c04c02141c0f0650001c2d06841388030288120280d2040c2c4800301da0583c003170b1100c0ba111000444000d5005001605c060800700c840158a076104d404801c018a01c44d00d8241d10b540c42d0030009040e040903418080006c2d08407200d111943c409092600000b01100100141c603600441109840d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 363226996 1250 363225746 363225763
    0x2070f05090f0a11070804090506042708070219290f07290601110a0203060c0c07170a02101e050a030e06041a06120c04050612060a0c0206100f0b0a02 66
    0xc4c0d4640006101040c0b203c450000d20596461081c02d00154442e042071004036212000200c8032170000e4a000550034203010901e83d8054001c907401410071002c0d0f000204000b0300740050300e026088601080088039501c001c090071503074103464262108501c2442d1035480f4401d2660f4010074100015440013001210076546022907285080e00311001c3d0742220741c400c500410388446000ca05102c41894541707400298a0f85013640c058003504c2146c80d03d4945100e1900300030325010150003455408206200780408910708031980c0001030a01c1102401480198045008410704101c2c580302c1c07825094062248210503c2480d2514981c0c500420b41d0840041c13040a1a80b4598021b02003440140703e04640c80070407107030141004007800e8803460104444130039002000e24564024a1040236039141c1540250b13840b4030050240c06042455510850800e2411135581c070550ba82c3c0c54034240510390410180d81e0041d5880b6507000c406040900065181d415442030404400d40003484813541c61082c81b40c0381 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 363228246 1250 363226996 363227021
    0x409020a0e041511090f04051e0a0207150624020f0f0105040c150f050f0d0c03020c07090b1c08090306010305071a03060d0213090b1602070f05090f0a 66
    0x1e1401d007460300002220240f020320b1842400d0500c10340c01c58040c80102e5200300c6004100d01c0c02d1022030400d00014080040c0b04014560f610803000ca0518215500103100741f40e050f01c0180d4a800c0b92800090100c0701143c42122140740c1070042c04080c1041c03141c200004440d9159140c10455035100f2403038100544106017041c0034003e00010548015004030340603e104890041d503c689444010540d625188050302c0090241d00d19241c00d240503a000703007540880105154030341182d071040041580d403c2d07000500007a60005502020340424041e540240c0b040c44014458040902c00051580740182c0c0c2007a60b80794401182c404200715482251080391010f42516030300e41e900d00345592504020710940201c0d810300100d40e0840c0c0f0856080304e00c2900001c192080082d01602400b2600c241d00d420b5111041c2d035080c1e248045a80c1481c030900c07442001c03850310314204180800906041880d4014000642d400c2d6042c0030f103980e90300d001548406070340c00e81001a50781c0d52180700035112500480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 363229496 1250 363228246 363228269
    0x7050c0f0d02071701020c0d050304030e03030a0503070305150328060504030801150503010506030118021623010212040f05071d010e0c0304020d03030c020c120a111507020409020a 79
    0x48419008070700d0200301d8413500601e80c55524160303819402d0f4032800301003821a030450341100750303214080c20282da00140a858600300119201c0c010a14507448152020b020880c04000c0007116607050241952040c02111048a400309500100c2c0e41c940b5204a0680007110161031954003481c14551103061980101080c40f686c206401c015100e80420b010f0030282d8100f2000108015000d041124101c410103011f942ca140c0c070b0032459100034190100f40e40311003030702001001004606034a264109134025a8905c1205c0b2640c0e049070741c12807501516000d20390041c025880122803200d03019a10a8100030340d80403107446490315030b0030042c0f1a000320402c2c400c2603901d1a07240302205c0c2c805041e11405451300145840e1200b240b54180001c5900a40c880d19591801c00024441d400c082c06124241c0100d59044462100141c2d455210500003600e82e40105082000c0c8071410061006e19101034a15004290040b20b16049501c903a100190189484070041000c64035140c400030002c04c00036100c1e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 363230746 1250 363229496 363229513
    0x70e030a060603030809060103110f0d0503180a080109081602190801050403030b1f1d0a06020f010b0a0f0312020304030605070806010e091303030e0a08040b070c0b07020907050c0f 79
    0x1c4004007240c2c0000d40000ea581d100154241000068460503240c03c40d1901c081c14490004200d1031072940d100c40390300a5580e1900c200010020400341c00940003008400c44c502103511b0500040c0c0003154820241c9a05144102d800b08104200b1904203010082d060300c00442d560000c0b43c8901800002403601901c1c0110005280f80198881c90180e4425901484540c010300200414001d074810441c150340021084200c079940581e89680702140e5100e0070001c3da100d000300180b501042a48040056040040c0e2400101000e208050018004907405510141018060355810042c0e00008006d464280c0142c0c1015000b001902c1c029a44040248020320f450b4000500b08042a950f0360b02244400c0d4400c240740c0382554040b88280031401000003041c1c0c581e01e00700d028100d10341e60303c0c0d414011219084081031000380244090301c101107410382c5e40d0346103191500010555521140f407628041c0b1108005a584482580c2c00c4020341ca000c544807000500f41a090119846010410f441a041d2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 363231996 1250 363230746 363230753
    0xd060305060115091509170c032d0106080304051908010612060b030c01080a0b1804030801030c0b090117060303271008060303120403051903060e090a0b040605070e030a 74
    0x10785010b034644d02c10a482d03607555101c28285001c1103409011a01000d014010000000140ca0b51822803504458608540c0c4c00801e0402107600480c0f002c5400340984440344880d800102c45221285000800038035213480113046e241d0050380111803142000301300141c8224a22011132000e000410000c01039070355140d105114100b01510116145070a000d00c0303880d9403801003151104000181c5441c1c1702a5034241e401401000aa030900354042800d25207656090480880140b08030301c240c48428865045091003c141c038402e90081480c00707003c112401403644d0001303110304046000100e1140640380c00d400a415030044800d0500600001c43d00310304040c0e00441c40201404040e00e00c8c07000ea0107040001c82d90002d040702c2c0143c240e4001c011803111203507101c8240750700900a103001824281c010f002040ea403204201000c0001c2d031140e00c24082201c20204064004126030002c144000d000d83d42c2c90000f4800034000b404242da80c4000841c054002d03514100429001820b568503464540b4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 363233246 1250 363231996 363232019
    0xe04081606020d0b0a140102060c1e030108060708130f02060a030b040c0e0f03010204050f0603070504050d030e03150403020d0809120703090e0f0c1902010f0e01050601080708070906050d0603050601 87
    0x5150340d01c1a403c072000051b20000b540c90030780d00542e040e03001e080c1d26a6106000c0805521840050385400e50702071143c08a507000201440c01b80ca80c4101400c00c0b41000c420041640740058420300e18120301d111001c002446003011381e4540366054a00544468120794281d00401032180300c281c1141c01e080000006980c0f0403507488800d041201c408807a850341d80c0905080b8002e50041c40e402c9040070600c0c00350340c5884005540d0021191031301c41c1c038080e2100301040d0800328150084021810703014400c0030520342445201c1d00e500080c00628030070702d42904c009542e1a01d40000f002071019079404101400418012410380550342c0c103555030b82d40501e01d0028510307001440380c01c04008100000c611929001c40402c7e018194a8a0141c1005852001d559a403401c0c00341c4141990342e03940050716000d2003030107981c003021241400080e4914020001515818004000d0002c01146804104030b860b007180c030b003070f043d0340203272074199200c40301010305400a0540f9000603081d8481c40000113165411032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 363234496 1250 363233246 363233261
    0x60510020303100806130602090415031a0606282f01050a0e070303080709030c09050a0c0806240f07061506020f030a030c12090c0501180e04081606020d 67
    0x610f400b10704140e40d604c0c210f40303400381541d5046219010004540105080b500038100380c1b0700091000030b44600c0c584600880304c0c002d40c4100c40e40c448101c403c03a00082c050f80e00e250301140c190b0360640b03490340010055020240d00c25040f1809804070303124846c01ca120f10104604682176450b60352103001400142090364503503409902e12507083c0320000d51251541c0c052030140d50b05501c0249007560440e034050310301050041c0280c0400c07500b200000302080c034018040303001b005a00c0b00010b55040202080e02a10708020a040c02c0c080303080184006503d44e08240e4170070100c8184050041004c02c0b2181c481849020502416807802040050502c00294030044001d031810500d0107803155994400d98440101c0800c0b0b000b5a08140070400005000341c00110b400c1d04946000084080349070300480480e800d483c81590140c0f03800304180042c0d40c01041000b00340120042d1040428505219504549402040140210004240b5150154000c4c0c42140a00d0380080705544584004200c0002040074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 363235746 1250 363234496 363234511
    0xb061c2406060c021003021b0627010b010e040c0e061b0606030604080a0315150329091501110a050c101707030c0e060708070b0c090a031104060510020303 68
    0x10501c0024095001c0c05080e0802680a07224a9810081481c04d0700250040e8103000c401803820380c1a018414014004e140c0b1803070441c4030060030a425803080840d040303030341c0c81c0309030144c2c0c0740c6101e455980c1e802030701d2960406411038005c40d07a492100021654007407545039203a040000848d481c0e081130300410505038a040d002c0100c5020b83c0d6918209a5511030a0f58050305c125007c100c00400284070340c1100301611b1001d002c075146a503554141e24801d088004400c2d00107030341c0d00c603440102c82d03041c59140c0c003001880b00684a44281480003440092001d040e2904803254035607500c10f1303a400307210702c0941c3e80c44850580d400d4440c2e070b040c10b545893307051031414400d901c600c01d020740081c05510030750106a01c0c6840c1c000e40d0b07a10b2050580040042003101400e010307060f501a2626907842009210380c605c48c4c1c00d140d0315800c4a10300282030b94009810364444180502c84140e40d0f403039018521007101d0708482c40c0c1d0280081c15021500405c0203400c4035411114800d000340c66190004000c40c001c624 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 363236996 1250 363235746 363235751
    0xb0403031d01091d0601020a020d0302150105060903070e06030a23010e06040309140307030c1508010515031f05040204090c0e090601140a090b2805070b061c24 70
    0x1c0301401100c0383c5006001c0d98000c100010080200c20707805640c4903a2000045c01100c54981290700040d40c10410410103d00603403003000c5143e50300c1030041241e03004007002c0d03804500340b0840c02c00003910740c0707075500500d641d10701618000344459404218800c4000e81044003150010501c0c407624951444c0010590b02940c2802944148680c0c002140d03407049805a4031000306506000c00000d100e0310554681c1d07814820000c0200109036035640d1200104050070000344002c00301b8802400c1c05005034006071040d2055501c20b01c036240d904085a5100a01e0050b01d42c1c0144550010016401d03142c1000350060320109010030325840d25480314100c000540c441c1d0103111300620810901318402c5a034180082d8000806103441449000a888020300e5810310640744c0e034590264403229001414440f665654041e141c0039a14495529844038901514006251000d41c1d00c80c051140b1000d0012809110008408101404501da0a032165079204900d080a106026002a14007104d94a0703050300d140f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 363238246 1250 363236996 363237047
    0x12090f0c1a0f07060f1a03010c05040503070e07122d02070221100912110a0812060d1a04031202040503070b0306030a0b0405070303021b010509040f060b040303 70
    0x18110a0415044078084082c0b80c003182003106002900440d00c2202e04507115800104540c525010703d0000c40340b816143d1081901e035004042c00d40b0040d0412506005007004148000c0d1000306000c4160b1324140e03070422050301c81003001c565004440042c0c0c0451803802c0080410f14051090050182a080040c00c01c40c41408a80008910403400000c1d070100c000c0140840c0c4d8603800d00b034a10f204503403109075000440f0310000f00c400c0d0f4031034101c00ca40300c3c142c004ea604040d0790000e81444080c6440c04c01818084034aaa0f15420b512540480042e0f8001000004420396603400010b80071660101d4450030540300a2151801c00c4000d980c101c1c0414510410a010b0684504c2602c0496000074003d2880e14941114091035910260400d82c05000d100500fa01003600004650302551141c402020aa032440c100242444513607810006d2890400d100203403581c3e80001038800c22003044800040044108074100005c20003a405001c92040204000040c5a00021840301c6040079046680502 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 363239496 1250 363238246 363238259
    0x904022203050a0b0c0a0e100306050d05031e0306010503070e1906030219141215120307120c17030901090b07090302030f15010b1e04090b1311030a0c12090f0c 70
    0x14016186c0340c43c0046c90a0314908414a01a40c941100f01401e00f0001b03a40e0792548003042d0042e40c100341c01d031100e600c0080d1360980d0306410030045c0e0384054485481d9086080c00c60001704584000741150080058072081742e040d0395103e40000c000d581c10740c14140b0070240e41d403801170045d402c00007601c0140d43d052110480c081e40207040782d4100803a1b40040700e1812079068489042c124024040d100315044c8488407a07400d41b500d0011814800c00040296104c001d545042d00784050701509900402c034418030054000f9204106800203000342003030643d00c0c0e40d9100318090052800440c080c02c44a0755a0901144581148400054a0081c1c00381d8407006035001c0c80340da480000d820052200e0030711070010804220000007605c401c000000c1d00400d640710032a070b03645a6401c15040202015581c41c00380c440c41c50645810303c0800b40210040c00070b06901c40410805000060203542c40d40d80b00c01404887c03d1080710041965170303500030304001c80109410400304030380c18910200c0780c46503004004a1b10307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 363240746 1250 363239496 363239521
    0x308060102010c02150106050a0219060506210a110f040f05010521061519030809040f0c0e012f0f1204181a040207061a150904022203050a0b 62
    0x464040e043c88840d1b03441c0401c11205a44410f0301e600860041250150b1209072048007140410b004040105090522000300312540541c0d0003a96800c06190030024204400410703040b0391180c002110812407611800421403030142208256881407518141007804510303588002d041c0e50017a5540090303076003c412007152100700401a208a51301240001e401c504c614400070f100181c010300152800b0001c001403140c0a4000d4004840d810400318044400c2e060600c600109810b181c003062040b1158460701501c030540d40c42007141000900c130004000f9038550f004032402c85003100c1c1816070810400751000e4030b58030040c076440740c0350003002c151603004552201a0b03402d0350180e603c900c80401c8030055210081904084522540c2c030f01d0300905503580c0c1d60f880648107403401040003003084640c0b81140100b04031305600c040c0c0f043c948010b8040d54159078409907010804180c40041c3e135105401a082107088107440e08018004c01580c0c04001c0002c00f0030300215251240c090101243c6950f003141c3c44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 363241996 1250 363240746 363240763
    0x602071a010801111305041d0a060c080a09020f2e080f07020d17090a14010504060b0301061520010e0f0d0903031e180807032006070807060b0d0308060102010c02 71
    0x504175201a000d00c024680b95006c945d003000750181c101105500200140d0919000900079210319a0b00c44240340681e4000340c0041c0d00012a00f001c000c14030141e400a07034060b00c555441030007600b240c40c2c01d00503180850492882144120380c0f030309150a46000c01041e0110443e8426080d40142d0040781e006800090103004440141c2c848503a400808070340d850310000001d0000c100c902c94000d004003c41e001c41c07151441c3c5101180040b44c94075290a02009030762410641e203010344e2414204006008010a00e83ca01c04044e141c00140703448114074410500c507071104010180d505e44449071402c0d41000880825049260091701c80030119264140c61020141c0300142c0404c8148a59072101d11049034030b204e0700030150800140f80800f0700300e8900380401d0341d002030800390310030602402030110013442427218487e6402107048032600c5e480405c1c91400f42210041c2070150204503003003044195080111a01006884018001464280102a010207840050165103840c0600561a01c080354aa1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 363243246 1250 363241996 363242017
    0x31a06030c0603090a0204020a1713030807030b0621070908030c0a02060706240602120414040e031903020301092901052a0f0c101b0602071a01080111 66
    0x5106a03070010301405500061580c982400384515000050780c86102903c00e0340450780d03a0946001d0028811305d410000a000602c000039420303401d5002907803011409612098510300881c20300901d0000c10110701601c40c0180d8002d0f190040c03444040100c0b8140c511403041c0c1c2e0f6466081c29515800a61644500d8a051000d0342002020002508101d4000e22049106040010b40e440c403454a41b2120240981200031032180b105081041c3c81c2e0403c15004080f00c11055a0300e85441c007108042000c0403900054091900c036001e9400110007031050302c00786403c81c280803080b01e900800041c02503209005030003089180c90360805031244407584001c0a094080500c1e071016194400549039900b02d509020513108400c480c103410310b2445455591a5203c5000408038038840c1d48040b42130191904083e400f896042512100c0c030303a445140c401d0303860b00004240c0101c1c8000d0038060003a100f607180141c004203a010707000c50503540c0030041354102c40710f60300200440c3c0f00c08c0014010380e01c522001b10 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 363244496 1250 363243246 363243253
    0x12130503040303210203090c03101514061308011b0c0206090f0609120303040b0f0405070303050309070902031801051b18030708190b07170f070c020415031a0603 71
    0x24000039008144444882501c4020055132161450f441816a441120b0403c3d854012410500090400700401700d10030000d45401e009404800d4a40c0c0c505020520440c1000b032100030890071305803501011510040c280300d00d15059107485070740040c0030742480320781082c1946241c2e07802c0d0a01c0d44600c01142c100c03540285054901622031042000410700d910b95075a000f4000c0203098401c0e038440b0b9207010b1861010700034644070320341030400002101000305070320402c1090b402004001040443c0c403200741e075490b0400c1380e1a6141c48070024500072254010507003451001003401400c0350349060740071181030503400078040c0756119402d01180f4205c0d034646c1c2c601a90180518140c0007591007150300034803000750032140000e0760341c4001c61428010f0b40313031301e2200003a450700e45080c461410720407907028140e41071050300307890041c403d10000303100141150756443d00000815040c40c40317840c1c401d00762a00240b0501400705000c5850281c032503030b40b004075902d81c41102c2c03008480720708010aa12426001300036 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 363245746 1250 363244496 363244499
    0x403090e0702010219080403030e0f010f0e030f120a090606060503012402030a0c030e0315010e1503100b010c0f05070f050f15031306061508070206102106111213050304 74
    0x58039266005441123040c5a180c020403111000c4c00c1044044030300000001194048855000c8421170301060030214030b80d00b0400125401440300402c5400030381c843c9191540c40d942d1100c981000b0682583c2c0200154104000058204e6000010718146c41030604101040500d520b0104071a0000128074005a042030003001c0340c8031301405000300118064105840c07240002c0000a04120030718000c40c507507a80d403500500c0f45140348803089a100ca041140889440f013520002030751422030060140b902034a480908126034407480100c451a51f000c07841c506074200d985081511030242c0e01511140f482d401c0d400080740e2811244031840110050b1072400705002c02000440654170042004140003945018400003a03c64071a2710011700c42040d244c4070701c1d0641c040082000e100540710400310b43c400307000e100310070303440360b000307000300c481d0703500d0b21103181d01408441d12003203a4428000d85820b15006040112a2000004007142d200300e5205004a40c1c0d2802d6100c003090603400d014203554800d000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 363246996 1250 363245746 363245797
    0x703080a140f06040e010e100e03030403021002070f02060711011d061902120c01020d06050a14042d051005010203030f160905120c090f0114040b040209090403090e07020102 76
    0x450b5600700e900078001107240c0311059a0070742940c02003a04400325a200424943e142c00d000d108a07582100b10802840c91400c003901c0081d52500c10302034440b0074035400a1f0600400140c00303811852150701401d0251036070710608150080c800714600007400302d07005050030a003803421b805008114a6005047d5070a060042e920031924241a0f41480154450742039803204104115003d484408200c81c009651090281242400d44000e540040c1c0640d0b00c84005201140c5240c840c1c0c091498141c60001c0d82d07a01207544002c400c88032200980c11004141d100c03c14003600c940111348103048200c040004540e448004903a2480201d0704426a80c2900c004a2425401030110241c3d845072450240d01d101e46030380008400d40c000d070b00681841c1e80421082d4a00c1e0504040aa034404802452441c140d0f14103150340c01c0078140d000d09144074580d50310702d0003229030300c0c2e50540b810400d01510121044c80d0505c0c0c064254031a90103290110400c0c1c03000100000d105008803009042140304440e090510541c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 363248246 1250 363246996 363247021
    0x11030f090f120f130e04121e030f060f0605040e180604120903050316050d110c060a0c061a090f13060b01020f06070509012703030e21030703080a14 65
    0xc10f800328040204225040103000b080144043d2140242c00503070350605103000d038101e03a2065888000c2c409208104a407038006107040c845030b885c40b81404900301031220b03008801049030303810008040c0030150300851855401005081942c5140c160b04031203403107045140c5400c051116205010b584110000b0300081c0162460707282d005003601b01300000c0381c3c90350760300c50842e00300621021550b07030041400028003070300f003101401c0c00001d42405480c1380040d6071815116012220441d00a00d4001203818950340f0500e4440045c0e608007804210f455513403a04001c01142d40c1d0348191045034501d001c1108031030720040c100c1c06420b5401010f40d503c400ca40c0c0f03000c090000d894485066000d58000b4408215045c00840d104195a6503990342d61104940090041c140d251200c0d120786000c9820079148070021450001983c0e0541446420f891144002901090040b244003a00401c0502d42685840b000000b520b82503101380c580b11110380d40c446482e41120500c1c011280c0c00d03041003002c82c882c0b4000d817 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 363249496 1250 363248246 363248257
    0x309010c020d0803090c041d120a090b13030209070815102606120705010c080c03040803040308030105010e010512180115030c0e06030619020c07030611030f090f12 72
    0x181900798000d506840d1442d00e1342044441c0341c00342c0c024410200c1180742c18031a10301039440002c500302c1100b980c07081143c1d4982c42d1000ea5000c0d0300e00003032484d0501c1c0c000c4081e0ba00602d070040140f9500c800d140f07402d0301402ca40703200c100d0080f401c1c4000311b4002070081995a210f1300640b0b025540030301d00c0004201c4030120044021060040000c020441030132a00b03041001740d541d0003511211803c5c03210a024441813001d40d0b2a6090700a4501840140c2c0e00c81840c44856070820703030481d00d44030314040347c1d0704511550340724042600c00000c00008004482001d14120351003601c43e000d0424000b4015075440c0300300040101d4a41d0b4000002c0c6032858062280d510b40e281007400024003240718108245a06a95001500c466808000401a840c892001281d110000350003500302800d000201c10342c0403110420780064990045038801c118001013000d02c3c005c60700880c081c448040410598145a07100b034074442102034a030342c00185030000000b5161140e07080c2e48028451540595014042034206 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 363250746 1250 363249496 363249499
    0x90f0e0c1918030b040b100506270934050a110705040e03070605130506040b040525050f0a0b0915070b01060f020d08010e16120e01020a02010b010905030309010c02 72
    0x1c40002902c40124801641c8102c1c220121030905050441d043c0000514080c12102c14040038003041d152a41a210800040d01c1264400d804804c001c40c10b0801c0d40024942043d030700e400700030b68005c0e050031070080201c800c0d050304040b0300c4056a10207201c10865543c030100f41c1c10411558043e21a0f020500d031601c4000039102c844c0d0300c030000074058030640308908003550f1020600704113000440c419150000010302c80310b503440909681e81c41d220100208043d00c0003003030000080902409003c0d401000c0c0d8200240c0384070300e04803031406e80318212602509000302042c1d103510302c4a00b040c048075425280a085001c0c00e0050000411208000e1112000c1691307509000c228006020058040c0c0a0081f94a44c0070035030510340f030003e24082d00300030700100700b0648a00400c002070b18000483d0700080d0020030340d1505e618511055460141c000c01e40c4110500c0d10326201c800c424103601404115075a507009000c0c034440480115210000341c001c00303625401c100f01500701503008403001c012183c070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 363251996 1250 363250746 363250757
    0x11d070815040e0c1801031a040302071a190f0801090209040209041a0102061b0a1b051b12120d0509120a0203130b18010309031e090f0e0c19 62
    0x20790303001090a480c03155840d14001ea028105046075031034100080c5580f082480700039050356145894150654024150544d110031600000c141858800d20030755000e00104410001500c404500c00455507120740401c1050100c408568203146120700300c2442c020039141e40320102c030713401e00000800940c40100f04c0c60740603600b000303d0b940d2a2540c5c000c40c964034000c0300c49035060104850003e810700800400d00c0c020142c12109481d0441015030507079914200a00c1c1c60010100102014080c01000354005003c512540008002d40c0ea00c00359101e00c2400140c4e110b032000e86440c00c046945da0b03074601241e060340009000c42403200da103541c080c2e58003003050b89c1110070014601c899031400d41c2c801000e04006800001c2e44400d06810866140003c04071800e080703190022448030039210010381c24065042589034078220051620500d99000c2c9005040c0a10458582081d00a04044003c2c45124280031000b5000240b100c440f889080c4598541c0011a2070a442c070f5040c0d07807000000400d07082c140070303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 363253246 1250 363251996 363252031
    0x1109060d140c031501090c08061807050409050c090111060601091406091008090f0307020a12030306091a0f2407260d0b0a0f0b0702120d0e09011d0708 66
    0x7030701040f41d048006072201113903081d035041c00508426510710740500e00c02d024440c0103002c01600c5e2558001c03a190740c849a4408a41c0f90000c00f11181c0c0300f00d91220400506180612103a0a03c450042c22501400d0b01d8548450860030f9105031503000450720a808651409030401c116054181c4032005100000d08003490003c4141c0010300307410922510340001000b040400c03080c80c6042200c40c07020304a400c025401c01c1050380c00612820702600610000003401010702d010180640c200401a058900c3d0902412208604104442404c81c82d420320420041d0004c6249042040100c5c86040c1201c2101d000c24049601030072066101520840381c0c3c000101c680b4480b1050180045c03040440031800580da1100400e50304103459081070702500c10072a10104106450700c080c24401110f140380c190940315a65400016141c000c0361181c03844900400d02e03640b015560242030344c0e100400c1110701d56103a91702c4110361b403164446001d204508200d004081001c26002c1c0010a03030100c5071188503400403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 363254496 1250 363253246 363253249
    0x1501090312020d0912171c0e1f090803010e06060c06010905040c0504021c0c020304050405041101080903070812040f050109120327140f03040609031109060d140c 71
    0x2440c460142100582100300c0c2c01c1c3c581c50344005104010007a040744001c0314035103138560341206d4200d1020b8041c0c80d400040d050185201190464010202c10103040021f132503100c144503150b458000010a1200fa0023440042401071880360fa01840d030001d8805d802c51f0300305181809803400c06010640e1040c420311401c03034010030400002e800780000d03000c08a030f581010315045040048980100c0d1086e401408480612f41c1c181000346620350300300c41d001c00d01301003010301a820340c45250045504142442e082005000201c000341d6010700f02030703851000c15034900c580251240502c80005014440412294080920446921350002d000b0900240072800c640c0c0d03110300715842410112400002450180d6000350940b00320b0118038a06801c1c21099001460100c04550f06040018030117030302e0729540f4038040c1040103107a02002103041101d640303544514020300203050f1407000711041100300c450013804c0d0900c02402800340902a100041c1c0204540e9191113207940e4034100000303482181c0e004900ca = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 363255746 1250 363254496 363254513
    0x150309080409020703021c0f18181b020d090603150509010608150f0a0506130f060507060606020106050a14030a050d03020a0e040b061b0102120414150f15010903 71
    0x2e1207607880040e654100752902030f00780224110004030307448030030608148441d0803580349110500545004420342c0012071503d458082103411025100c00e6075140030803000a2680010103260b01207981104026070b0b001c00300e0b66480f104103507800003025034108200c894069048078440e05688082c0e03100701619900450a110000d80c007050011306074406001c54401c90041075100140b05580001c0ca00700e103040800e16034441c40c400e140c01814001403210101e903859680c80c01034a0110f0401c2945691400024031a4200000590b59545004000110180144186000c40d9070280680001c03500d0b00c101e00407004c585001054260181e145100001001484001c40c07031081c68800588442094000030b01407964000c4880c0580c0c60301034625101d9651105548810600c0005808001c86d5104402c0c0a400740c0d4001000d8100040c0520080061080c044080080b05504895a00e821a002c40c144c1e200250b81e5214140005004101551518001186030b035106050031a20155241d5503500c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 363256996 1250 363255746 363255749
    0x102070326120f060d021f142208061b0d09020405040615090b0303040e0601090e090d032307050d02040f03060204142d0a15080106081008071503090804 67
    0x30700101082049415010520216045001983c0c410417500701c0c1d9020a450700c461200103210703e110000c0f08aa200c0c40390381c0181030b240c25055000e0b01d5401c5418462039040a0404001c00310280c3e070008038202c500004c8180c803821301050000c116400c080c407821400d6200185500400b6140c441d4500903840b14001c4500461080b440000d981e106025070715072540450308950345003420802d0045865600100343e5050743c2400322100c0040c4c44180041e20004215800491041c180e58104111340c01c2c0810003800d000c0c0c82d078400f88411494800009001248445103404450020b401f044421b407250000d001020078210005240c16280c2508000100c05540304544c140d40000c2e0601105150038400500701c0c409503181072110000100c03003a1861121207a141d814010075051140980e5908142c03c014094810545034014000000038900360f07090280002040d400404214881a1201084101caa43c0d80191808609080c0680c20002c0c00034840002c158841d00740d840441d411800410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 363258246 1250 363256996 363257017
    0x1401050904050624091e0703090302030301050618090106020c1309230f1506030114010b0301030f06020f040306050421091a09060415090501020316060905010e0f012004050102070326 80
    0x1d40380d09011070183d0401100900007030230541008140ea0021350000150ba043d204100c0c0d0706601d480d80c010201c3d400c0320740c6d00e2056030300142d40400000d140da00031400c611251710035150f81c1844038103480000d003611080d00d401050816031440c02200f6021450740d85070369403485420365055143c5845034514182030354a00721048041c6000f80079a03480d00340b048010b9403900740d0038031501c1c0d03140c00d214038220f000520000c0c0203450307518016020031000394100c942a03440d200010340c8481d101e00340a0010002210b007129444e01803e0300740c0000240b490030802c2c0b00241d95071103280b00d00309440c0c091560310707282a66a8214050007502016503c850180000e00700c101c0da020404582c5a000800c0d401150740981e040d90010090b95090720300c40300c0d034002d8064001c5404995111149000e03401414402000d08150107203100750b00354844190020180b804c0c00e100300480c00b003406801040715200b41c0c45000e000d0b03400300d1010000502c0140c085688801150039000d55136055154041181c5c3c04648040c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 363259496 1250 363258246 363258271
    0x409210224010608071b02090f010e0f15040914010612020102150f04030e010203190306090b030106050603040f05070b0304051e1b01030b040f02040801140105090405062409 76
    0x1c05a03141d20309080040300514050806075140281c05000030700083c0c515410003e550340074540b0502c5c60402090241e5010307100c2820b500c0d00c0c1d0120941600207000381e9900700391410200760342c5441c50184c3d601885503001e031104014010002c01c0004d04452008469100007500000e080340c00030301c5540005d004008440c06045c1c444e200080c00c2511130340b030314928007210300c05009404640703640065020703a041c10200090440400140c4c614026540684404800541d90107103695041c0c120104440c0100c2d010320000785104101401e884031030152580000050000901080c41d00c130b0403210581c010303c19104400d40b04c40300c2d00d00f180d0003280c064415500c04008421181c900c08409009114000d01805400c00c02003001d518107501451018105502c5440005881e034075039000d500e60300302c400700c11035036a40d591180034080e158404c087e5060f0388400c0000202414070341d1820744601ea000c0003802c00c903590101020300030405841084211001d490b8105d100e921403101090040d02800c854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 363260746 1250 363259496 363259513
    0x20a02012c060d1a06030906042418120302090306150d020d08030601081506070609050319030e010f0b0105220b07060b04060b0a02030a03020906070f2004150504092102 74
    0x210000001d44e05040707030250782c04004104591700e001c10182d411035440f040c0e5101a4a0380030310442c0000344241c80c10344062604048103120142142d148a10724402c01144214400140e02981240035040100d60980c00a8001401c04084d254401c0c0c4d094100801c040c1d240364003078010400c0a405000104c0f8180344c008140401c40d80c211003202d41c804c0920081103001d0042ca0003294042c05240c2005001648441c00b12040005c2070060311040e41403007028020059204900a01520551038064029403920449000001c0300740201c4550320010b84520b07107010b040044400c040a071100b0400641d10054101291814503100184285401602c004c1043c020340c000b00421501e030782d0301403440b0395400c03c04a440300381c0210544400020300d040050301d82c00c240d00820003910440100620748422201841c0411159028022001c0141c0c0244011308100100344411501302040071041001d45500c10030162409030008280d05211740d551b5114215480d00c81d0303100300580411800541c018041c1d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 363261996 1250 363260746 363260771
    0xe0303040e01032a050d060b0301091202070927080f0403060906020309010c09150507031b05030715050c040909020103090b0a06052e110f06090304090606020a02012c060d 75
    0x2400b600c20207805468004c0610b040c000600030801684010400d907220030f03500100782e6003903001c8045682c0052036040c00b001c045800035280c0ea12070107014074403460040d250a0a5100c00318541d0100304c40341404440d11b02d607072241c040030303040181c03c166071345420480840090154010441c22520030500961a411b20003219401d4455112010307003004003071034080049900355000d10108801c6030608a9403107189040407036911183d0580e608044c2d50760340d02c0000300600000144407841c059020040c1085185651600703a803c2500c5187e0021130501082c0120060303907210900d005d205040006036000c0d1952800c811800444103855180e81c1e52908010794140200c0138400fa2010041150410810600310900715484440e180104400c1450048030b585042000c01c00440d5a201114203d00e800f520440d569449401440b00d210b08101c000584140001400b400c01d0f0741c161a2850207082c94a00e071a00f400c80c00d10031210000c1e211034804916102c0360005c01c04034182c0030000c2061400c046 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 363263246 1250 363261996 363262043
    0x60c1f021908190e071715100f0312051902150c09090a09030201020c10020306010311030c0d0c020304090c08150109050319061116031202040f05010e0303040e0103 72
    0x20700304244009001009010b00c0c042d001c1103042e400c5200000b900302254024580b81070b5081d00505900041204080840000000c95802c00c4004414400165694555040700b5810502c0356554620003030200340005240d90400100c0040c05180c05424549400320303800b5001040c2c0791050258201c040c80c100191140ea84560b80b121803209102e10342140c4002040000d0001000504100d035104051402c042c400c0d0100d030f80c4a2115000c4580c8114003100c00d5000358010707100280481d1410100c0140c5460701c0003500d02c10b006011016041c141c4400d0a90098042c2818400840c0401c000224040031203100c0c4c0801c82045039580d4400e458048280e11001d402c0200041c18850500001c22060b50b00140170a0444090740702c0f00c0b000d842502d4010301400d1050700410a8540c0801c4080f0030600c503190b14034840d0b01950b91407407483c1c0c50710b840500f00e1146028030080907030550780a001c1c030350080d0003d4001c494054205c1c1d180c01d135905106d0850f00405e0704111600311401d2640b5000e283d525 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 363264496 1250 363263246 363263287
    0x122402092205180a14030915030a0b030109020f010507140d200105040f0f060603020423150a091517010b010206251d03070e1b090906060c1f02 63
    0xb80d40f03d001031810300021590740078601c42c0200b07034480d4240000320519050064558100f00070382000805004803c0403041c07a001201c042600c0c502d4100003440d5483d050044240598011708072a070040920300c01121240c0c042d820540322001c4005801c07001c0d00301002024150310f8580d035281002c0804201d0b1041d4540c0404030b80c0b10740c0c0e05040c18071001c503140007422016260322020002e54001c00d440c222020380b9080e840a5031041c944502e4000580200c00c44420030350340052010050743d10781444001e031401d1004959040300a5640a0000340e00c076920400071303116640118428240d40e6203601403410121900181240d440742a008000d503010409181c01c05940228902c0003148104840344410a00da688410008103100b030b40d050310846100c0c50380c099406025904001d448100d6151040130070713151000b2844c0310a0300081000b01c58801e8440c010b500510440558581c07508005a03030704a01c4640940340100400c4000320038580c0200e610300200b080000d62248501099000c11034100e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 363265746 1250 363264496 363264511
    0x90d0b04030e2707030509100204120b0106020607210e06090106050301062c060a1e0608010902120621030a020c180f16140a0216122402092205 63
    0x40c009422101c3c02000420703620241501e0002a90350b11f17141d4491500301181180102a4400030740030031001200804a002240a40000fa00380d0b661001e04a950380c00c201c50103400514807080c031b4203000103000480300d01c14004010200b1000c1c46140e81070705028043d20342c1040d60399540f00410460600b80182c2c001001241c07415103aa04a03c14100500c002c15031080b0114098007001072200c2da0b65a00081c080c04e901da601015070800c1303900c4100c548911b801907102050811000060b58040d40c001c460f0f240ba034030244000f0300c1c0c550340f003400b030240d45e0050002400703c86d0360315803450601e04002a004000007039004080014520040c098200c501031602154000380000b0402e00c0f139031203042150005072080b05021038015004003201c030a07000c85442c0d48000c00000c3e840780250ba000812070082050092031200c3c480e0b4490314140e801e880c1080040041d01811194078440a2901c000b100340000640302515048420f400501c0c1e4400000c45504407400c0820b503000e00f04000d105855000c0703803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 363266996 1250 363265746 363265789
    0x131d040302030d0c02120a170603120703031104050603040c1d13140c030105070e01021c0e010804031e03050103150e0c0f01050706180215040b07030302090d0b04030e 73
    0xa054500035103e01c90041a40503807a15464000c80b002c0c820042013044a00d400c404507100c041204005003600c008074968991961280c0100b080d600c0c021036000f075402c0110304081d00e0030748503640942c0074044074000f4507070041d000e07c000243d41d15568011441244510b4051029608124045900030b651140880c4412a240c04010141c45500350355080c46030040002284a0654602c051415442c2d40001b038240d421706042c40141030304004402040d0300d09800f40e82241450388650824480605015400a01c0130344080a540d4011110550014003902e040140b5a11029104035254000981480040da55100400c2401014203050040aa08810500030360300111003440d580c40c02c004e61144540001c801d4690640c0c0140202d83d89164020800d001c410000340490940c002e583d90113030f004600800c004032034060b20704211416940c1014059041520710b490842c000c0d0401507034140c11a403068640c1d80821100d20889200341d01c6076680072104403100c42801800a458084009001c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 363268246 1250 363266996 363267001
    0xc14010b09010b07081908070e091915080102121603150b0c01150f080d0207060f030504030c0203010e0d090504230603070510020a020907080112030309050102040b131d 74
    0x1612208a02d04444905180c603480f01c1103404c007100703544208560f400303401c45102c180b605d00b580c101000074484e80158580000300c2010b0014000016411200462900070883c80050121410340c84004d20000f032110b0110040d03103400d0300a003240d01490011410704160b81c100042a0002400b1600b200c2d407901e8240303c9481b0301042c80400d451140590480c006011940c292401400d6000c910001e02e0f07032030500841550390301803601690f401e00410540e4014030134125520341c000076000040314620799401800301c504850807401808042c0c012420450070f88403610140e034090044880d009806005000c0c000a03004000c1c0400c50503500480c041d41c1000d1071840c0c103403c04028001d545664080f07500555a640700001d003043e2846c0c1203250b100c0c001d8035620b0081580003c0d2041c0703440c4240c854118540f030350202510384120910a030203040e0b04460703103d030000744690030040440e0711502c0007508094a40c3c40f900c3c2d0b11380200c144440c904000700c4003041005c40d081d1450010803445c103002c01190 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 363269496 1250 363268246 363268249
    0x91906200406050924070c03120201140117120703080f060406050102070b09060417030c0c010e091306110d0f06170a021c020619030b0a050102060a150b0a0c14010b 72
    0x40c000e024603c0e10031604500115805c0301d413225484034819050308100e43d184814503010301c4030241400161a484400040980384500501ca00d100d48403409003080c1ca16032805401302d581103c6240e4954050140d201c0a2000409442c060311409210f40c40c0c0c1201842e091046000202005007d10b100b00e0801108100340d07600400c15109843c928007909070f682110901280d0507101e1a80100c0050381d80c00929201c5103004000341040b006504103550025501100448280b0b021030803d030390000065010900b065a41e028100e03020f807003448045150440b480700781d0b940350028003440c845952280c2d640d120303c103454801c20028004022070410f0a40200001650390b410361b4000a0082c50148010044151948040c0c0c101940c020125503035100c007a50300312100000182000301183c100320b00c01d0341a00d031131140b08068a030180d00818860303076201c5052028040b60020402813418030701020440341103e4004080782813081d103e01100314000d00d4420841c40e80c2d0740ca41c821903494555120707440d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 363270746 1250 363269496 363269507
    0x103051b040b0f19081905090303070503070e030114060a090603050c0f03030d0f1a030d021b120609030408060f071d040204050d0f2612091906200406 66
    0x241c420180c4015101c019495110f54a4400c40100201d821600d4418440144d41710f0324031407007104042405400c1800e2404801d0541c1c409459850060b001840003a0302d9601c5040910f502250a181015102104102003070031a0070764125010403110304410000316081002c40e2100509001004100310b9146441d0140c441079018012403280e00440c0c16070103141d0302042501ca5440350904104051040000803400a061814020418281240130900c0c3c516000c00e054640300659005006185000840f031116050345050a56008078480c210070301261003040b0803407240006c034008650b0b5a090080d4289000d5006001c0d006288141081004040d4400340c1954a0a04942c864100c8010340000401a004903000280c0107130180407160b050240b810301c0081214011005141c4070380c6040545107401251084080002d00200540450038541030030065024052070700b65851800c0000d440440e005242c0400e40e01261036800394201202c2e54540405804404081c40b49071501c0c02070003402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 363271996 1250 363270746 363270749
    0x112140a0917090d0f0201110607020601081009081608040b040e0f101d060301020714010504060c0e0109050d0501020c0312070e0307261c03020d0501091103190b03030304030e0103051b04 82
    0x1e500c102c1716442d4110790240d0300c5011512500d401740c4400d4174110b84001d50754102403240614070b1141c0c0490320342a000714440c03102d5058100405500d8946180c41c00418803900d0141200c0d00c05082000103500c100c80f03005080a8520201c800095050017a188103c4403c0500105140c995005003000086020fa078142004210030006e0a440d940e6440001e00900441c2c0010300841080c4d4445907400b071041d446079218900c164010040c1c150140b100721506990000c2c400c0c04200d0191040c0201c4c0341c070700e8501c1082442000090320304544040c80e00d09642002644a40c0a11001c007030051050700400c400180004c10b4000704a4103240c42e01c44e8204403883c0c1070206100440007000714941405000c5440208520460380344c2d1a900c0c0341d4014000e61040701c2145047c1d2510740003040d0100d45000d403000102c0d0f09683d080c20b649440707484100102c07000000d40701e1b43d5a0707140d82000131345080c030285204a000e41c41d0312003000d465100160688100030850711040408890b4540c00a403440c00b03890 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 363273246 1250 363271996 363272003
    0x60f02030c030f0915070f271406040b0a051e090919020c0a050c03070608100303030b1309030806040605060309060703020a09030206040b0a1b03020304050112140a0917090d 76
    0x1c01c50b01c4d40700f101e50500c8411224a0940c03400c0d94200f0080310380002e80307070740983d0240c4d0b0b5101d41b032000d4040c0284080701a8840040055412108204038042c0410b0302c0700c1090024941c0d407030150f84100c0d960031640400d40b14004108045a00c18140c4009640f0031202c80e0306030000c7c0d2030310800d50001100c0c441c1c010b140e1480c0101034080f44510144950682d0125103006040f180d01140ca0704240307507600daa621030184240f080f10300c0452060301c11000300c0e004403003038031202e64464199a000d03009811020b4519800803c0c0d800782030039070b004500070201c0590003502d80d40b00e00d0030000140020382d0581d8001d5030040b0020014418100000207400d584981140340040c0c03220400007044070889020ba00182d84110086804143c3c141200001c004801c2140c81d0701ea480c070b00885010640f00789007080030b00543c2050204200c2c0354003030401d00c4c00c5200e03444800540d00081c6c0050080e0340ca01502c8140e01d195540f5800d004110281050728280341019a131981001c00400c00a0440e07403410724000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 363274496 1250 363273246 363273271
    0x50118060c03030f0c020a050c121203040f12030603060c08090312220812060102070501051b010f09050d0e19140609030607020a05010501050a050a0b0315030d030207060f02030c03 79
    0x40c03051603c00c3d03102070103030110001c05001100f02d002d070095541c00034141c180d80c18000e105a054544c940103100910109882000e003140c7c500420f0280e080707401c010002e51b0a4249007220038001000c130b0406585402041c0c4000503400e0440c2000030403030790300c00e0300182406101c1041c009540f800000350742c10408920f886045d2660b0f0b1008200c07070140755820350100501d059103500b007044090000340000400b0003034600ca543c2d44081c012650740c7c0c0c9501c91603001c10070030003140224100182c0c1c1861018400b41c004178802054010000c00c458020b07c0603a041d07001010300005103540700315140452201118a003242c002c6600c1c8100710041c103449030812944200d500c0c051152110001d4521541000741554041d00d48940040d4850001070b03070884141d46810004251454002e0400d0281c5501030240030a1504085d00500300e5400548202494555101d05090940e000c105404c41c00381596009600c42d0a5403a0007020303035915039205030f00a8014010440c0403800340c000c0da9800460b40510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 363275746 1250 363274496 363274517
    0x1b03100e06040609061805060a030209010e0709030b0c03090f060105060d09060b0a1707080d0c020906040b0909070f080307110d031713110607030207030b2205010f050105011806 78
    0x42c2c01000240c1c85a98854104100050800310300c50004250041c00f000600150f41c1324030401c11007070214080254012411070041c4113004402c094070764032a0807424a00d0000ea226240d1454540d000c9070190007e410000800000407c20700180381c3c10071500b00240110350510340002c110303005165104504030391351000b00c814008150041814108050911004c054803241110507000b40398420311594451100009034822001a009140310340c960b8581d1514000351b400c00400c10000303400c240d4403544601406c00700396500c162541c02403e1450080c5511450903041c41703d03a5500e81c0c4500301e1038009014102c00701d1050703101000340303134003c80b1410303c103550030310301a2a104240e407446489a400b03d03041215004d81719a1600d04a4012006822151310a0081100502c24024018016005440700b000010000d88501d504507803015016aa40d200c41c0907502401c05041034241c801c4e84d1110603441c0100031502c11030380540801e10300010f010111501c040c40da442c0c240319507020024200c01c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 363276996 1250 363275746 363275749
    0x5040618030c03050d0f1e0c0207080307060b0a03050f0105090c0409030c08030c0f0a030204031e030c06113f04051e160b030a0507050c07031719081b03100e06 70
    0x5d090511b00c00c280c03c0101041400c044102c000d400c48007401c0451030156034010281c00010480b00b2546c417500154501141646c2d00009480b074500d1300ea410400250f00440010400e00005040140b1100002400d1030810101440d000c00340d01d03c41e004620303062440f07000c04e50020344100b82542010804d42d890b05d0b41c20f0308070000d00c148182c040c020113010170302c007800e0340e855001401264040c400c10780b4180000e042014407002c0e400b0300100800c0d031000c1c60382d0000300107802403501a1001c002640c20140c0244d006003000071800381e900000902d1216815402a500011082c86520004101e11070300d015501d00d581c0d15019411501c01132462041002501c904021002c0b1120a800640f10348a03910f81b007211244d0030030b0719601e1405044c600080e0103035214a0990b40102d84540061008603e90307180c2c0d4603640000d0105000107c01000560722034544c44e54582c200080e160345040081c94403da040007100103880c1b660a4800c801c0060041c410800c9901206030380c4000b2500000341c88800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 363278246 1250 363276996 363277001
    0xa030b06090d121713140109050303010b13170325050703120f0e06090111030f070804030302190503270405010602060a0b01051908130501020c0105040618030c03050d 73
    0x101c00710390000a5644010030010703404243d4402421a841e543e0301c40b01d20000d40e05a10504540000420b8169041d00c1c0210782003907020071601d4031240c00054040d503541c645900307540c000d80164450300c80000d15a012580c140348014010302d0705007024a0501400001d03207440e445201034103091f82051841148181b6401800d00d82200da020003110b030100d030b60389014154114440000c00202d01006443e010035130081c03036800d407544d4005050600c1c1c50380301001500d0a07144102905440d10041c400c05103000020b5006100c03040c0550f96903074445145140003803070625000b40b07540c0802546084c10b00003c100100703991101c13050024010384148140c4000100c0400c1c400390581c854100800000c0103030300401d030a401403c03880c0f028413404016000540d1184100001c1c9042c905040d80c0c0300c50141c1c401c143e02a002450080710b070880080d142c50740390982c0c014101c20002e696449041c40100146403148c544013001c1813251030b00342545a00c001c0c0c450f05c034582d0082c060050018180031940502d0317 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 363279496 1250 363278246 363278257
    0x405061c030e100305040201080601051c0207051507020d050414040b0301090309050406150228080403080a080609090604030c060b06040e010e060109080303010b090102070b030c0706140c0a030b06 86
    0x114441035014030242402841000c5610300c8a000301034210f80070007103901c85d0040c64885c9030103031a94000c0c0c0d00c858004540913030280422f8000c0118403007960107101d015000500f043c500560081404154280440c8a80302c0081c00903000e40d44103018100d00d1a4110080d10b0031240320b070301752060341d421100200d00645a24150386606518250300d140805400c16055002e4460907501000b050341c6811600700724031203c02d1701c14013603407100c5207d240f4159950341c0070b00c0602c4100143c09030200c199644005a0f00250411a04080049a611034569006007015031041c0d040324119920305020b03601648400300940701a0400680c84846410700807035410140b01801c025102c581e50303c4c1d8400d16403071202400e0069138a4003c1d0a0080354040d0f00c07074400141034410036000f56180d81d1030004050002c3d403101c9000e5046d8003c400001a6003000600958480d41944001c1603680e4001d00c5c14104648111840d00440c815420034000c0c07014205013a525840c1e214140060030041c40400508107004a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 363280746 1250 363279496 363279529
    0x1080718110706051b09011202160507120b070801030804060c020102073512030612070b18130e06070f03020408010e070303120b012f010608010e0c0a03020906040506 73
    0x14440b410400c03e81d0116200b01e0b8018014409000c0741004c100d020f100310890580025a018441c510b50049503005041da00c17030701c1c070681000411a0383ea403410540796610102d95007011050380c606100c5410300c03803507100705035242c081142c3d8107540d11a40a030085004800802c40c1c10148501164001c100102c0688a007030340c5000d590250852031020401c0e02c41d801139010a0410058070401e9000442c144407009943c0c0c42811995800e0510605da010349004a0f034070310520100140003903181d030080030130340b03042014141600d0b100c0c400d0021650501a024216620b0590700d5525030130082007503034000c003480c50b03c0c2c55491406402200a405141c0200c0350551801c1e22240700204d00203807100840388a62103a88102c101810030350200c82141d48040d01003000d80d4440401820324109004030395007400b1000d003460050b443c0c81403c540146c0c02c4a15035070b540d00007801813400100401302c901c00013110080411030841e80468164031014100a01440c1c9441c0400c200d550b4101041054196 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 363281996 1250 363280746 363280781
    0x1409090108071a0301031505071214070314040b01150c1e030215130308061c060e1c051b150a020301180207050c10030204080708030714030301080718 66
    0x7110454192144050312032041801c0003002c5665045041005482c103c940091010f002d07901c0b41c085450141c20010601010408500040807145c025480b401c840c000d8210310300b0906141c110340c01360407649c03c00c4021072901b070040c00f04800140d10280d80781c15928044c1550701a06040c0c0c40907035044030302c02c80052022a01d1801400810342507100000464020b42c21180c01c00c1403203021805c200c005403041a5801090b81449003c01e015180c0c464000c04094a04424900c40000007400090110012100d00703444030812000550b0030000484407452502480750300303002068005e00503204805008610342a461100c40f0949001d001c0d120745a54086820142c3d407400290160095109002c0d841d9003052014002442c84511704c25074801903807100c011b00c00300300b2074420042d208001c0d040c801d08141e000c00021450308030912501000b441200300651300c6003020300c1c10000800c0f0412400c21240d01c103000410800c200002d1100c00c4a5a00305d07054010340020b0321034000703820b01c528400944032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 363283246 1250 363281996 363281999
    0x1060803160b06063a1d06160903110f04050f100609030c21210e0402180108090109050d0e040b0906210a020a0b0703230a14090901 58
    0x20034a1407040c0d4503204031820340305a42ca0104006103070050b0075a140810700714852401c2d046203265088103c40545a00f5251840c0c0d00041d00d00c15120026503107808010190300107040c0c0d8004000385900105103400300384c0f40e00072240c0002d01c0344160340302c00b030040c0510f00014000f5403201070a8094005024200f409185402500c4111108044d41c0300e4030320844010000030540e12074070342d000c00d03030340d01c0842c1c607180c03a2420400045c03169840e4190082501280440000510424843d000c440c10110885440b4a10040040c1600700f00006042c003035030040010389400b11900031402c140b0320003402c2c0f0040300e891b480742007401031030b0203d4001c205125030f00c284091990056a4261313140011503052016280306428001621410345500790014155418602010443c540388401c1384421012552004c045400240200700c2d0365000c0110072000017419014542e01c8030700c40e1441070184020b020b5030030f0142e10f00c2c1c5c00c92140100c0003080091108501c094003005104546910000500e160441e5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 363284496 1250 363283246 363283267
    0x3010c030608060708010e0f0601052703070b07120f110f1e01020705070614070b040b0f0c0f03070509060706050415050106030c1e05160b041b1202040e01060803 71
    0x200303128007601d54244a000e0001c1e5004d032254110505940d000c00c055540ca0b11400607002c810040500524103009042c40b144400d070084a40f400c100040d07000d602d60914a800c418141400d2840c0c00009814104104900105140c40344080b03482c5060b2400f92142c0210100032501540c1074010320f8154000c1a040c000d81c5080000d000d484100070a00b0f80e440d9200a50105080707114608009086403c0340c1410841d03180207030f83c3c0000b00a021804545440400d03501d6215103402240c08032061103030340042c0541c0310801d4410f181c0c0680c0700c1d14010702c0c25141300c9440c42c450200034020010000300054940941e150b14081c0c8809591010083c8442d041614100c1402c3d07501e03442010003503240000004034103109006a031214100d41d103031081c00a00c480c0c0a6510700541c196814184041000b00c0d0a00500c0d03130090184e003e00030f034011060750a103454035005a04034111801c101440c48401130010281d0040b04c1f200300c0307504aa0008141e84900605805450207500c04001d5020200b60340c04003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 363285746 1250 363284496 363284501
    0x4080a02041a030a1b0503030d05180c0d062703020105150a050a06050c0106082e0209060301120f080a020a02030601090c0804021203280e04060317090f03010c03 71
    0x1694421581800301005003160403028a000d1200e05074154803902080b0081051007031a41403251142440542582d112400301c0c0c5580d01882481d1011039407003082294403003245085840b07414240e0080c0c2421648440050701140e030030000989a2076503048001c2c41c0d0300404440d162040412428030352198840c0c02d01031300a04044070300c524100c00340041d90b401c501c0c0c41e0010300b0650724000c0142003010f041c04404c5859130000030642d1000c0d0b50300d407008100420100034040b0002d828481449501ba603180000300000d02e92018115131034018041c8a0007a6126020759040d2040d0080c00c0e00d402c2081d0420341c0096007841005840e413800000d01028055011403559600d5000b41c0403500242d0b03072403403050110b50b602201400000c415002180045c03401291a200848009084900300710040400e2180b525800b4042550940c3d1456981d03002e9030030450746004c81604031403c010903495910341c08400340d00700604200803100041e007411310780d0780c008012001d40300c080d001300007107160030307078003400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 363286996 1250 363285746 363285763
    0xa061a01020606010306240e04020d05060a1707050607081215011b0c031b41010816050d02030a0e01060503060912070f081c0b060408031c020702060408 67
    0x500502c0000b41481d4001c2c01001c0403180c48160b04d01182d150706401145001ca00741120042103028000d500403a5200d00103002c00351840380740094075060030300821213510131541c800151903541c80c24402c003110b0041075020480c2c60580e4410b9554600e0b15109001c0e2090482100005048606101e16003920081102c4070502c00c3c1c0715950b50000300543e006d1070646089000f010403d00410500015141c5108441e1800070a4000701e0030070b848504d02c0c40a00036001441c03404a82c010518809200401d012008000c1002001542d031149400001c004a200400e05c03000a0450754000b1951441803084a83d80c141d45007085469051000c004000743c03202c102000c12943c245800400d19107004518140101526402001505420220b0650300d4006d40d50646040a90102c010301107075200d0014504910507410290032001d4808030281150704584646000b164244402d0203403080010441d06400800d02c410500b02c044100f0200c0039115000000750480340120b40000d40480004002d030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 363288246 1250 363286996 363286999
    0x30509130b030118080f1e0304050a03031d06040f24050a0e0133170105071808030d2c0d0201050c09090f10030b07090609050a08031b0a061a 62
    0x442c0300c02114001051054803130b005003e91104004180080d4070754401081f4290764100300644145252065403099002203a06a0302034102d14059001c050f81072080070044201d0030000d048200c0c030000390694681008000404074a00308045000340080039561408042c60444410f071117482600c2c40c4406820240d0305141020b082c04d0700c8540484041c024541e8042d0006400700c00c03240000c03850140103004051200303900c00e0146003c00c1070392181c6c0884d561101d0203000800d450510380e000418420400b11036500c141644042840450804070450b281010720010204280d240780800e8a03034882100609618804c103044a41c8041c00c000c2002e2540000300c0e0000c120700d41d0b444901450504c80c8a02c65648250032000041c01c070791041000340d40058450390504010341e00d82c0d440c45c240a2007642c980307000c641c0c510b40c00c1008541c401c1000c00039110a4441c4012240b4140311a030ba00c6c080c80e90900400c44005030007000b08101004408001504800140181c03501070041b054030001c4040c00b03a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 363289496 1250 363288246 363288251
    0x20c0f060609070e090c04050a0f0519050a05060703020715090303140412032a030e040b010914060702031f0c120209030d030c031410290d0504030509130b0301 70
    0x55440c0b400300310307451140c6025103071091401c10312410000c05000003040001308180510010603180c444400c483d02400d0340c96002c880281c20a01000590145c0c44150074601c00c01c810f00388070944072010010200c500c1641c401b03417120301901e020b90400708079807c40c1d10403520132580852065030000d4004101c9000747c8401010403096401c4002510850041e4040e14594643c60300c0080c0c0314115044d0441e2040410900c003249843c002c0140c200c0b044d0040e0f000800c66081d0209610701071040c0d00e44a182400e000e100780313240a102c038284a0400c0c0350103220b2600810440300303540b02400f608500c844c104c008150640010380b0401d009000f84001e542c0081d00030510310f00040124400c072010010300800500b5120030403441100600030000c100c100305a1280a42c602220620b92514000d03414020303142019418003d408580c000c901c1809241d00340c00329910821000c0020031500150f00c080000b1032265103030b00781500c151241da0324840e001a01d0f80c02045907125160700400c600743c401c4009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 363290746 1250 363289496 363289501
    0x200d0b090307060c050c0a02100504350a0b01030212160608040506010501110312100f06031d07030804030f030314040f0c050910180b060403050a06112802010b0301020c0f06 76
    0x121017a0041001c210401e9000b418203002515007402c103510140c5091a00c20b14080e05c0d900c00012040d0300001c96810700b10145a600641000900fa0511b8007000e2401426202c1c66612070341c00c206c80611000c0c0c001c0e07100140904e070805080c00691501080071448010050b03550384000c01d0341074200c174107a90f0380c000ca034004111588100d41e89034000c24440e00450400c1c001a00030840c2030b00261018410312019040010340b2451013442c0001080305841c005049103d200b000303100301c180d51f4410a101e41151a050000440201c00d0303409490304031800c02000003c41ca425001000584440810150003e04000400140401922805100b850246174240d6184141304802d0b0701510049200603c0c14418004400c15400d0090b240415010208035020b42c3c40c00308000380e01c0354000790b0f8103800c4100705070240702490003a040f0421103954520b1410142a600802904507602c1800d003146500c8410340e4094801d40001d01c182c88014021581d031010041899643c1074080420300d40c601030b8000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 363291996 1250 363290746 363290771
    0x2090907091809030906030b010c06180c09050606071223091905010f0e040b10080403090e0606040509041118010f090218010e060c06010305010b0108060d200d0b09030706 75
    0x20003400a600d1740740c0c4c0025904100742500600070b861029810090b095803c1d802181041c0103400c0104003505205e030002800342080c107011030b400e422000c1418200f100f4000d0b1501d8800840c0d0000350000040c803c088090782089507020101005501000f02036902480401c45410041180c10002c4a240f04000184800400121514401d580c007041c1500441540e1a014a13640c0d00d02000041c030002c4c0c80090440082d0f45036140b2070441c0001290304040108040c1c02c00f04a80140101068030550f1b0300d4001c0010750f1a04c210301030240103880e01004a000c000e150324404083d202c001380054100d9004000c00300003600300744283e03000032007102c00004d2401f400d8422908020307500940d00e840720b00500019120701003407201c0985c22100070800c001d203410040c000e0364080d5104c2da0000c00d842038000e0004040c0c88010700040c0c8280d000f04190f0340040c4c0d0501d4404508407040600041d4540e0500008202c4601c100020f0040b40c001020401e00070008001800c24a01c140c504001340e03544d400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 363293246 1250 363291996 363292001
    0x31205070e041d0706030f060b030c03040203070614030a150905150f010903080904020c070305030a090e100e0414030d02161b051302071b0303021605090907090f020909070918 77
    0x45030000c3c581c00c02c0b00140702d0580b10741c00100030b25110a81c04900d4994441619806500840b8154603520001c07081c0401c41ca802d01204008088a14003100b024550300d001c00c007603200c05420498140d07070380c2000900d80d12200d41a20010711041c2005c00480c0703855801000d025079403164251180000e00140c000b1503000c0c0c4040f40540e601b0440c02420810351005100082d400031032100c000d84205500000010300070001419000260340e83d040d40145040469480000e01615030314400004050502000c11071000c2030f40e0290708583c1081c02101d440c0341c0503045100f14a02c00004a0002600304240801c1140c0c1000b114440c42c0800308260840c0d4902e00f000005014107035114400300c41414507440c513031b00a003800300e000300d43c10030209843c0720401e503001a00c2ea1046016801c945984001341d2040454100200700c1590000214541a218541c641c140d40c080c190310f107951901110602c50301ca5064404010018000c46070600740b488016207000b0701c910681c80d948a03100c17448200c1d940d032030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 363294496 1250 363293246 363293291
    0xf0c0a0f050c1206130204181707050c031f0c031103180606090106090b030403021002072111070915080a21020309030307081c092a03050c0d031205070e04 68
    0x11170100c880b00f41945c20003016001d81362204001220400105000c149100e80301c0c801e80d05801c0b042d80d078032003491500a0074400c0400c4494800d402200405108003d10282000100c104500000c1c2c4c4000840003a40240cd000020b0006d80101104201003441c6140e40c0b420110a20002c40d64265140020003410000034010000010417080c02041211130610140d43c0280c0f0a005540169a00710002d200726003019106440f8404d441b03d4650140e40c03629000b102235140c80c90030034042440d441105540f120725110f040f2500b43e95002c00f001c101e800100c040d001e0151081039501030002c3e130030141c070326a8000440304a40001038080400803800001103840014015010318182546034446840300c0e0884001082016101d0080030100081485060394252040c1d20700007015000c40c030b56280b02c03c500031240666544900050010a20008502d40c030580c085620390040d0225240443c0e61039913150390904ca4905200500880d181c000c24200e40306901650100030004403030b0135000d442001c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 363295746 1250 363294496 363294511
    0xd0e0601080a08071a1501080105010c210903020414040507121a070e030a03080906060a03050a060207021c110f0402030408121513050a0b04110f0c0a0f050c1206 71
    0x4651000009907444004d015101e00440b000060008491844080c0e04801c031918211601c0e1034200034019a0800d050b140908401e180c240341909042d99080702084038500d1129488091625401005103e903070054090341d4007400a1050302d0800d03e1000300e40e032060310126400e0180c20030200d0700389003a041c00c4160360f4101400303000d42d9406039000840c5c01030103881c5c0c204104032825141711030740341040420146442079644954528052101a08115000c1c00591060005880030004660300194441c1d1154001c03034016034075071051002074030607031355086202d41501d80b0300541014071a1740156044040300581d506c1c1c1c1b440c0152000c020480c442120700800d08d403810b01c9090a847c2e092901d95074000c080ca40300c0c012740003c02c00068142e03010444181c01e500e403684104900318440d03001740d291441007078805110a40800d00303c010305010303c40b07003080c0100000c900160362030020800c0d0040c40307400420301143c450560600b1030326035590400440c042c641c03041040c0221900090240d100300c05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 363296996 1250 363295746 363295753
    0x103050702150403090e040b040302010b0a0b1b070909050304080105010602010203160e1302041e140319080f030f09010b0d0c05010c0201030e0316030210021908190e01020d0e060108 80
    0x80c42410440340400142061382002a002c2021400c03c10017500d1901030380c050510701f20700c1d290600d402802e6901c0384c48218059550000304004a040f418150342c181c0501d0410080300703c0107030012a18001041d8020441c807402c01000c1c0003070003004402801034032186002402640c1e294001039090b4481a5800080103aa80007042398aa105010300710f080400144500841030048596a0030380c1c000b6044410b8468a01c0500390b11811078030760f882e0040004003000301e414503130240000d841e400300554010844000d01600010014080c003164502d0341403800c050313142c1c00c0002100c640c1520480707a41542d58038040c603e180364031f021501c0d0301d102039008225054090804004690004550000700c0c145030710b4210915403103505101900018080349a01c0c1490b900d103040091a107014403074084480fa10402423240507885440e51340030350702e0041c01c244a07240c9801c543d50809050040320030034800d10700040c20813041010740040140d854540f6060020a10040450307495440030b00c0780d864543e1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 363298246 1250 363296996 363297013
    0x60c020102071d0f07020a020d151808040611100f0912180b090103020f041d0709030b010b0708040803030a06030605061005040513022701030c0302030610110f030f0c06060103050702 80
    0x11821040b145d801545407050b292850700660108151a002c0d0204a81e03440344160481503242c0c440c45801000700d51301814030100101c644400c82a0b22640c000c52007002441c00d0000390b24041040108400c1404070790810002c100d1200e100e005082c0610203c6000c0246190649964030030140d10603917841c68448029407501d0000344401a6005c075000a041c140c003803115022000c0c0301d101510003005d9283d100c0e48005200d0f02200c6d90400b000b003291052080c1d0540a00200e0302c0251150f055510f84046030741c1c0c960503801c10444d640500c0e804190103100000030025400300c0c5422960840b44518024000d6807155000c00151200207160640050070030300081080c0e1138040c10581d003800d10340400514040b80f501d440000b0707400f100030100141c0507017280142030b540c0c98494400c0210f02e5150441c298201040014140c281d0301601108204aa00900181c640c0c1031060740c02140007101242e58554808541100e20740040c203a0300b41d58050440010041e5000c3d01031544541d00c140e01904045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 363299496 1250 363298246 363298261
    0x16121a06030709091a011a0406030c05070210030b13180303090f060513050c0607200102010f0f0f060e0f0601110309031203060306090127050115060c020102071d 71
    0x480104656410310032040001007001036485001d0005020389080c2070a070094005101c1e40940c1a400610400843c0503459040c00102d0261800c0d9052464080303400d070014801101c0c6c600540b0b0002c2d6100c031020318074101d2650103511211004100781c4201c20510000c00481c0e04540180d480b55540080401001c4000b80c0301e50310610351144500c0310754154480030741b0703860212441250101501090007011005000081111b066421401c6401602d484101c1da584441000c80600c0300e42130b25400000040c0030fa0003904149001c80880000300050252500210050800801c0032214246000b0380440c1007204090124800e4425604240084d21110300448481c546000c2c0b0300310b140010311105005030340600c114152940702c00011920303428404109070402c48050000c1e150b5a1501e001d183d07910400d100100311144810303d1f20100c440083c01c00f0340c0500550240c1e080018881c0070045012600700781a00f401c0348c000c0c0d08951426480300c0b41c182410030034030b124204c100e0102d400207490 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 363300746 1250 363299496 363299543
    0xf0108060709054002130e06131802090412090609030b28090305040321140904020d050103050616140301090209010504181b030603030c06050604060e091612 69
    0x102c1440311844410f940744050200005040320140381e642d00014410100e00046c0700d6180504200549440340d818803100003582e4600002c100e0b04541d45030030740c1145940078802032501554020742002024a4289040510384d0086002031020440241c40410b440748110359003015240e1001760000180c031403040590005058900320200035440600840841030700c0e000e807441c880c1c0b29450b65a10b45046190201e034000c14000d50703424043c0321031340c0f006140e07a20030030901840c1c150350101c682c0c801c1c001c0e000c14081e20451400c08551401c080000041080010b00c040c401d20500c442c002c14540c4101302145c44650200b5a2191050300740b006000001c2d10758010410350070141811841c280e5a07090140310780e901c07060313101d0f040340e0780d55450f17181c0e084c42890048640300300303180410040e819994041c0007201e40300c00207040143d44a0004046840302d50084001e44001c0e0a24160781c41c002c2003036660341004014261541c9200c12001a06032550b9048152841e80070b500d044182d03011007158090b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 363301996 1250 363300746 363300799
    0x1204020d0507031b09050106030c0c02041104080106030309090e0307020a1707031a0a0b0111120d060801020304050a0c0e0c090d0c051003060503070b12190905060f010806070905 78
    0x400b801441400030004000d003801d001d0b150440c01d0084242860041c2507400c0381c205030b000200707241c10061004e0009501003105110103a04039000598624582c3d1440e1030b84c080c941000042e58680000442807541010380700d42110710a5009012021440b078030070751a405035003402908001c81410511428541c0324050311802d04040840c0c510031f9880d01c070034420400b584868114201d180061150a2521b40550f8000144c00e080000c04c0440802105954117180c0c8910074002e50042203450000c41550400001015103200a5440f42040c3c2846a00c4402201007114052400d00000070b044020104013880340781e5010641c0c0c2804071410034030205034a0401c1c2141d00301d030500d4022903140d80340440646100e4460f580011030701e0502c2c09151801c50641c201121001d070500400f1502c80145400c50b0b44100300022545080700ba00904401802c0180c2c2d0003842c5004080c01c004400100349411812288841d00302d035a691180802a01e20f5801409902c0d080350003400441210795220204a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 363303246 1250 363301996 363302003
    0x1602030d0507031a0d050706030f06080703030521070519020a0c0e010f0905090a021002030708030106030515010507020f01030c0e0310140906091009060b040e211204020d 75
    0xa180008449080d000c4a4044541101080e5145180400388041040c641c4040105440701144004180c03a80c90f65601c0c18491034041540300c80d10343c244044c0f135802c0203000b0044801100d030070b41c1e01ca00c1d001d03140d0b030081803d12590202000c0000c0d507c9910010380ca008583c0390f1a06480e00309900100811030110303188041c150300c15103160074000b1311221501e10040031b5844a0702e0007941400c80c0e0500c202e907940d01800606050a0500031074400c00b08040c02516412101d007000018400410ba003140513201000d4482c510110000076100c0e016003000d44076207160030a8075085421200196100c1c062024044c3d00302c808441a0421540a51700400720000b49050400790410741100281c076001500c2480e542c09a11030358144500c004a0380082c1d04100e4000140c80503241c4400c2440d81d80a000c260300140c192a03000c0c20051207916030014201d80c40c040c00a1240b00c481010303160b910300303805201c4110341230038505100500d01c44000382c038001c035542c0e403900800e92150340030442d0f035094588096 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 363304496 1250 363303246 363303253
    0x703080c161a0f07033b03030702030705100911041d07031506060305040b0708041b0305150f070509060c0106090203040f110f01080a1503150f20031602 67
    0x20400300e40e01e0301e410404200c0714462408989000f201c04080800003800c01d400381402c1120b0105214040a40f0010242007078000300038603078401d20214650300041e024980716010000a201c4a10b07404070041003d240100c0469062404040240c030844200c0d0101618074254116000349a01d050b030020b414540d50b0440601941102803200c508054441c3d00072203240d400080d094900154502407040200410309040006103071540b168642203000034031503002c01c44c4150003c1d081003406501400ca240140441400d03071a01c0e403070055619059060100c50300300000340000c040d60b1859031940d20038126640c030b0700e00740044103040c02100c2d00440c0038650035540368200418844500e00c00b56100350701520003030b5003584013410241150101080301c0c5000780c0300005082143d9030050200c036005482a2000281100508240180040f00b500002c1c445520b25030401285051174100380702400501104001c104005042000c04040ca06036040c1807280600004505060b0101030307001180d05070065 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 363305746 1250 363304496 363304537
    0x40c090515040507030606030509160b0a021014011d01082802090705031b18010c020d0210050c16030f02010806061201030c060f0f17070c150506030606060703080c 72
    0xb4281d41044405200007075076400200281c56150140640003503090015003003140070425a00d0707843d0014011405000f00000304400028402c011403021001c0c01c50302009402ca035080042c0c80244203125100d0502d045280e1295402c40c01003d150490740c10320010000400c81c0308501c170031000c02850380d84000c0e000c1c40c02c800140c0c4a2107221481981940d43c0c0565905e400403801203141070a003140114083c1c1440302e880000310f40c1e020a07a07900024203101b0032032182c520000b000c0440da15402900b00350080a1000c40f607030040045c0c0701904200d000d13100070815241c4140503420282c880500f00c01078180c0040d006d5401008800d4010314041e00842c07401060301040c43d10100207074001c407400c403000c08080205652084c8080c010302c003145050742c9204203900b0700600c1c14441110f1550301c480304001240603180035410040e00183d01820b0368022600502000c001400101c4005010780514030014446203014011928070a9140e2200a90354a03440e0f9842126080b0144c480c00da0001000c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 363306996 1250 363305746 363305749
    0x5070906260921030108031c0f0903030b040507020a050606041104170a0c05010e090412050c0d02060405010e060f0a0203070e13021e2104050312040f110108040c090515 74
    0x3255205004a0b0000c0120b00006503c0d001420030010103491001c10520061008080200440b299040800c4403803107440c0e00e00c43c541e402400d1b0301e1000c40003545003041030420590160403105e44005c1c101d400304141d544120040e0b07181c4200040c01010381d0481d42c0010114a400e50282c003180a810150b42e080a817075041505100c1031415160304148d010700d050000300030712045036102404007031805140c0031140f000031980c0d403107000c0c000405681200c030440c000d0601c03400c155520410300c40304580c858941a08080d45500d021703202030b241542810ba410298640c0002d0aa00800420003404503e944014065000790400341c034a00800c400100050700301d50300e000b002d80303200030304840050380c50781a8904450030b850100124007448609218000203012030250700904000000cfd4140c0b0035039a80d142803030451081038940301480304602d0a100c248000440090f0710380d4440d000780c0c440080100d005541c01c0008540c01040400c01140c14419008260001900242040c00c0c90514868560 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 363308246 1250 363306996 363307067
    0x7060f0c051e0a05060a1505130f020417060c09060702060a0908031b06090d02120702012c13140105040c021e060a0b01050f22170705090a05070906 65
    0x4510706900d40c03100c0f602009028003031082c20340140c02203c0c1041030010203d52010301080030300c80d0b00c0c401d00c101c1912015204c61034100094208040d0f0045688945034125190004d901c0c0c06558a00c0c400c1340002141010200103e405107900246568203021150342005100d80c40940020f00304800b03200d000075898000c0002e050502c401130b07401c18207214248400d619001008003c6420380d4020805039146580215000544240503c0c03010354940144c001640c50110710305440c80701c0050740841e0074413441d042007110401c480841d0302401c1c2c0322403409082c050720200341c0c080c0040c4030450010131080c40c0c01d42c003091031a9164019103445c0403261813000d00000c41c502080c40f00c1e40001b010054285a144030310950300c1000d08169092183d483c9501d070719401003c400140914052481440383d2134000b00d40c4000348001c0b50240c5401e010030201d1615280d0070300ca014010b000b48404500c01d034006000c0c0c14170070001c03656103441851905008070f40084449540170324001c01070003005c04031100710 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 363309352 1106 363308246 363308293
    0x6010806042403080a14041a0306040e0f0604020102120403030818160b0a1205010b0304150b180f181203061302030115080907060f0c05 60
    0x416040203510b40704040c006040340b01c4800010040d01c03000402c00184075a030b0748a001180842ca000e1140500d004c0d149460a01e42c3c144901c0301c9081c006503600c9240104081040fa160740d40307072400c0c1500c07291242c80c036030412010401503580412041034001604d140329031515141d038400500034034000d01440c11540008205507840a030400441c0c002c0980b1030380c4000034941d2150001025403241840001082010030a4130700325a0510641d4106c950841c411482e607900c59460b5070a070346004c45000141541c40e0174204840d121600109402183c1254403c601d0900008400603c0390003800c1400728810b00c9012003107440003145e8400002220000b294890326054005520590010404105140301100010701000c1001079254040c1d556280d075030082d00d42c08952902ca1031b07140103400c080380030174840c038500c203100b04681c40040e4020000d9540150742e000d212100c10395038 = true := by decide +kernel

theorem cover : BRFrame.Cov 363129496 363309352 := by
  have h0 := BRFrame.cov_init 363129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 363129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 363129496 ≤ n) (h2 : n < 363309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
