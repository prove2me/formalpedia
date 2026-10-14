-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2905
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:06:01.269832+00:00
-- url     : https://prove2.me/submissions/8ef0f083-08e5-4b88-a52d-8716e98af74e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 522302158 ≤ n < 522482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 522303408 1250 522302158 522302171
    0x90b070e040c030b01050406050f04030c030c140a030809131d0102071b030f08031302060f0702010e04290f03030d0605090703020408060f061f1d010801030b180a060e01 74
    0x90400c2d00a6641c41c00d22071904108500d50240061300034002c900649040100c0451160700b011008401c0700c0c05190401500d9140380d5980c9000146580e00740038a5001610011421b2101d080501e882c4040e2940012050b05101031902400b6801910b100d00ba5280398072482e1510311184c0c0c0040340700c18030810700e001590b02d007928103001d107000340c020303203421420a001a030400106440c0440690300c160300c89985952a2188a80101c48a0581030069403089000500340000e0833450020700d2503d1003078807098000a03600c41003000b240d0004031104c005250405000c0111201d40c0340c890000c107001003c0107808209503020a03d1500101c82c9031900300d60320501809546400400070358000c0140c5420752400e800e0107a2561500c801402041c00c00d40c0740c0000c500b0b10740c0c540310b150800d0169807220b40c0300000d0b10f0710010400c17040c58803402c0201000890311805d07544280c0c102810780c0e8000c0d407040b00d0f070f0300d44051400c20744071101082c2c01c032802540101e800007400707070040d0a00f9212071800492030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 522304658 1250 522303408 522303437
    0x70912021f0e1905032e05010602240f0f19050c071b08030406180305031210120c1a12091f09050c01030c0e060703021e0609031606090b07 61
    0x8043d00c00704900e80785408400400c80740e54001485074640c00700b543d440354008080ea00d40210f07801340030040080700d810000041802903000034100c0b8109940b0110318083c0c6844031090254a0303003a2641842c40074080002007200d00a20b51154100401c4003141c0624040100410100d80040d600380d0b10000c40060180c0a00103141042c07542c4403204a01503404d140f406510070381c6da00c02c0e44900300601c003a02c400403441041d1f100030403004582040503a5038070f00195a44c2680150202c41d40c00f903008401c00007003464154100d03201c0d4100d90100c10b95000908100349501c075142031181c9055010810415205031054801015015550b07c0c0001c2c142035885003000040a44a01c041c5401586400c8140000c9240011180078400c5c00382000190000080401c44159281c0f808076604100c000500d4400c1650016a6843c0d41102c0581040d0240600c609540c95a8080d101e00348194418801a001c4501000c00089200e218000000301c00c0c00e2690340d480f48800c111078007408907441666480c0c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 522305908 1250 522304658 522304669
    0x90c080c09131b05060c010e07091811060d09140609060601091226090306010f06021f060905010b030f130b16170108010504020a0905070912021f0e 65
    0x3000400300d54003501807908003640390000715000c0703003e000c01030004486000c8500411002020b0079028011079621075524898130302030200c000241500348034203c0001002c915611074181c608217011283e20002c1032549607189043d00200300c85520020401c81900c20481621940c500700d480703269551740341c1c0c581c03141c0340307081401c028001d41c0329400c60b2007004130581c2c0c0700540400b526100011044484c0e040d00382042d0502010400515030381a05d0f03c1401d0041914000d4400c0400c100d040f20000d0fa20307408000b1600905101b6071026a0020035140300b0811641146c00c194081140c002a0703080d41d0301c101c1d2080e11002c3c0e20410800d00300205000c490264280d4035984180d1000b070381010460b0a9940702040c500007040c03600902010030001081d688250448440c2d0802000b140e0754a58480340868020700090700c0892103001c15210029080c0280c2c02400e11581c11134445803030301441c091030a414049095000c03079010031400f001502c2c200c1d00000d40c07044541542c2d503c0f002031541c3c005200 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 522307158 1250 522305908 522305923
    0x6030a0c0206090115180b18100803121b0d09200103020306031c020f0a06050925330207030209010f030f0f02030c030708030909160c02040b03070504090c08 69
    0xb032040c0d06041050185c20000c4580008407080c00c0d0301520b0500c0b801ca502401460f00d8052194000800c05c16540000d10030b175152402160340c0d40c012030741c40e81ea402102c1c1d620301c0380c01c1e00c0e410440b50120000f00f170f460001003403260402c0c2001010f40303014011819201213817107c0c07034200c561030120303515106050130400000b041540701782811440d50a0000000b6607d4101c00e54048030311400030129000507100b80029a03090000d83d084503120109490410043d000031100c0e06024400c000310700c0000710358680510b50000150401e071581c0c1d801c00b080078004a40d00e020106480d540740340300700c5102c50720a240781848142580580311aa007507104020700030006a01c03d211210990700140003241003134480c028803542c07005250504400c40d20110703003850000c8100c40e034075005040001800541c04401080b10840031240e2090542d909920b040e1000007081092000651503450000141031540c040156268000c1c1201d050030743d101d00207029100145c5013218128912801080301c2d007020440708 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 522308408 1250 522307158 522307171
    0x806060313121d1507020405040215070b011d0c120709051e0f03010b03030d05130b0c030106080702060103120c02041b09060e030d022104051507051905070501120b06030a0c0206 78
    0x100011110002410258010400c02071f108582d101c01013011565000f0282c00008004040b441c0c54003101d04200e80004001d1040502d001c915a400324a0b51200c00c000758480c4081c088010701b01980031030401d403400d0f8024500824010500c40216155980703080c1c1c041d06903040c100d1030072052040d1060103002124441f489000340e04004909450340e03000f0060300e241c64000980015a0351f03900034007600000d01808090802d255407401e1040e802c1607040154181c4000e522218001d86950b1002c03603450300c2c03d00c00a807540c0c030b02407003070050700e4860303451602880d000600219465200c4890041c0c00e07088814107102251014a040192640000da030803182042140581340003100c0c0c010213134a5054840c80b03031141042d8050701c02990001442560050940940b0149158003c055054941d5000c0d041c02d8407140b01d000286895158442000303006594490003900f039051805005450a01c25140e280580c00d44580c4084543e45038036018602c5220b8041005c41c40f0b404111006c0c0c01e000340074014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 522309658 1250 522308408 522308419
    0x1e030f0c082a0a030b1f050d0c06020d08040210260a1b1d010302031e0a020304020916090504020903031b2b05180f090a060e070905010806060313121d 66
    0x100041485c410351154071501d081a410959088070801d1b00b03001e2103a4000c02e6000d21613003c15000d21030003c03200340640c3d0380c42c3c08680351128862820344907081c1c00c8800a60012501074410340941c41003103281c6011a540c94003402c0f42007030040c0300c440528201e401c50a00e50f61002840d0b40b0f00102c813030b0340c0ca00c1e010710305040c0111000305151604041c4084d44150501d41c000021130321003440181c03d09071101da0b807103100190f81015466540a503000f03407800d034460408400030440c0324852400b841c0504041c0e4681d10100d82c549800e000280d0408002c040d8180014889d01c0c15421135480b11040d034003600d80140c203007007141e8003103400d010700d9036059030003841c82da59a10000907400c40119406003071004040755040c030705c0c48005202400309025864111200c6401c1c07081c941c90940007076080e16006680042c2540d00c0200880354049288503035800508680b022a150b0700f4100000c580148084c120701d40a400c070340e202c00d903050054014030400146544541c840b04145401443c0308414211103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 522310908 1250 522309658 522309679
    0xf0f050601112a0a0b040906140108070c2d05100209090f09030d1a0102010b010807020a1b05100f020c1909020c0f01060f08071e030f0c082a 62
    0x1605580c0e403c0c0c1d4516072002c1c158108840254044210000201150050080071890f807035a9072100542c2042c804c01e0310a9040a00c0800c0040c0025401c1c80e4421042e5510300003503558400403144c001c0e000c1010b0307038542c040030780d400c0c285402d03450300c1000448805202d0048041c24680380b49400c601c1c4c0708003002c61b4414031031940e240e41c80d551159004161303050505496250aa085415071182c8650407506514141c6900d0b040052520004000c00098008200c9200c0220040d903152a0840300718006800c0120440000f481c10340c075101c02400c2e500781180b00941c4a101144460101600200210300301c81004250b040e410480800e51500c150f4111450a9428510b044007021a005210304580c001c10040c600311010411034503074116100003480007a42d5841c0200c003829041c0541c0031607000d004400300d2121070b00414800b09400380078030210460310f95101c0710020851b0400454507103d4080c0006403000341080320822814540020001d45040314940441c031010b02e0240c0341c0034282c440ca = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 522312158 1250 522310908 522310937
    0xa090e010305030a0c1703010306091b142106100512010c081815041101180e0402010e1216090b030a0f150905030d090b060303130302010c03120f0f050601 68
    0x1e5501c20107139800c040744050207a18041e03000840048240b211178402000000600c0080c0c0c10060b04a03010385180c00f400ca842c804080203c042a004000e140310005440c20f10504050410071b1203860124084d0707196103580480e04d800e200c02070391000e4400300c0b43c4d00240054901102030203049100080200324903400c111001c1e2640703000070000d021a042e030105100c0c40700d0301841202c12040052401b000d2510b81440c103991520842e080440c0002e4840c640d1050500341000c45006440c582c0000480c280d880e03500446d12400310b1081541c000481d484100115181041020b84c035040d003001c0318420908241c0404121352036224000e10a41c0000b8264000c070344500102d200140d00310400d10188002c0034110344c040c3c50710003401099448005403802c080601e940c446000c09202d54040c4100343c840d50105a0340e8000d10b03c8544803030001c00300c04c0005601440c10701c0801442030805d040e600d40c2e5403100d0740485600c500e070020403680703c120034406400188100c0e07501c11403d01300703c100480d588 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 522313408 1250 522312158 522312163
    0x1a1c021b0a0b0c03040201030b030a0b0a050702030c0a02060702010513121e02130b06190507020901050406060f11120d020c07150e060c0c091e01050f100e0d0213020a090e010305 78
    0x5041040c503c8400404503080d64403d1304000c1da202030103001c64008024a240c0b5142505081751f904240914000c04640d02a00c08803c4601d1100c0c40001044ad144043d020441c440d84020001c0381401400c02c01c040b008220501050010301c4500601000d004142c182608812402d140642402c06034040080059403100300020038080c0c1e0a600058580e07080000c54014030681c40c1c0302503003008611804004607403010081944c00d100313035103d24180e44c4c2e4000384402d44a9600603a0041044540d91400ca584592008071040008008441d54001180002c0c00158001024a806942c00180c1107411000400c10100148020070900b00e56226802d0300901000c00c0400b403070300c100b0340090360307a02c034180420200c041d2040050010760301e4200b04d416500034003110341280322007800f04000090b2614003504031014912000d00341c801100d00c0840e0858a04608414943d4000e4503203100385c0168558524010110414000050740c4982b446006002002964499800d8130622001440000c0d0007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 522314658 1250 522313408 522313411
    0x5030f0f0907030213020a0905040506091b072415180b0301060f090e100911040209190e10080109080406032f030417090306011a1c021b0a0b 62
    0x511035080103610340e00d41280c14103040b540082e500c1201980040540e012a50040c241c0750b945450b1b8141a950794001e00c000c0c2e45c1c0403504030b640721001c1000a210610b580d6600c1c44d4043c0f5070503031203150010701d07580c1840029908065800d2042c0e500c2e00d030050200c00344903600e140c00c0c07080c0c03010710540e1802881d0054401d5100083c11904e803a401d024000d42c8094002101038800110715415080c0c940300000002c1c003117500c1e4083c1a00ca01c03407809050100c54441c002005130800c1c070901150080c5014840030754000d05045401ca080580382c00c24907949100301c3d401819003420300c11103d0501e24040500540366412032041d6915256640c400103081c0c0d01260111405810089041c0108000710742050032600140300d4001e21146070700c100201c09000452141c0d1084029403001c0c0740701c02e00c03074809010b041007180e0142d002c0001480200480c1e4000c061240c80480034038680440004900310011a4801500e00c068010035504414001940b8040000090500421146440d9140d03450302d82c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 522315908 1250 522314658 522314671
    0x50118051b09041d030903150c0f031005040203040b160f05071203060b0408030715060323070b0a0c02090c120705030c0d02040e040b100b0702040b1207080609070605030f 75
    0x1d00140d01840d40d103a582103e460b180d21000f54560380359100c3c00703a54490340f203003c1d031600c24000c0e07a146a01801c4002c4a4034041e603041c5c0c000a060910b00d840303030350159101800c0180d00441040d400901603645000445c8650720480c054841e0b4180b0603001c1503548200a90700c005d100503203031410714043d07001094484960300001e1106441e610050f05600400315078105d90044500002c02051207200007000304082d40c0308551040b03a8580d81035400c4100c8803140001018070950300700c000380c2400f079900304a0301d40d01c841040d501e00310f503200301c5440d10350300030405400492030b1910308400303503d000015640e111a03808005840d00c4122100e404c486080203055505011020001c243c61600060035206000c00262046503619210000d007909200704941c21034a000c0d9000c0002c903554520101501114120740813103080944035800c00c40503001590100303400c44101d000f6032982040401400c001040e01c1005801c85080c14080242050700786e40040091282c1001031154a000405c0010751066 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 522317158 1250 522315908 522315961
    0xb03011415090d0503131505180a0510030e0c09070c030c03020c090a1d0d021e010f2301150e1507050d080114040e070e250305011805 59
    0x901d588142040c5000e8055203940120f50894036200f00300001009141304803803141400001a9180714415441452a01400c002001803000880c1a07000c0d5524450380440101015615600e40012075070300b1815010110002e9100c0200b802194418407090803072030020b076190740c00d52424841c040e01684209200074100712a106550091500c02e00148040300e000401101d01c50030401240b0020340084055440c14001d020803160800c4400504e012112180381c014000c0c09001301c0d058080d407080c555400340c2e40d540b988000440c4030700c5441403480c1c159000b0310702080300c2d0a91031018403a03c0c058000034404548650920040341c0c00008403001100101c6181090386014404041d05000741200208076115155011005582002d0601c0c180c1c0c01d40c00d00c115540c103a1408010503152002400c42c0203400ca041e050080c4c1c040420b9469110f290704484080c60700d440000d4200304a0521019800a9561070052169200403204601918030020b001e00160410002002c6100410902c0003c1074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 522318408 1250 522317158 522317179
    0x6140709091404140a06020a0c0b16120e030409091b05030a0b0c0a03090501180302060709050d0602090604180608060a091524120203072412060b0403030c0303060b030114 75
    0x41010006041d10580c08002591602000b800150400104000c0aca03119140d003800981202d119031001e40890143d55920540e6070325507200703200100130001000c0c209000400c00452001502d005000c1c00b40d01c00d40114584a1032840800701110203600414404c0e04600d072500d000c910030403022078008246168056555240c84d909500800c1c110400501950810a03102c803c0c1c0609508441464000d800b515541c0c0d940d00c1c81242d89030801c0c024a503000008800c1400401c840d0b501074282208041e0200c2d140c15120069044d426103209510521707180c0350710302401005000c0c0440c0da00180280820310454105607280702da2010410080110181c0d500b0f0742e0181c4011000c0000408004070076840c078180e454205d0110030100d5544141c0c000d204034880060301c6590302c0c2000078402070b056001d041d40c0c0d030b581e074048400010007400115419211003012401075401c00040008501c03076140c0300400b046030715018064612036440040461820b0004100300380c3c60001100f034909040b210404003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 522319658 1250 522318408 522318443
    0xf08150708090a0602160b01120203010605010f1407062c010f200d090b161b020a120c0b0a0801060e100f12020d05010b040303020f0304080d05030601020a06140709091404 75
    0x64801b18180904402605400000c80d40360407001040c429000b640240007003600d07200103458045409582100040309004803070a0b80c01818090050b2a10405011411210408030005a80c07400100700300241010b002a10a80000b480b13001e83d50040424240580c100c2c41d403442007200d010340c2001c51400d0001030310056910199111100c902d60082004145023000803c9400103480d404242000c14610402da030b00945c4959000180503078002c04000d151403c01201301a40640301303c00b09c441c01808240400d454107050040c002e03880d9140d0300d91003658503045c0010b05951100c0030060058040201c7c52040342e41c4450050442c0e00325081100c11074508031f10610003442503071300f2044142e01e040300220328401101300400c00caa000b6400c441d02c1c2561a02a99207071310581c4078a02c0d1b980d210700c03900c03400e00340a400a5507006105005070340c60024261102c10a0394040914445154480d50400a1403130b00030501d40064056a5010044102503001a095415020700081c0c4021700380138900f0b05 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 522320908 1250 522319658 522319687
    0x22080c0d03030b09010303021006120c03060b030307050a030e0901050d0317090703050102160210081608130f0c0e090307080409050c0405150a0305060d050c0f04060f08150708090a0602 81
    0x1d1100003405131442981c0d02d040080d00d44100104400605081080c00a0900032424016038800d40012804200518541c1d68000511181281c2c580501003031003042c0104d20b0034440307030781014000d4689545204802c01003014109050708030340c0c8512100c06482003c26800107040b41d0190b01041c14402c0d036100c82c1481413030141c45510041056000085600114918035500d00407544203940c010a00c0000c00c0c01a200007a0441340320641041051501c00250f00c0b6100d10340d004030341110b5641c00992540c4606071494410402512990903000003004060076041500340d001d040c040c00b0b9810907200d55a0340f00e05228600c9a030540545600c0070034640c500000131100203100c01800710010f0740c1c1c01900704001d500001c0300c0402080c54680040d21604090754800e00159104004d01051484142000344840200d50056040340d03590030089280280c2500c0380c40035003860030040c0b034015900741048804c11001007915040007116014001500400070b482c01d5002e80c001800341e00c40910f48854078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 522322158 1250 522320908 522320921
    0x4150e0a0b120f011b230a09091113080313090506060c0d02060a0501140a03120e040f06090e16030b280522110103021803030301030822080c0d0303 65
    0xa09000b0f1242007204031005602c4515900c0c400301100078400440036041d9126503104004181031848001007007000c4c04044003c5c41c91040c00d0408029068951415008880ba200c000b08803a050000301254000f061501ca900184a40c10046140c41c1e14080c6202c2070040900c81c03444a50f48a03004280b180c1d5540d030555480515120031244500741c107410082d99000c0c02d84080724561f24000c004225403515580c00b0240c00c50141c10249420310316520340c041c650b1110901d008021200322206035036607070780c02803005041030070b03e0219400d41042009012112042248a2554084042080c41050240744c40301103a070000c11562407656000f5036070682c000f0303140411404140a01c1202c2c0c42c007881c0d602690007450300c01801c0030038001041c1c0d0326160380c200c480c010748540c1040b1950040c640c800d4004118541840c60700c0303800c0b40000c03400300345190800e8000711001080400d41d10440051360011088114125244120b00e43c07400345415102c181099800e806035400300500780030306020b5008807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 522323408 1250 522322158 522322189
    0x90512100c0e0907141e07020d0605270c04090203160617011217031306050114040b1c06090311060f01030312020405150a1b030e04150e0a0b 62
    0x610140380800e0008150b6031840c2d19403403242d0b40d800701140d403491281c280f5425100c000c0b03510501c1c041529800d03001015040b42a862800420002140141c4400040e001c1e4240f190364003041c2800e20001844a0524401004040c03d1140d0328031089658005a114030441d001d5900042e00e07030140c0003080c10502d2a544210700c02e6541d100021f00d181c1e1085a40880d05031031001412180d13222804610b00004203003010b0301c101034040050310044004001541c009024000c0c500a99080f51741344000c4e12402d030700c54460781d80b4254141c2001d0070540140b461070141120040c0c0ca1b1000c2200c2e4510013082498064a074564880c08001014041d9102c40c5450b00e00c4ea045642034030740040307505007200090004800080c2811049a5410742e1402501c0560300d0007402c203803802c0048008840035400c207806160400c0712035904c19903060603840c2c14040642c025903c04001541850500096408103103042c0130240e0301440030403540402c41c414a130043c203100f1012403400c0c111800541040d40307180c202e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 522324658 1250 522323408 522323411
    0x21c0209010f0602070506090f010e0f0d060f050106020a0309030314070807080307322a03040602010e06010b030a0b0f13020c100b010203030c0d110d0204031e0309051210 75
    0x31642c07040081c041c030100c402035800c4600450301c42080c0081c9003c1c00648981003074234505440010340c0030b004139001c0d807080503018141603000400003543c2240680425a030251341d543c80c01c0040a424000c903405000310b03000034412a1420703500103241b0012840094100441e10100c080d140402c5421260955040241245c54070500d00340b40c44150700a81d8444003103110015508070b078013100488502241c2001e60b00545544c4074a0300604298400a0400c0081d490100b82c003000b0f00c0b4031105442c1c0c900b1040015501c490070040081e00f110740c0d000010502c0c0d8000300040000034810002c50f9400280c00d800803a250f0002d0b4089845000314111242e0309c070070410120200c070140c950150414101500840c2c00c40302034200d001c0304888182c1c00341e5005030002c10004510038072640040401e00b490135400030742070410244d0000180c00031002d035480c2ca90001000c0043c801541086645450b0002c4080d100d000180d4001e0122840c0e440381c2802820f070a5043c12454000340050407601e02d48060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 522325908 1250 522324658 522324661
    0x190e03041d0a0603050d11030f070b01030c090510060309080d0e01020a121103041e0506040308011a0c0a1b030605041103010606050c060a090c12060e070506090a03021c0209 76
    0x99140004042041c08030000900400080722001140910320841c1e810030060030700140028000c0320314007251025100c49200410240c49441855001800a075020310004409541946002c4d15015615404a041ca80c180720520205004034155441180d003182000258440c0a160040440c0120301140c91f48600e01842038000c0d4106400130240924603594034090811421f050808558150002b8a103070107041c000140001e45240340503404504442c0180d054141964586207000e10482e801c500207000440108421828208030f20380303200c4a6040300d4101003850190a55420071070b1000b0704100c80c21500b0303811034805200440051501701506004c10300d041d04090b07000000100ba01c41c003a61a000c9d00041d2544101d05450025045002501c02d0f5100e00081c10041c00d5151f4069070801c02c2000009441e10120514a244138030911010400c0c80341c1118041c14404141d0260340110400c004102007542d40c1c40c1108250307079040794040d02c2c0344c003044a99101c00181e480020b410005440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 522327158 1250 522325908 522325919
    0x4060506040c020d080417070b0901060617060117101e2303030d091a07030b010f1e050705010e0a0503190509061218120903160608190e0304 62
    0x400880c480e09050300c0c280403940e64140c00300c2e0f950041902540c002410800801c0008010194104c10420640b850b2410500684c48a49950400f510310b602d0f980e54410040121503048100c1c91003414500e032903103d0384d1810030300103010085454400c2060040c44000a05407103820105600505540120318040451303540303240c040c400b440d0003403104900b044260300d0040c101c0302001c040300030b4014002c0c0d030401030035a0f100b001502804c02d080320040c1007124580d00307121200f10002e1085580b65404520600114009041d0211943c0200c0420030a08500689105a4118403032030f812280f9200e0340c0c5226500707180380107054840d496491b40c010380c55000140000040941840700b002040d00c044080c440c1c005450714450402d0480e0006000d201c080c0c041010b40496590010701240040e003c0824050154100304d02400102c80c07500e80480d108032942400c10a0800101030f00d90003010640c100080604007480044c0329100784101108001681445500081071015030082184d40b82da4640c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 522328408 1250 522327158 522327161
    0x705121608280c021206160c06090503030a0501140f3d05030106020f0c0a03021c240e0601030b0412021905100506010c0f0b0c041a0d0b0306090714180406 68
    0x180164400c600c003050b1911482004680b241c000c090303504807c11181d01c066019100c0302d0ba11441500d80c181d90b4680d62000c21401e100640c898000d821f000604c5604000f10702c000c0c0300f00d44004900030a825510020580c0302c1d00f180400700e0700b01742244824808007880710f0103000420066241640720301c10201c81a071342c200010358165a001d4090f0303914041d10450300e691310003207050910340c40149144100054203191926002401d810300350030060b5150740d21815003024043d01e0404034219081c952700c41c166010b1183c03d951660100c0a0501540b464940d19400d04000d00007800860403007003001441da000300301034010203614260003500e070b0789181084c0d929001005c903440d955030b00f4000004c0080d2312030700c81c03580d02e03540c04880b038075402a15845400b82080c00406440c500e10040001081c0c20380c00d80900c040d5a8a40e0300c800c0e644500000c001f0095504101c01a030096001009002d00c064000c20040c0981d42c8426803e8550807015001031f41c0c3c0443c40c04200700905000040c0414880103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 522329658 1250 522328408 522328427
    0x31504060e010911030f062101051302042f1b060f0f0f07080a0c120609020d060501020309010909050a021207050d0b090c07060f0f060b070512160828 66
    0x14500700300b00c00390380104d1204961208580403103001c01c0840005855150007114030304c0407440c6400d0000c000f450310000c01e086800c00e031060051340c0c2e1344848401c04c628003402105898650148102c0046a022215092545a103a09107009480101c1d035141401a800504515165448101c1c3e040b81850802224900001d9521100070b0101e0070001d00e860f041040f6050040f080d0380d80e018400c1c0d0f0f9107440040107080e528990420000c0d5900509050801800342c080944000c2c84010b03600d038503400c030322011034000e507010505541092110411b143c0c1c0026010048403400c8d0404101656885850310003881901c20012281011000b0b110146610001900c0d11030a900402c202d46040076081082540c030440d140c3c0b2203000100b00307500024416400054030315002141c04034468101b584910182c2e04150040c10b03801d403010842009200701006082681c1c80c003006900d260441001c0394001c9220f00c010f001d04880e10004440c0c2442c1381d00e180444c41041180841d12444100000c0100008038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 522330908 1250 522329658 522329669
    0x405060702190b18060310030602160b090c0a0801111b0118030305060f01090b0d2004030803041b030f1202030d0e0303180f150907090203040318060c030c08031504060e01 75
    0x3c549043c404c60300f4400101e03802041c1560b100d03006c5916507070f503480107503005001e183d10076546400b99000040000c02c4580c0241144409015418092801d100384a540d980c0040c0081c1c1c1403c031600141d00410044500003554441c8804a120b08400e1103409000b86425480482c04044003580501d075266106601070407081f202000000022070044408240c90f000e0364a0403581001421001503503540554084040c602121761510381024818a054100e070380141c8028000000f000200102c3c1c464400d408640c2ca005103640c14150f403502c19181c1440c1000806404211450710926030003041600c42d280802c450504c849224842e400340c40350010b69902c120703113612a04603808010089030010480780c0e034900400103900c0c0310508800d00217025019070744600940e1408180e01ea160b000451203140039440702035000c2c1c640040f413034030380c00740342d0049013000b002d00c20107000240d0104e00c10f10341d40d0300310300308903201d88600046040c803e006a0203998414944070001410f2020303008002d0480b003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 522332158 1250 522330908 522330937
    0x230d080a0e0406050907200c030307050c040c0c0f0b040c0915060905030a030518010306051518060313030f05160f05070f12030f020a060e06090c01090b0405060702190b 74
    0x1640e60080c0038405101b40c1d04480401c8041c21005000d00c03002d03038a01c1c0392952080803035407100f420602090540d030102e082074036a0b4001002006860a280c007903407003440d00501d02029626015119441404440040180808020000b181c11702000303010000c0035240900b0100282c007400354502c00102c0300c912854000c1a0310000c0066207150200e00c0100b55901511000c2c5010b01400140c400a1100300b0344034149662414003143d15100c4070203000c3c0100d40d8041d45940c40345c100025a00990202c100c841c0b14040402c10030110842e82840ea442d001c2e0300d8280051640f295041c195218010304141c400150050740520341408400011512198000c0050325207094450503088404200c41c00340654226106410800080c40344015101818291054a20340b5844e43e6400d01512959040c42105510a0342402282c4000f4400c1c401100003d007086000da500c0c0000307000795401a84103451040001107802010754039480c52842c180b140c4403880100c01916600d2804040d04003c0b004a13048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 522333408 1250 522332158 522332171
    0x1602010b0a06080f0c0c03180a08060f090118152310030309080a0302030a0c05030909041109090127021305090105070810050603040b042103021c020301230d080a0e04 73
    0x200c03100444424851b404003451401d80155aa0078084004032001c035080b50a8950008515100740324150040100f03140061442c00e01c0480503013522190340b124042c43c0904215040017a1a1a61590f420040041c0100b03036002001c4015407040c51907035015414028a00810407181b0003a02480181c9119440d0082030544540c0925540c03207003502c004016a10800c232201100d801245c0c0c01150620400440703242030252000704580e05019030701212501049003290420b0b15000c0c1d030080c0c3c49440300300200001e110036031525400036035603891040880b015800c0030040d920380b4600001d04e080f041d00c3c01c0c02141044140d00c1d000301812156040040d04020201c0d55410071100e00700211407000b002c0d682180c4558403031900b01000500122000044ca041400546a400c040040611000d442c016210508280c46000000040e001a603c1c2d0348100010f00c044001054580140c00c20041e44246050041c00499a0810601405042e807400400c01c1100594800c100070700c040400e45060128 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 522334658 1250 522333408 522333421
    0xd02040f021b0c013005040c08010906291302030604020d090813080a0f080d0e0109050d020709060315020d0b090a06030c06030207120c23070f1406031602010b0a06080f 74
    0x4015200340722410741211000c02e00c168600700d401c40d0703800a012300d10851800c4d94500019003161840d00c0d040b140a81c5504000c48042162103400b40b4003807040d00c003910303071150f0800024a2038120140a80c51582e0101c0440d03050f840307d5050b140c007400c1111080040040e40d00f00300c1c0e0030f40c022290038901c46852400101d2280f0740440c042d03442c83e40c040202c00c0303050320325541e1110300e4008281c0030600c10f58400c0a02140c403824001c0c0480a80500c02410380c0304a5024024100005500310700400c0b0305080c802c00005d80d150403001c0001790034072030040c2c0300c1c0c4180418001500c2d0452250368411aa2014064850300590100003142e1044000d20b03422650b40d5003d400342c1c00340c0712020f410031400855050740c450041a00c43c000b0351190a10b0071a0402c500308291031481e24030750086043d070000c0800c1c819041d00926440261010404040172000c2d003100050b10761000801509032109884141c881240c000d400243d00c110300140340d502c8494232544020420300b0121400c000e5000000c0c04102d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 522335908 1250 522334658 522334697
    0x1c0510080a05060408030601030929070905060d05060f0a03050d020d1404121b0605130b07080405060a050f0315010216031e020102030c0d051b0c0d02040f021b0c01 72
    0x100e41c2c0c0d11501900d0680d403251204c4516400040a2034103054941c00c0140c002860070700d40350303411b65142141120318803109807802c283c8403000300010280842c104082c05543e48039002d5400d4a079403000e0100f003959401e40403a0442881c04219a0060482e035070100400a003c00c9001840c1666400c481520865013011120a1070f11800c2c40c030303022010001400140b1041c1c034080509030140441071243c015a410001c0c006209500100c0046c2011640c07510031580c0304608002094805d032104c2c2806406d45920407180f041c1d2248a01c21000020402911070280d029240c040980040e0f194680c43c140351106002c03401825501c0c01400b030015540840c0155031034081c2940d0700f1019514843c840e204604854103088a0280d065200034030208200190070001e403a00d031001507a800381c5030b504c1c0b4090354202002c1c000d410074064119840001283d11041c40054031a60122000f042c1054241e850000903c9010f00c0c01c40811525815600c0d010740004000d00c3c0490284c3e00c0f81c00600d4281040074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 522337158 1250 522335908 522335923
    0x3090807080306041d0616050c060109020310090f0b10170c160501051510020303071205101206090209060f090103060b010315081614030a1202031c051008 68
    0x140000000d02540d40460451006540d001801a0000550b8100c45990000801091410401c0c0703900140400c0a00c1d0100b0b241455140c982e801c0242c2800300410401e07445031014042c49401c95804000281800403a012040050080701c1c401c2000044961820015182c4080c0003401032080b41c1394004400c1c4100c45080201c5002c020001180e2152052031a20341c6c0240e02851100d0010040b805c08507000784a400d001d111401c42402065807040240242d64501c00e034070744159001801000f400c07a421a070b0000074015072020000e0b1b10794840c1d40300503640715140c00011040b910107080108001c2c05600690b0103a0003100e200380c03255541c0d070401c420100702c1a10b040d0044120801080000d02582001130303241414100820b40c0c5100c5090203070000e005034064042a4040b425282c0e1040401039408054445407614172114803101c2d01090365012148001441c80b804280b400300064406d1040d29031041800e180348464007100d054a801402091780c0c400000f6484400c00501468002a030343d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 522338408 1250 522337158 522337163
    0x203030901050f071704020102011104170c0907050d0903230d050a0c020a060908160b04110604030b1513050c070203070e070c02060711060d23060a18061e050306070309 74
    0x9a103c485d03010f4110700d41c420007603c1207040d5901d420051000c3c034000d9001e40003900150301d0f00f0301368014034115540b0b403492408200780a50303200c0090081942e031003c1201d45030351601c40d020441110a19089883c1d403401001c074020f88444030301384038004115000078940040325031814405611000003110890f08204840805607022440c441c001809a41040c400c03940940e40e59800e140c00705980d100c0c1c81144c22011264500760070100001c1049248012030440d00a8038400e0525044ae0303140d01c941d000140c1170388620507614070b21768031036034403040303003803010128014180194100071248030402d03041032208034420b0240c05400300d080d03810b04c80031622601c0c9070303962110519025001d210866124400940d02e1141001100000740c690400800100c40080750009503901001e0035101d07001118850383c00100d865a051140c240d075004241810f0321103800c0c0c00b0004050449010300146160b034429043d4408030100310407a2200400c04104440d0b007502a10069600c407101107048800d1040c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 522339658 1250 522338408 522338417
    0x92d03060f070f0c0f030f09060801030515040f120e0a05042a09030f030e090a0504170315041509050906010803040909140307061d190605070e100203030901050f07 72
    0x18038400e10405808035054600c3c00e102e0501c0a15071207005d00b0b0503803400164042220b81e1403080746950300030b0302200245124600401c0a5041d40d0b641f0f51a02201c002c00d03801d0203a410042014080d59200e82e46c030b0303564429180482059840005030074001404c40076449204511000501e9090900680d4030b40341e03c078024051000c03c07822000c926203c0e00c1d102c04081004140000c00056440309000640034000d0710381c1c9800900c0301d13041102c04580180b03800d003698140000d0000044502c407804003000040709060303840342d075481c0c540300b1000d007011015940241410402e0798440101c0c6842c1c0c094403a0090140030316640c082d40181d454900f8440c805155004010400801c0b100743c0c031540e03803280320702d10340c45a014a144541d49190086001a250309680701d03140c015440e00c64460503147e401c808060034480e140210708286205000314080c14039500c1d500080c0c90b4501c5004240a00c000050818512003c014002540c940084980282c13561800c2c0100d80c150034600c08079481400550784 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 522340908 1250 522339658 522339661
    0x141305040f14011703090306090609010c141606110409050f06040501030302150c040f090e0c0901080c0103051308070b0406061208070303020c0106051c02010e0414011703092d03060f 80
    0x80425210706104d641600c10b000901c0803c0d40c81c0d4041c00001e0054080900031711290500880050844000c04580000e00c403841082801140401e030698a400054108000d2095101d0038a07601501540301020b075401000180070988041c6ca600140c00340e6217805869009540e00801c4c04110b8100b03000240150744142507051100c01e01400d01c0d0f42c4100c1813034943d8201651001c4104162000e030700082c04054540e18031444038801000f010984400484681b840d6500d0529440d883e0f500c1b400d86941055210700c0041c0d11702070501050031109070f00c40b01040c0e48034100c2c00c20400c400b800340c40850f440e508010000a0a002d900210412903400503003061501e036080d50240c00a51000d070344182c2d40e54842400003400d90325503800c1e102c40d0565400150100d0441d10006060900c82003801c0e2046d423802c50813100b415290b810413815925032034120800280180011888c42c010f0030f548036845807070030210031011a4242c03048810700000e0028100c4a90f00700040545800e0300b00c0d521000020640c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 522342158 1250 522340908 522340919
    0xb0304051c02030f04090606110616030f23220b070f0e1002060a20030105060918010308040302090702031e1605064003030c141305040f1401 62
    0x14a22609403240122813070500700b020741602c80c0d082903115850603507840d10200201c0790000004008a01e502000e80303c149440d40c0301d0204507242d42025001c26541d544010441b8034294001d4034030100c0031740ca41001713182000e41c0206003001194109280305096089030300f8004003200c81d0490951046900312180e44c0c400702100c0c0c2c0e031281c0351401c042105a41c142e48468a50340024000c03144194098021464841007a0b0161000c190400d0040740c1035001010318042200e080c0ca05440d8200e8140d5650b81e04bc000140380394030f00003150031450b4500c500000404c6488001013040702e01c03d0340c0390070300740d40e0b03a4000307980300c0c000c040c0c3d0510760248498601e00040e241c00e004080d0b00e0010150f00300d585d640b949a461404d1400c590032010b98603d00b507402d20f200408020130309900c1c915508007080703907008000c0c01b040e0040100028240b50325128204040c0d406101d1031030015020411060b01e682491038504c8400303c0d6889087d000f9480c00c0d03429800d42519001e1041c0000002d50380c24103992030003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 522343408 1250 522342158 522342193
    0x91c050a020f04111b0c1009030210050f0a0306031106040305061b0d060b21091e01020412051c0302090a0e0604240f0b070c03030f1211040806010b030405 68
    0x298001c1e44107a0310f0301c03120008602800034104541c00b035001143c01801d490002480c0c0744460301b072180b2414a1150a2691650262041d015642d0640340b82c00c101310800070540e80ca01a51004011100011880c1950564554800f208032030064006030000f903400c80500c1418842d50101400c140c00c0740c0002000d5010804640b02040388a5881629140051a01c01c1c21030701e203900f02e042e648000190700d241c4a0b201c5904101440603d01c28156503040c494881c0d1341d945d8524910b0115a4991000d9050000c000e6054800401e03004200b0341e9850400d1612940b18103103103d0340c241c181c0c0c0c0161003d1030180302c5d00c2541c202e420003602c080b40180c14604843c15100c4002d154039032068841400ca2402e560001c44480d1401a80345402880341c1450180700c030700e49017034110340e000c003106000000115045000e44001c0303d4042c14441c0c203420071000704903202d40c026007050b120300e070030940a2641030b001c1000410450740220300b91105640c0b2650444001c0c407069134040c10306d900c0003011000b03c0284 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 522344658 1250 522343408 522343429
    0x51509060307080609010618021303031215030804060215070f110a080d02030f0703020a02030f220f15020105010302360f101520160b091c050a02 64
    0x201101d01483c0e840c0c000703030314008080352030340b00d02c0c1d441e44000c105a9001c1c0320030b0002c900500c4019410b2040c9850311011400710392101804000324062445041400c0d41e114603404803c54902100c03207a16420030a88541c01440303807070b0041c81a020b1034804030082d44600d6028001c213036241d03482c07800705250480356440301303003907454560044d24008000208400c006115240407981d025840c0d141c045294189440c0003025101031600404c40b1a100c0d0754007000301c072084400d00507016103860b503c03c0d80b080e19456058070b5148244200f0b0000c9070b03c0b00608124000c40d000b003101612003680e484802c030f00340c40083c44000d410401d60909038066502000c90380c103040c000c140340000c100c106008140c00510042ea022000980408140003c0742d10100880303020f0038010401e204020040030f40100540c00c002c0041718441c081d44a002c00d2450107106490558071010308a03241c05440b292241c4040d401001400c0c455400ca180750511b41d01403d2240c030081e502314025242c030398050380074040104030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 522345908 1250 522344658 522344671
    0x90102010f050a0603050d050c150424051005030a02090a09060b210106061b0f1e0302061608040309090b0d0606030f0506060a050303090f032419051509 67
    0x1214100307108000304511600b88103822029010030041d146040042c05e00701d000c0c0028040020400c060b8410a5000440144440c00510007071103c0d55141021246c0380248010f22095244000c0d6401080b41e843d04254010345080d090001c44a944104055072482225402500b05949400041808000e0760040c1c48080c007460f40403410754004800101c00104010559141d002143e03840003600c10b007486054080d040a09003c04000000180c000d0004881d40c1c00501050404420804100ca80d048088000782d0300803030351140440d0b91401949404080300d180d200da908030411040290f02c84c400480c02180c058a0300b0100a00342071990001c0c1401d1408140c02c4242442100c0c0028030b107201d80c50046010f006072034401052850041d05241c03003c0c0c00e0f0392054840c280107115558000c000c0300c608100849003a40403080c0071002c20708001003410861050041d010082261502c40c96615119821890b0801c100106100301141181c0041c0c818002010350440003134407034201a418544c0100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 522347158 1250 522345908 522345911
    0x1050405011a03130f0507181104030206160b010b210402180a060506030705040915081902040f09050c0102070b0a020d08130506040c080f03090f04090201050c03040f050f0108070c0809010201 84
    0x1011340d2140c0c0300c0c000a40d50222540c0e40888010042d05404020340b69003c504544144140904185240d000b4091800007900c650740c00198600c00310100c5416100b00303903100f8040c0025694409444003960056030744e903400c01000805901c0c030030650041c004d01c101ea006000d54501d14204005505084004000300b0200e1343e2940f000c580fa58400c000381d4400d00143da503007665141403d6440303055070085501c00c4604128040b090020f09008900c041840184080340560201c803400010301803e20003030704003001841e03c0a481c0074040007041c110700e6564282c0031901280ea41d8003d461482c400c0300315000c0160000c1a542c00f10510401e01541c205140d030742400491012600c80703a003000000c1d207007100c148a8440c010010a00c0c1445201d8401000740041c5041030030747c0002c218440b0020481d24031566450b07a202c0110384c01401601c240381c03000e00441e51a2a12103034080e42098950040e9032084901091541c0650300c80c07210700b48141007940d50140c44203465034421903140c00c4503000c1f50655 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 522348408 1250 522347158 522347191
    0x1a09030f01060b0703170402031c050906040306090c06050412021003110c070501090b07020a030b2502010e07050a0b070f0206090402120613050f010b0d1d1501050405011a03 76
    0x488240520800f4103581d005a0b641c5002502e005006e03803212480c05100c1d1283c56003000301681e404580c0001c0c0b100c154140791840c4104d035400321058881c0300070541e8000c00205001c401d111041e8441c0140038401c03101d04070b07c82e071502802e860f503026610603006403075100e003000401410490248031032841c480c280402e900001202c0c001c1643c21401064650f54030640c1b0401582d0303070110603c002001d0141005180809030380229060351041e0001030043c00001b008282c1c0a41d503068240c46009100d48411011880900001d01800105211516503c41d900021800340341103503102e811038400039141c919001d0f0f16074a0701210824014143d03032100c0c040c8400c2c000c03915180000e0031140e90b0300041c81c1d0286011803c2100ca000d40d810b1000b04c90780707410f0812005902c0f0a0b0f295044da5270305110302c0d813556213851128000d0200c04182c1c218011011440c0c1c8100140040e40ca0462200c0302900507480c2c1c0c03148144000c41e082441403605030034580450303240300e01c1120021a0000301000300f071880c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 522349658 1250 522348408 522348433
    0xc0d391115072006032e0509070c060c05130522150801060b0a0903031107030609080d2a0309020a030f0503030f0703060e0f09030d0e010b01090503071a0903 69
    0x4a400c982001c0d51141802c14051104a1401e080c00c1c443c0c8004a500604509000c011301480b0014104528400c02c858040555201c0300030199000614004000131102d1403d5a801480136040c04c50480d000c0303040c4501507a005000d002547c42d6601c2218503802c92626040c200040d04801c0141c0307400100d220589001005050700540400c80c114890389144130785000c601e035084440c036622100540005000c00b11119501050050403a501450078500c820b1840c002e0f1810315590740d00040c010303454800c0650802044002a1440c1b2401c02820094080c05c2c040b0b08180c2256051240b98800900071a03003612400395002c600600c1c00501006034603030301ca548204e8030103181141603443d940044200a14803040074151540f0400342d24040c400f65140215811f202c2c4000f40008160b0441c00c000111803800030010ba695085800405002d0840a824954000c00902143d1070008814903c04110f60038006420303011560302814000891420081b00c1c07000340c100c01d00560385801021102d182c23 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 522350908 1250 522349658 522349699
    0x130507080a0f1506021b150306060304080409020d0507140309120d06170a120c0b130204090b0f010512070e060910051306050103050a05160c080c0d3911 67
    0xc4c0086400901e0907604152030406030200380d00075544522140100c40030000c0c2031a0503650044001e072030b20398032600d9600e4610b02d03074001c1e90810b019143c0702182c010045805600694085c040c251a01e0440008010844607588812981040e2503031040c684a40c000c0301180007040110000c1310000398098035881000b01c0105900001c01007a881411010180000b00c02400c035a1130301c81c06c0084400605944600420b4401030034440c0d88a0000204419500c541e0406010540e00180ca007032640b40032003401d003c054082c02114014410485801c04400d80003402405461161060084595408041045c100c40040603a85840350a4900181a489401e400e00b8400f01d8000040780039400c0c400014210b490050060500d030303043c2014065420140d00e03421a03440040c0c80c09100030725060810301e00038171410603510038a100e0a0340b16100503a000013054050a000881106812403401c02e401100141c0402d15662a8081030340000040160356080000c1102a0010301c040504020074203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 522352158 1250 522350908 522350951
    0x10605091e180a05060109050109030803070504171e0c210304030501050c120601030c1e140406021005130308070804031211071101030507021209060405030d0e130507080a0f 76
    0x9004501c2c1a050041d01110360140c0c56010101307181000301c04c1d25203000240220954800581048400004500300c58852000c590251524000181c52080c0c5d904c401550b5820743c030425680a0014128003c2018021603124001c15005282e1075503003202c5011070b0400c4443d0300c512041c9100401c00080081d0003070140341d100e0700c901e00b02907403510061101418090b000801d501e0406141c164414801c50300000c1e402034114144402c80710b02040000180c0d0030980b164291695100e010030700041c4154009059071009440c0c1e10240a1607c404042e0b07184004d122100034003140901001482c10303403285054a82c0a4060715250f5000013008180324200c41e80701d0007010084400080400031312140c21440c0d481c00302c0a2800b0019490f25aa009444000440740d0b1a460400000c4004466485070180d60144c0f030000c059800da1640d860002d00b1030904c00002500880350340c035005804e401d0f9031080d144038150702d845d120984d90b0f0380c14940c001028201c520b1205103a0703840f8100c444000000551 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 522353408 1250 522352158 522352189
    0xd021b100b010f0e1e121222050a090e031b0105060909150a0b01030e2505091003031206080a0b0609100b0906160b0c04140603010605091e 61
    0xa0070010700340010030f0209801038407400d001c01c140141d40c1e6900d4002059044444200b0420750f0082d810001412040341e043c441e86642c42000c0280107904001c000030070107054014010800e2028500588580100314496164020018141080040e6483d040003808480c0801940d14141e405104a40f03d5a640015030030182e41d05c0e030810032a41009158650846a0900188054407214034bd07848901d1005000d003051544610003420607034000c0c2c2008241d06458804c0c0c5501007443d6852501204d10f01d6a402740d1450a075100160318100220b03014040c0d000044a000101c1c2151825981039141c03080302000550750711400603a009040c4480c1200b94403640010f007090a1100c1000001a0060700041c41e0528800c3d08008869800341104c481d6903060702e2054490000d4a080c000b8803000c600042c080b081007208000790500d8120040054505283c24000d1146600c0c05001c41800700340942800300d035080295148500e801601e1007803c05d1020b044444580501700401c1c00c08030892490f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 522354658 1250 522353408 522353411
    0x40e270703020109091103182e0510030305030a05061309051f02031314010608010606051909061b052d0105090616080411040218030c040c050d021b10 66
    0x707108560744046110010541510140180b44c6662001c03042d07888041c0c40c2d00b05030890b103241c10301900c0081c0101800070a040c55011003480c0b8a2550645200015008000d500d01c0d1800003141c40050391941c2003a01c0e01650303004d06698820312808010328018024076800310040c1094203490515001d80c9060600c1000503103160b11004800101c0300580f00c265110312401401040124490051020001908110429840700d150304442c1d004001640001c00d480d400d01e0b0001c070319184c120f0002c2c10603100030b001c00c04d400e403100f010403120040b83d402032000040201e9003a04090108076012040b10340668140ea0340703106040043c0d0003001458000d0b0703c041e40c20300300c49030829400703106460b03200202c1400b4203000d00e881d50601340140d40d05079400090120b02d9001c2024840300d06515220340d03901038411555121041c01010034840b0680049110b4070903101202900e00701805011540700c103588a081c28403548074407400280d0400f0f0003c02500f002c1d49504003c00e802048000d0440840010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 522355908 1250 522354658 522354673
    0x207020103050601140d0b040902060c06010807120312020904021b160e0c0a0f09030c03050303040c0b16170c03070b1608011d0601110a200102070506040e27 69
    0x942076402c0200414144400c2e010440f501c0d4400b1411128030030712460b8005451108580001e0040c4500100650031110200d4413446446000a4260582c0c2009088420003039503003285e04403009031040010005290180d4081041c2a2600940f4001d44024405401c21101a2a25150400c0501804040c0d40b100d001083d0101983c004400580340320341d84c5d50968900b10716106810f1161980050030445505160301525104040d64000740d64030991650001d9a68200199203070410fa41c26205c42c410810001a049680b0f801c9550b080a0a0b2001714028070503142c04102ca20142198114040c04210403a031546003840140f4440d44201c80c8140141014405aa0100c0c0e0b40d1020700d082c821800010f010040210000c0c480050118000170065a11900120b414041da60020900c9200e1180740208200034080b44c0075a40020346064801986c400004999501c014880c00e074005208000034010a16500380c1980e1095403422034050042c800f83c1c100c0144500780410301d81c141c0080c1d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 522357158 1250 522355908 522355913
    0xc12041211071a0901180806040213020a1e0201022a0d05040513090215030906161e0c050f030a0512010905011d0a1b0309060b0306040317180d030207 66
    0x900900305241c062005140b800e0030031254103070901c0034120b00c0d5141d480c04203455a0f640c0c81440024411038820520110541d940d043d015612030b0305580481c0f084114000d0315051500c139100780c84640700d4990b14040749002902c541e0302540b6911081c031045540070440c0551146049000d60641070902c0b0081200c1d6421184c2682490020700304001040ba0402c410007503a900d04040e00d0710080d0011001034101c070315100191032100250343d40c8290b004007108020850402280d024800c45103980d0702c40b01072590103800c8545103002000d0140600821450002740e0b4420381c903441015206004440d0102d45140c481483e5030029001a000114001810b028107421615001d0050841450901181d4100400c16488100500d20501300c2c146903400202080540d030000c0300e0326161102100541694154001c0c042d000240c815200781d402c0002116041c140010143d210780d82560300c4198010958019000c1d11001800e669403c1441d003060b000b9146041c05180c1c6000c40b50744005079a2507162 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 522358408 1250 522357158 522357167
    0x2b05031b03280203011d1e040b061e0109151803080406020f07051c1b0f1401141902071502010212091615121d01050105150706050c120412 61
    0x81229030b0290042c40100a9503a102d000b140d85004501541d02859584044c0303420015483e4a20702e011040030020303c018411700201c0d0f01e0240c041915454142c0d4548000505140244e4a00c11300041c0e16580800070254410f0410403144268a003c1a2300030a100722101c0f00d50464006844d20399000034100700054041001d40c500c000480d01910480d45004006a44034030070318407214007084000c1d0310f80304201e102050600b1a14807904400b1245807140f41e141006034060089a40040c0f24600c036081540c082e0960560301200c0c7c00140f49001802c0c0c803e6984507401891130000d43c420341c0f4000c81c009203002400204000300c0d40c001030701c0c0d991006041c201c406000e4980c0d07405411801c82202418803090101041d115080400400202c01000c1191480144212100b90070314001107034a4038458284441e0b0285805d00c0288440d907264020007004a2070600d08030b910300000c000c004000740c0c0c2d90704007946c400d1035421040e007061000400c06c400b0410440f403c58500164203a009092a0030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 522359658 1250 522358408 522358471
    0x20c030405044203120e01020c0102010e0618010207080408150a09020d0201030e03041509030210020706210212180717030d0b040e0a050303092b05031b03 68
    0x16011580c200b203074070484080e10f901d80a286a811100c1507512541001641030b91100840d409900c5010340e40c03548500030000308505041034014068015503240310742c414003800c03c11031244400342c41e0b1525104e2016200c40c01e110380200265400740082c5001c02d9441014100401801020b4440f03400c844021402c412001407580c8041490b01c40c0c1e40c005a243d0b0784002c11050380c2800d0015a080c0c0c441981840d5006030392040c03c003e10350070580381400e5440100001100d200f92425045c401280d20140d85590a500429000070384510007414004c420551301d6600c07012160300103140480b281d03600164800219450b502e40d1202c3d44843c681440204803c400900c440742c1281c0110f01c454011b151a442001c5410720011345558502c20700e603a035540030080341c3d0191812140017101030310b0102c2d01c4c0e400449041405005004d10000034aa10101e1001c83c103040d25860f90341030419100a80d0190000350101810590000d188116154407000079805801c11600c1c1d0400000c01c851b605803038010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 522360908 1250 522359658 522359681
    0x9060801060311090a141602100507050a05130506070c03050f0f03030606091c1a0108010606020a0b150a0807050406050105070b0412140d0203010515090a050105030712020c03040504 80
    0x240c18002c00204038000318242d6900022161800c40340c40e46400e043c090900c40040e10b945004600501c2500c2136840c92200c4042c42035000e0360160030f5600f000d0310481790101c40c1e483c0440c40403c42c5504040c03181004044a8038909002c40c48142c030749000c070b16250484801191140c0403a801031042c0201004101051a1a90300030613149070507214007600c0f80005082103004002c003051580d699500d06400b520064a80140d6640c903440c5400c1a0021040c0c45c010118249092000403440c294117000d4001a6103003500140480000b555400c1030307620008240352814911115040c2c041c0c0c2e1140840c1d0010200000208501c0c6e003000300300411904a1781c415414800c04220000010700d54980040e40213811000401144070031100541e02d9601e160394580d41d54600051a0190100701c0d409581a1001a5401c213120310101810031460300c01d50201c6540015031480030012076100d07000a55100d1701c1440c0420039440716007216400c0c2c3c0c101c04803080b001d800124090140e800e051040c05c14015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 522362158 1250 522360908 522360911
    0x41706010501120903091809060207060f1803020703080703170718060203070209180316050d02060f13140c030a0602041404090c0311061b010510080706021b040e011509060801 77
    0x8420f40d8014001421b00d2140340300b082c20960200310f946400358400c040e0075030010415540c900311031428100070000050f00f15110b5181c0f0107080303859240711605a403d50350580091101c0d600f541c4499450b034014100803020013110080a04541d4000c001c850300401c180e417500040084140800001c0200c5900702d030003150720610003030340965035400f040394003e001030711100c2c0410f03150410282140308020200e0080c035001e2507480c00f00f010000f006030445c021942a610b40e511100ca044007404400e490000182c07906140580104120b03440c01c11403c00303894203d6180c0c400ca90f01107400d24000d42c1b001d440041d804981040100700d03041040c2d180c0345040794104500000780e90b49034055001800007802503040c41441c03d1250700c40c1400c0b10100070101072462450102000315030701a160485a04c4621101000005404040041d0803001d80b449a00a0200c0b0240081040007131200c401620303911617152040060510f07020b1281e044001100380400703d401d0300b40004101900d10981c000c0041c0d1703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 522363408 1250 522362158 522362171
    0x302010e01112512080f0601030c0c02100207081606230a1b020a030b0109201917040308061905030c010c0321020936090304170601050112 61
    0x5220040f41c0400512801100c0050003448030304114100c1820000c2074019141c002d10b403410307004035285128030400400e1405694882d03004400b99031801c140b01001c150a504c2e001c3c014a0800e83c0081031040c82c0c81103a110503607070008035140c84540021000840403200c030901c600da52000882c0e8450500344007103a42800b000304161400e1084540700c0c41084142071042d540f845240380080307040c64000309a1403c45440f800c00c001d1402081c491151420315040388400d1051441c094507000b4000c541c44242002580f420724030b1017004036034030b10f0100f2006009500303003a18400d0200740154041d0342c89586034a0105c0c24400c2d0745010814000d10781809600400483d90b00181501e070507602031a200d41005034034236003507608071002241740c00307488000048622404200d50103010f020300300320740c81400c8560410025207045032103c509541c2c180703541c40095a4064145a080d008604070b006c69182598481c40c104000308860506803540e00039600400403513a00280320105164170745c40400c0703603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 522364658 1250 522363408 522363431
    0x3181203070c03120504050d120b2107050613170304230607080705010902211c02030c0303010905010501120e1903030f060902070b1015030b27040302010e01 69
    0x124000108094108101c0c4110b010400d0b206020301c1035060040b600c00d02ca90700b01850700340c1d2100e078000e2030000001c2d91012060303443d80b0180540c003810b03200a0907480c810196038007500c01100210582c501c1502c01c00c00006650749600004082070800e905002e005242400c8009402d00c42c04081d01a8540c402c3c00b052203058290418811030302c506220001c00c220452020803c140034040d4080c043c00307004503050082c04010741107201480d10071503004603031400002c5011400328648151020a0f440040e4840b1080041800f0781c1203144140120303803d010f44801058659482604030700c019680342c0004011658200110155a00400c6802d00c110150981129940c0f04841c280385448023009542c0001c3c580250300c171441c40c0c0362055080c84100c2d20360921074040c1d80f1144040760705062180000b41c1c1e10040004000507a8446c00505a00e0119060700b02e001d840c00c20300c5580d101030220081c00070b03594902001094038040c00701c40d68480c542414080e003101c3c54002c4449469051140000a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 522365908 1250 522364658 522364693
    0xc03010503190204090b0a020c0d080915060a2d1d04060c180b09010210090c06140d0c12050703050114100908060c1c090323071203020318 61
    0xb2000b00c82c0d840248140702900008005d0030740408040d000184903010300c81c0c0110341d50010400018881e084480e42d9541d020210303a0a403040301c000136541c2241110480a80d1074054103504540c00511082e002510340d05401d80300a0300c400400b00c00b07802d42c40c05101c5900320800c010020140806140c00c00084000b50014000000740010407056681d0b010506850140d0468940751810b4110420b0315a16041c1003190380d408011034038090711641034480e00c642c841d40651201e20350701141d04400c49103465410b90f060602c1c1184801c841a060240e002c1c02100e43c030030312200c045a83c1d590004211116240f608640b0094102010142090014030007001400320003031441c64240d032040c000142d4004112440300082e0460075907401500705203e82c4140302c8014106a00328a16a101412034040e0510104c8041180040205450219607030003082164004c009000d160b03001d6a140c50b01540d40c035106221101061008207030f010060140e03020040003e007482c104407000a0108110480e500340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 522367158 1250 522365908 522365923
    0x7032303130914101d3616180b1f020304060806180105011b02040905010e1c080a02030402040605120601090b10080c0f0408070f36090203011509050901050c03010503 73
    0x5c0c0c1d068528400309060381c01e0034101c03c240c60350142024045284c4c640384507107504601844020310f486048a25801c0b91245969101203034400c180a60b4514480401034000c3d00c1e490341700c40d82c41146003449021680d0214000f410881171075010715035641c01c04001801040002d0300c004e000d000c464100d05411100d401c1c2e0103054030000d0800304070101051240000b0003001d400000c0d0401c0c240303101d8400f008415000b000e188546002507035000c00c0b2200d003226140700c0c900da50f100051a00808100301902950046820500103400030a0003511800071a000344030b20403012100d544080010040c614042c40703914880d040031a2034901010218800900d0210041c2c0100f1010034001092002c80c10320808850040c11074009a5442c250342d012454400401403207000e104924010106401c0c94980c00905003144040302041043c102058543c4003d0810003001c070381640d603c0380b13a03100400c486c00e00940104103600d804200b03031030101000ba007034840141a4081c001e40500c01408156401703c1c00d138 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 522368408 1250 522367158 522367199
    0x1b23030a030309020a0b0f04090606080403120b0f0907050306040606030e03042102100c14030909010303080901090503160309090507050912030f03040609060507020703230313091410 80
    0x100f0141d946000086440070716900c948294240000d0100d805018103024004846843c3c00400410359510410f44400000710740c0140003445038908034040c3c0f400eaa2055198040242c008001481c200e008200350f103c0503a204004910048100807051a050003078074040c3c60310b803805108400720b0056840c2c0d04d00507170083c1c150381401e82404801d031000e6419581c00c1326030000c142d01c1e0404002071025001e07000f41203003640c02c90980c880780c1c0c1442100008403025058040d1001000760b217961822102c03c0b80c007401d1107209540300c2c0301680100d602080a80402c100010f070359080100a8500031b800000541d200300d000506001c100041d0980201c1580cbc1b03885002e8501d294040c0040344000c4c1540301d00d03801ca810302c0501005000a0203044d6100448052240c031040005880c2c04d441665200020321000703069407a003a002d20556901004443c400546150840c1e0034030040010107140c140e40c0b5003201d0521690780c060014030a6100c91100d17001b100404040380c01030b0500550491012800c0301d130 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 522369658 1250 522368408 522368411
    0x50c150324040603060203040219120212031306092603030c0a18060215090303061f0306050409050d1e020c010507110d03320306040507020a1b23030a0303 68
    0x41d599000c0c1204031108080300c0090040251035101d19082e002074000340c9060f8002c3c1c06e0666030701440030049007072a055400c070403548201d80c040fa0303007048041a403110034800d240c00305000458805103400340543c050045078803940320781030500c2074000301c0d10382c1422102e040607460421804c0c50080802104e0300188441074003596100030034016110341107694811784084410030b1000079083d9000c00c50f0301500070320302000100c9443d030443c540c1d941e00080e9401540001f130f0000581070f0580030800f82a507607040e410003060b06561a030010b002c503032850070140c5c1c40da000a0040c0c104240e0101414902103402091005403003810b0400954440c021981c1d41d0510a00091384403e018200005940c0a000102002c400c00a946401404140044036040c1499044501c100e426441540010002883c0c005e000313081d80e9441082002406000c0c06413400d601a001125021400b52a405107003900c4030b443d0403c00d245440301044160603040884c018000204201c00d0341960082000e01c0031903050710b0b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 522370908 1250 522369658 522369691
    0x606081609032904050106080d09030b0601030518011404050f010c080c0a140a0f020c090903070b10121208060a0b090d060605040606021b04020a1e0302160807050c1503 74
    0x54441e240e41c01108600191070854104005c20105400071001d0b1140ca03025503400b41c0d0841400d941c41445804001d000c80561400103813554400c0d80000d030b1007441c4200d141c2120310390380981821541c5a0365000c03180c421140c20042070140420542184404040007081046521640108001c60140c024002141d00050800040340300d2400c41e20084001d8059030798841c03410001504281c04000c401025000c2d1a60f410828549091a58450400c0d50061460301466603550000f08400074000c2892070009200070402d00c0c88d0400c020711840c444c1070a0107000ca5040c20240c0400c0d80180680d10a86103075200780702d6070090000351180d0746410385094001014510b00070016001c103400c443d40291a0000c0003030102e90014900510311001c6003c140654212030600c000d03440384404e004046207010420241442c1c0146008000184a00c1d0042c14503800d044102c5200c1964901603d100d02c010a8001c1030110500072a440807004a40301810781c222030040070140e0000404e00740c502d07103801c034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 522372158 1250 522370908 522370943
    0x20f12010b090126070b030c07083a060b040e06030f010c0e041d06070c0302120a0302040e0c2a0c093412050c04090f060608160903 58
    0x401c0074920540080402c0003542c1c6945118508022008405480d603040c3c2c1d00505882c0340209000d0190790603014040e00d1a541c1c810144050340c4030842c21621000c1c00c1269004e81c0c0401d0012a68134032101d407a440c52140350400d910a07500d851070344083c00c20320340841049560b90420803503003110301482c909581552902d001038204400d002c00394000e5401c0a10070381034154052103140003c07200301e8081042c0c2035000e410f58824900c40f088a4155401400070540c65401440c0154040d403083c4101c404210443d02403601c00d0704061114400700b1b80100f000e12050264030117550340210ba61000906040c2c0082c409480300706418010807080d01c083c00c122544110074402103824030f0003c0c01c8408241803011800382a41120503400050180a43d201031184020b811502d521a05d00d540e04103100c0000201000200400740140240403020440010713401d0182c041d801107284405400241c00f403130610050802e5000600309158040a00300c42d40d0341e6604644110b042c0c03a0402078101400030302a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 522373408 1250 522372158 522372161
    0xb06040e011418160809010e060606030a110d0207061d0c0405040219081f0902011e02010b0418020a140109230306040b160c020907050c0a0c0602100b0d020f1201 71
    0xc01c3d40b03010082d01c4601308019054000301102482e0415036404a4030b40c0c4240380142202c0035040090425000b6401283c014039181c00915046905210001070900311121180740b20791012424042c19038011464100344451840703480c0c1b240c018070602100f04480740c00f420340c0b81d050041c1035500c2140c0c5c4034040390554950b407030010011810180050407203500d9031025542e6155403500c0c400081802040704107205d5050003541e06175941a103601141c220050740000c0310150708000d0008642d81c1e03403130301e100d50b0703440c4d0103043d1040606141405004290340180311115103550010035140c0d86282c0030890b03990384029400100d03881ca403402c0c1c030121a07444040f03640e000e416a2840d454490300e4180014051120801c2c2d0003041c5400003e5403850402806075081c034100704010b0341c0100c40c13100190503507004900030003890a030441562000016680d0342080f0140c030350030007001a17200442480400486100d44900710b441101c0461420003d030b0b001515181c810703014140100e482314403a5179281001d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 522374658 1250 522373408 522373429
    0x504150306080d0903110f0f131b0503040201030c080105010e0103201b15061c0f1209322b12030b090402091b0715060602010b06040e0114 61
    0xb000c0d1072004100c410300401201c0745000030f40c0d10b49204c0041284a181040329100c2c50b5a025007400c020100c81800c0008170503d001d56134884503210040600e00054104641502c2685600d17403c0c0c41e030605000050407511128003444c140104403005100d10307a008100010020383c240b0303001c0760f4400040040711020500f050407280142020614181a0b0650782c091200300708a10304480340d041e01c01106100c541c0b000d880d21030f04103040e0260003130440003000b02c40d45c4481c020a1000b2440000f030340c40589860700700780c100b000600d8a80f02480000c54100d0340026000d07102028519400b0b80115507001540415219031181c40218541c1c545c442c4100c070102c081c1d40002241c0014a0082d003440c40d5503e00e500d83c49000245402110442450802c08003409030f0b8026001a07140c3c0e5516800410f04104101140c481010a00580c030000b109000e581550401e20740b40854000d2030044040c0c292000502500e210b01c07820f0006020001c0500076540c11100003800c1d035840369524401094a0140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 522375908 1250 522374658 522374669
    0xd02120c070201141204021e060d0b010e040b06090d03140f0c06010b2b0204090e0705091005180a0603140a02030606040204051e150310060207080a030504150306 71
    0x2281010400c030600c900001c0d10049000382c030b409400312208260030f819841072000035040006000041005030800a060341c10002002c4200202d541401c00003e115800247c1014095616000c0c40d50607035910400030700301031009171010700000f0002c1d400110355004500189004540c0c00030004107240c460503294400760003000e02a079484110f0803034914030717610901c0750013041d01c00d0300000176000b4070030b030110317580b040034001e012600401144500c001c44c000214a0015030350240804504252580703c4c8444440c800001002012b02c0c060600080c030100514030040d00031000700810007034032a80d10599103141e40460100e130b59a02c1c04042401804a40c001900040005060420a000000301d0240032802102202c1d1030359030398001c01044c0c0c450343c052030b904200c5900d50f2140740048001d0a4104200080100c13102413280184505150022101d071341904d829283c04005c0650148000c00281014001070410010b464a010b0410322407485000c40300001d030b21150000c00c1c0310345c3c0039001814 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 522377158 1250 522375908 522375937
    0x30f02040f0e101109220e030a052b1a0f04270c03120503150409080d0c09030602190909090b01031419051e0f06040b041707030309030f0c030905060d02 67
    0x40e4071b2451103851800400c0384610702031510a06c00b045840000075540075170655501c062424150510001c0c1d000d026087d00034000c0000d54002104854a000e8035040c20f45504000d40001550010860707074013400652580514074060032855007080c00e407003e10b15500400118200440e0600e4410182c900c3c17a40301802c900f00078040450955030000c021402112452518164003000804020840341d81003001898550100a95500c0c0502508945c98003401c90600b01c04866598480c0c1091341d0141c01c04010b140d040c1d0498802c110303008400f0001810303204030100548107450740d5007003440c03c0c10301000c0c1100407641c6880c0c040300c40400203c4051401340050080c1202580390466590f0350300700a0450490244044422040c00007429081d800c1800c80140300c1c0d41c9a43e1a070050400014105581a12240c0505030001140b9401030864074401d81c0d0000354116107043c0104440900f4100e40c04010541d0095000300341c0c02080d100582d0012a5055912001c000d00d0074000d100f200080300101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 522378408 1250 522377158 522377179
    0xb090a1e061803140d0f03050702060403120f0603120801060801181109040c031a0118170c0a060e0405060411030f09100c090503060a0903020d0311090901030f02040f0e101109 77
    0x102107606079494229031a240c200700040d034819815188e003256a40c0041e80810001808a4401d400070081000300c0d0400003580c08040303000c281038840d0b40d0030a540308443c0e0b65496034020381c003082040c0186038a2800004039418241c00d44580c0c05982a80d0f8292a101c421484032251164100c50403c100107004001c20346815101801624000040c1c001c200e040046200703055001d4104085480700003070100f22404d040402c0000700c45140c0c05400001d119a4084000710780f141401c1c000031707201d070381c90300c2c110060000c0820042d030b030380200203034091410900ca03030102d02c92000c10380f0303004409080b00c0003082d40c42441a61401c2458111404e9090404081d80ca00c00c4d0007902e0441034540c20b17016949207541d02001c240c150b404040c00240160311090900b0200ca200341d100044600e00c07848454541350309600042d012560230303002501d507602411200f078110314051041b80380100350700106022402100b0b00fa20380b61100f07081c145070702c5030701c03808030341c00c030303101400442d10790810080c14203808 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 522379658 1250 522378408 522378443
    0xa030f06141314120d0e070f03050a0501050109020a0f21020319050c130302210304260a0201050a23030f011d090c010c14070b090a1e061803 62
    0x2d55448100903602d003203010701c03e000106000308543c0400d40b00c8a0965103800341c0310000300c0c01045d00710340400c1d041c05181400316041c0c0f05070003a9402140100024000401a410400c0c2141e02c1a403002242c540b0400c40c44d803c041c0c2000311000855a03600b015a04844a401011200100011542542c0b0320000402c8441d04403641d40c011200a140c408001a948400c0400501d1050303810146440b901c0140030030051030320000f5015050350400841400400303941d0454919002900701000d5003a820140b11020b1001d07050038024a60ba40005000d000b113a1b40010704644070304c0325448200680002480c0c03807020140c00c00d120964444041a540e86006000246420350a014003243c5100c1d441104e58040031018210b40030b8070259000c3c0c40460400b81c01503540e0b441409045480c900c0ea0300c0d0044550b0750501c494801041c0c9501a02d9844190300108625003105400580101c1040d20303580c000741c01001d0654058941c42c2c00d050540145e0321010300030380d030142d41c002000081050f00700c450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 522380908 1250 522379658 522379681
    0x40207150e030a022401210b0406020703030c0c020a17031e03040201170c03060603040609050318030606060a0816030b1306090f06030308060d110a06080f0c04050a030f0614 76
    0x80040b541c2e030a83d49041c00f45400b1001c503143e24000c0190400c0403500511440c15002211042820b100201047c001d040d42e0b11103c1060045a050399601d5012a410060640502891000c0052440c05501031606a0300141503c0d2041c05a24602540c001c41050311803420001c0314079a00e80c6100103540c004051902c52210740c411070b002c0b40010650350405401503c1024a18090040303601c5140c2150307a40e034140001a00014000d5415588641d4180701280c81030008005044000110100c0807089c2130a140c540100a094a406040208800c1c89031740d80c03111649420884002895400210200d821006011a031150540c0185501c1c1c1410109005511180807030700856401e100a4048503882d40464140303110203008140c10000050080c545031244080051044c2001d00407000c078500803420504030b6400850128902509000ba1130032005400740d03000780881c0c4030601d05420203000c176910001901c001441540703820404001c1028179008504018903544034210646010002e000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 522382158 1250 522380908 522380917
    0x4120c03031808130602030a0903080c010b1e1e01090e0907030602120f060f010903080a450f0b0f0f0307050918070e01140c010603060506120615040207150e03 70
    0x2240500c004c0029a05c1d001000391003400e251600c0e1501e41900e03640341c1458641c4203c003c1402c6540c0c030010001c940d594550880c1003465031039480c3c106e1035481000e002e072409914001d040c81e041044041d14080ea8041c8801302510109540c1042c0c83e141d00101138904651900000c0441703001085650001003511450752003001c2e45100014a07407500d50901c83c0c54100285018005103180c2414000308140c00e008000000039482d05140f2208085802000c100700c103110507840014410031103141500d5507881140200c10a05218071461074883e811140b02440e100c0c01d0003528011a894400301c00d84016a5840002c802c0ea00d80c0e22311f0461401480380d400404c00e14894240d1252041c5583c51086000c0c0c0701e85800e44418141c8801d4000554192504811418041c4410040c829504c2400c0c06031200841c441c54020929041040030060b0b060020700109002c2d0344104100210b03802007200b0216602426540165900c0c41428404400c0c030580c2d0030416000e050020446034a00d0000090 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 522383408 1250 522382158 522382177
    0x1c1a0913050718151d0f0601050d09050c0f0f0a091805060403020627060705180607050a11030d02030406350907060912290c070c09020304120c03031808 67
    0x44d034030b41c4814010001501c06500019121030400000d0050441c0c40707070032600142e050500f182000e0900403400300707840c0c1c03029044840d40c11051444031242044021214a0f00c4101c92035006031a050010440d4011244030342e100160300d0307a480441d102488400104007903040802c0e124503107401d040182d130710081074540c90036072070792440007034101501d0090007482c00001c20013408643d1200442101d0030b8002c0c69542c09010700c0f81e0302e0348080d581c0b0341000b0a2014800c2001c0d20150b0580c2c244060175990003040140260407241e00141500c0d030100072103094983d40d00b0080c0030003400480711a119039902042036039a180c004e02d0700078440540d0484901c100a20310441c0c1101d41c40d03641c01c840d1074210380308880783e40b03a0141d14000040c2c03000c444c094038050807220070080c50840301c2d10302c00c05400c140c60508606000041a00c00d000c0300204074006040030b500e0543c5117080c141d81c0c01c4000051059090100b0100701c3e5102c08140c400c4d04010004468982c5c0440c0030285403c040ca0707a98444900b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 522384658 1250 522383408 522383441
    0x11a160305160b060a09050f13050313081b010e06071b0b03091c050405241e031905010f0b0304060b060d020c01060906030203030909070e04021c1a0913050718 70
    0x10121b045016462080c084030010401d80c0c0c0300c094482d460f030500ca1804840c01e0200f44000385101881c1b03c004002010074600501250a0716070b242040f808c0340080c26410081c42d1403100321651102c8049540c21948104482c1400d000a403c180f03e405554201e4a102e44001090009001c400902800c0b0300f03c1e0341d0714280114115001c01d5400340720300e204440e000100705400c409a011250b0411140c1c0452000003881c11014242c1903451b116002c05000c807880b000700500c2400d45e80d01c10b10000c95a145042007286506245c0703940103000d020303c00c005002030004006010800746400a42d02008041d0a0b29160021600d01801a4100b90100507066191080c001804c0303000380075013005c60f40c000e0041c618006a00c003c4c0070703803840c005020601f4801542c0359035020fa201d610043c0354116951801a24003901c040c1144103550700290b2903181d2082250320000b2070b541e403800031500300c100b00c01c01702d960303175034915010b0b04160341030b400070200c020901404d02850800d5001034500c0074200d2032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 522385908 1250 522384658 522384679
    0x170a08060a140f1c0311070603110f090105120109050118050f06010309030207080703032c0a060e0406120606030215041d06040b030a120305011a160305160b06 70
    0x78440c4160300c0380304032000c01d29a01c619a2803800c0481c0c1c0c602850101600d41c2040d01652400d59089000c0444200c2c001345e60740000d101030200622685015002e00d10b024000c60101041501d040c6c0200361400d8200b6030006404650341c1e0042c411190000d20700c05800f1065a590300710f000050500740b080050215400181510420740d51080a01c66032607071a902d0070985890004400401c00040e04805500c10000c01042c104010400980114401c0d03541360b00548200a80803140000e0202d1059810100401702e803040c0e03374503401c00c010fa0310b0f1440c2280800038000d000501a142540c05540c80003126406c0c4014803906c0d800910540703009580046462200e00c01500e001d00c21807080d10f915440d0520004000c005054107981c1020004002040c035809580c0000c2c00d06440344d03c02c6594989021840d4084c5406028150041c140501e0042d1400008051001c15100f03840c901464100c0c040800000c143c013680c08d030759040480c141170300101103051410340e58516083e114144039004100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 522387158 1250 522385908 522385921
    0x141e120403110f0316110a0b0315010e01090608041203020f04080604060b0a031e05010f0c02060405011b210f02130914150d0f141e03030103030215090703170a08 71
    0x5c44000d5401624803d1441015490304a40844001c0c006640314001800000d06a2800300c05540100030038400400d0280c4404000340c118241c0e09807035410b20000d00420031409401946040c0e1042d000905a10340341c1445070118000d20800c491720011060224010038505d100003941031059120701000c1241040003801c00c03020518520cc0140542c2c580454610726480104070013201070300c108000b103240d2409920352016140c1213607500c001030344000c0400c001d2010034000c10041d483c49010301e90240819030300085c461211a00010485118070300340181c031403001e0b48100c1e681d9035941811901c4031108002031108030094440d94140341c1c1000288a0b500105c03100e00c078040c0818500002c1180740e0041030000152002d0010b80b00300c9107501010000c0340d16010703810300310901c2d940941a200d0390701d9000400d41c010012400f13000d030b1041c801400083d800003507614010000c5850241d440c1ea41c01106481d0040d240c00051400c12004200181041064040c1c094202035443d109101e80c0c840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 522388408 1250 522387158 522387163
    0x51309021f0e030a080406050f04030519063608300c09091902070c1e090905030726040f0609090b030a020603060411070c09050601141e120403110f 65
    0x10304c000d800c41d030081104000070b0340101c0040c4030580d5aa007440d810f00d0795a8641c00d040a407520300404800c012101807400f000000c2c0309104a119605208803010040c0c1076081901c8018907421541c00522001300c9020b010491041d1200080d81341c1c0b086c10b80080d440802d4900a0240e0f01024034100d821022491a044440a0740c1044502030244500c5540e07864144910344d08141a841890f070b400c0240300041010f9110010141c642c1120f07058000c81c1c120302d1282441003590001449a01d00074200000078008011208226084040c0e03115442d250141c2c10243c2101803045019003400290004482c0c2c50803220504036040f03074403210303c1c5a40d51621b410a81da00c2005196150300070304000c2005160550285800c030f1030280001401604001036035071141e10803601039070044449241000340704400e01030360354040c8003880c04132241080c3d08c1880c0d074203000d40d410900d084800070b0b86c40001c0c0036041050398110b44207202c07001c2150809082c050300845440d8201983ca0195001c80c00016600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 522389658 1250 522388408 522388423
    0x7210e0402040b0c160602061315050a0605030c0409020607060b060c0a0f0302010506120a060518030c070504050919060e030f1c0c050a0f0e0f0a06112401051309021f0e03 75
    0x43e40123000c890742d680115404484441400302c0701c81049181c28584c500f12849070038895a40e0010004515040c10704261408040043c42c61040b4200842840140c4543d0180d0b07000580c04080440d11501d80c0c00000c90f01d000706484a4001d2061201440500c00180303c4081d01e06e0080c0c008019940301da10500001552103040200c05130310414401c40022083c3c0e02143d8498600503200320707402c00103d0361074150381c00510351034440e50207400c09205038a0184503590708411a10014103050845034184a10441002d00207080582c1e12000240c803882d0520803200104411009a03641c1d422225400005032400d0080b001c02614085480c1d901c24040c6085442548041e154020f07100038400c42183c0c020031559031243c0001178204244480d44403501d69201030b2016845444654180000042c9425502a1804c001d000494100c00480c1a80c20459041d40c200391001900d0f580d01070210760140c40b031218008d4010310891501001000f02c1080715940d0500c0e5960a203640b0301282c00c05568030b60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 522390908 1250 522389658 522389669
    0x5011101140f0417091e0a050405011518060c03110a0602040b0d3602010c12020d0f0c0305090103092306060321090409020109090f0218040207210e0402040b0c16 71
    0xc10010a40c400100c542c40d0394101b500c000e01c40c48629480d00c3c0414140e81007a440701101900d440c0e080350700281c0290643c0700c0a411403100388007042c641030000305880b800c0300010782446908280003c450800380407a00d14550828000c7d9a06e135a42d407401d905642c17044403c0441e4a24060f681000c240c4076254054500060b0003c0c0742e0104050080d140c2c0da040d01040407030512004401d41d500041c0a10302501c0d030303038083d0340190210260720003014010501c40400b04080200b2003031030300002508007094550040003840e002851005520b0458803040d0b114001196003080400d40072030551000030a98031620042e4103568a40c1c0411090070700681401c941407a100d1428820f140705410507500001606005241004006039216501c0b0201e40c0b0503103d8507092500000c50403984241140e4070030310400150740071454171150341c54500300c0c0403030312122804400c0c1500c0c16031030b5544100e104004d0f01400070300455545a0b11103034000399034400e00141899004920020030a24000421300c4112036 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 522392158 1250 522390908 522390919
    0xd0914030a020d060b0f0405010b0a0e0a0303080109020310080a0c090f0207080d0203090c091302030c0904050a0b090106150207030b07030908072603131a1005011101140f041709 78
    0x10a541d07122000b070a40105c0303031a002582e080070000702d9551030081c02d00800d03501d110242d485110180060181d41c0703078500725008000421003000006c1c0d201025604440e80700070016140d4803079030304403802d001c00f56016078901d2243d42450401d03c00c000381a02c040740c0c0030000821101d01d1b0b42004600b0703070141c410007508200b01840003c2c226901a001968004519019646601d490708000b07001c01c0c100313036101a03030210740f01d8802c000c500f400c0000980201e000c6071000b4a51601c0d41d5596038440001c1e80c020000c010742d00100e415441c0c00d401280c0641003021440501072030281009594003101d01c8140c0d40307032461102040f6114020f100d1500582d81000c0700514250240e158044a0204c18003000d00b140c00031a0100d51212064020398000c20f015404a0410307151070030407a41035407092041110050141c42480502045068000101c400c2804c10700c0d07000002e4a01d89004100030f4848d4208010180d0400190300c00c001c3ca16441948100118000c00d05110514002c9000300d1143c140c004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 522393408 1250 522392158 522392179
    0x8070902070c0b120117011116170c0d03050a061202090c0906180f10020d030e03040305063d050103020f130e0712020c0a1704080d0914030a02 63
    0x9409900180806800384411981241d40e449505049501c890605070b0711414000041c8032603058188011840101003009010000e00306134072644ca8850b0f03060140e80c501403e2010410000301e041c00603449079104110350340f2140e400d180c081d280d88100242c040004d140200290020503e44140340c01d03103400b50451100c00a05a00b4081b0004000e4200d941000c01800840086d40e20540281340101580507a0350100613104240310500c3c0c20301c075682e445806606280c141c1d580d40021080481c06841c40c001c5242c10b03a400850381103104581020344140030740c2c1e0420003d92601c4c0c202210126030082101c2c1407a0003038068501001d0310507180c081d0300000e2174003004103602c40d0b00079000c0ca06c80f49516031b107080c80007941d603110038400d03611440c03003441ca04007040f40d000d030855488940070220606c15854054282400c6403180601180140f90514080c0710041482c80b00c030941e809418000200c56074048500000b42499050344078071030000c170a001851a4601300861602c0c04030341d0144c405c0262 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 522394658 1250 522393408 522393419
    0x8070207050102070b09100203040e010311040c05030f0609070c021207061e09060f03112701030b030a0602031f03030306050f01030c0e010f12090309090f02030408030c031317220807 80
    0x4101c7c54482c4104620080c44003240441c1c03400d0703501d80210700c41d50200441f444000c00380010358003001003510501c0740601c1003007aa01c2c9524840c5174421011035404000365203000c002e8841d5034803560065044013886104010170240010318074240d42c43e548440c02c18a140600d00c00f161404401c1900010313041c07400404c0703180c1c010b43c581c001d002014100814200c1a01601c0360b0aa00268404160403812100b41001c03441c64011554a0070000c0c0303014030951100e800427913600e50344104000d001e19030010000d0f50750411003542070103684100040d00003c80d0b4030304005015020300d00070300c0d104000c40503d46110b503000b0312030342024084a8407000140c0e0ba0078401907035003168060310300b010702c0484126000603031440e108914101d8400e45841202c0c605008024044500d001c880300c400902c10400d0101165140090700e0340400440c3c046990f80d51004452015044052802400e100c4d40c0240342e01d002880202808403481704030b000e89414241a04030040c0d1703c10a100b054600c1e0401e4005016 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 522395908 1250 522394658 522394669
    0x10b0906160303110703021509030306031203190e0d030513110418120201020c0601050a03171305030d050d0507301407020703050d020d0e091906030308070207050102070b09 76
    0xb8000d050015004200100605581e84a03501c100c0040e001035030203800300721484001542007407083e030065056180010111380e980c2801c41c0440140500400003908192620300b10f1003151401050a00c241700010324038954130159003c8110101e802c220003d0700c8071482c4200242d0307031070f00030900303c920b05101418000105201040c0700780645406100b803022404102c58035102c080c2c0c1e5800140d03222a030403000d41c14010306802c040c3c80340d03218803030400120300c010301802e036a4500304442568070340707503402c48441e002c4c056030080c2d405000f00c81c020916a40c100e4080d103120584600c0a00c4156a2800101d07000c0d2104450030362180c00c840c9144201c010400040594005c0700203001034481c10150b00507207c228101d1b041401640701c640c05008000003444072122a01d1729000804628035118400340012002030295809001d1480001e65446401c100b03117101041804030800c0415280d0400820a400446010303015100302000001c1a510000d040f07400c690004814078101b25043c801c200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 522397158 1250 522395908 522395947
    0x130e01121505180105151018030318091b09050f18072d14130506090d020d0302071e0806041704261002122703040e0a05010b0906 57
    0x400280080c00f451000700c000344a118080c1c0b074a85115541d48000c40304008600124060b00e00070000c1558103894100740f10b00040007500d500d0306041023007101003441400621740603448528000d052400c0702002940e68441170700030038483c0d510314110b291a5410b214031072444480e01a08940301c4000d2000c1d400103030321220b800070300390b2611003903504409845c880d450a040c0c6020003030724811514a400306401c52544080801621003c90a207060040e1982030503510344a00c4e0f019202c0020412904d50702c51900740301082d03000700078009111550034029501e0a050042c14003404090007401d100c2e451081640c0c3c02c59903d08001c107031684c1c980c0e0303c080748499444032182170480203006c00b0502880d641f1114883c9500c102140d01152864a89070307103400c1c071411220003580d00c10012400401500c003ca1903111420031034003c0b0001c003802c502111503d0305444800300303020200340441d00b603500b28103080c0506210541030207142d072200e85054441c070441c000b403039102c80204a2000001d40b0860b114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 522398408 1250 522397158 522397171
    0xa1d0102010f02070803100e13031b06020f0306040b060c0703020d020d0203070303080f160804020f0112020d0b0111010b03150c0904060b0715060f09150b130e01121505 74
    0x8140e0041c2c0755110826608500001c0328a92008002c00ca90760041404a000805a60392105542e007801c45064180c003000c0c807000740030490640c0040342d212601d48006c00031250702c48803c56032101d200e405c1c2241500241e448a1103581400c80103102d174500407050303891064031000549031540c40d40e400c0008004c5100307022600091030085090169906200c0c00c8003e50080c0c4a003049442d12104100d00b50100900700c0c1c81c00c8200340d41c20104039605c9044207500590540d94035140000500c0160f450810f205e240800407030000841c0620340d22140c00c10b420550080e01c43c1045900850300142c243d440d04059a07030103501070068041451100043c0c00e8000c41c20300401d0b4507141000700402c00340e4405030040c0c1c00354100050300e002080f02040c0c07202c01070a08a881003042c203040102404911101e1311901c005191205001d00100d01034032078007002045010300b00f40e91002d046025903003240d81d910031484160500303000003640720030440c00c8500c400c0c0e110000b90301440110358580010b24018203071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 522399658 1250 522398408 522398411
    0x90409050d0801080d14070206180909010b0f0a2405071403071a06100f0509030f0a03080f01060e311a0f0f0609040b06040f14060a1d010201 62
    0x800400d0060210101884035a0b68500d919070400b96810b1401c0d108100b420f0403c203070355034030000b0414844152107907181e04032012551149016400684800302101c0c0c141d001a039002841180c0c001540f01ca02c28010540e401c1448500007010009854050310806100034555840b14183d42d144030200c08481c50b00742800342c00e001c415250a085003082400c12890356100241d1101440024594264049903600603c0540e00d403550101e900d0351184580c440501103070304458181c1c640514140c848400003c0c048130589601a08640d0395407141c408158081414480458400203403403251030f041c1d1f841921046144106501440110f15110f8001c030500841458810f00c43c100f5000c074442680110140440d0703415a40c001e1144e84140710440d0380c46451405800d88054072a004202c40c4880d044030780544a800c460302003400751088841540c0d000200080100310110740717021101c2618802811600401e0707107002805103d210724481d10011aa418050b00c1000a8605000307210080c180300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 522400908 1250 522399658 522399671
    0x4020714210a08360d0201061202030c010e01091205060a0b060910120f0c180501030c0c02150409050c0a0801094109010209180f0408070c03021003060302011d060409020904 76
    0x4111441c91319100e0018490b0810064000a29824010f4501400d4100b10703910104d81a940041e0f5030350842040709060021900300300e80e59a000340d031044e0040107203050719403041390503141c0662611811183d50303a0383d92900c4901d0295003032050644400340006400140140750a82c410360342031003060100007405072680d59002e02c1090310b000706c2c0c046042035128802c038003107035801c2081e040c103032508410304042c504552580c001d80e002040c60446501600d1007031600b14080c0074510b0034400d941100c0502070802061144001800000b0050564150b50303899199813039401d413000307880700c1c080d48820105800c00c90848403004804240c9541d00089050031803141c0e001c0e60381c0d1480c03030101c0390000c843e540030403000c0507410056900c0304905001202d18030f091410400d09052014007400140000c2e80210f00c2c0c404000b004480080515001028020030341c0c03140e20020f01604540c0412400101c41504a03650b0744119900700d03200700030040c41030342441d0420001000039000f4900c0160b005d9110036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 522402158 1250 522400908 522400981
    0x913060e0408300906091203180111070c0f0906030201020c0909010b090103080306150913180503040306061a070b041515080d02070b0c03090405040204020714210a08 73
    0x1041518400e40100c0406510300d81107070b1083c200b9174020401010782d00511145111210350700e00f101d0f0f100b8503044602c250443d00c40f001600400401c01047c503e400d0014651085c0040409810100e0b0340402c003840c100c0d61201285010b40342035100090160740503401d0342c0752528048240303503805100c60b40001440c81c002e0303000948880d070a910964004000006101c414203002c42d445160340f85c084c16852030070f822603000c0b40e1620508404203440380c8c0c0d1500400e10041d0792140880c640d640003003c0344e8a0315100d06154005206c14450000848518911820700c031100a060ba4080c40c0c02100001c0e0741e9940f81c641080498800b02d6003220341d0703921a440102000c051804a0281440070010211507000d440049d01d41041d541102c82040020b00c403903101c54030008201c0300e4950058602081d00d444900c0898068018524000e0801540410b80d2b00c1040000602c0700c1c13400c2e00300c40703580e1100b0381580c1514130520442400900103040c071000680400c200d0b103c0d10a02d14000d8098110a40c03600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 522403408 1250 522402158 522402217
    0x80a030e0d080d0515010507030e06090105070b01172e0b0415030b0f0f040c060c05030f070311060f10030807022407170a2718020913060e0408 63
    0x143d00901100c1d54400c01d11410301151508142c44503001c1c00c180303160801310740303000c0c1c92012996801d0740304101c0003440c0440d031b03441042510050303984440542041e5840c1c219440a4115a5222100600c100080200030711108501c0140074411481080c8026007030300d1221001c4c00003c90003641050719550702c054103540c040035030300003180210103c1e40c46081207030454900d440d0107072100c410a8041c2040c000030481100d150b008442203400c20240d1a002490a10b085010380c0703604c41502003020400506168201d003090081801c1907080c1d03030781c039a261610700b102072006690050340c60903070b00302c00d00c00201554010a442400100000740080e00900c030602c0b090001c1481040c0c90b9400f2403850b041008400c0312111000240c070040b410801e02020013454000d81d030300b00c211707108080500c44505407103010b07800001c2c200ca180c41c0880b410094072000087c1d800038446500401c2c040a040462024900c2204140d60140320644025105d944460b20f00e03401c0707101060380c80ae45003006141c044812 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 522404658 1250 522403408 522403417
    0x609040b0a12110303090f0d03020c03010903050702011101050702101112010b091003020903030304060b010c050f0d0f031803030e1905010605090c03040b0a0c0512010f0519080a030e0d08 82
    0x1080c07902c2000030351603d04800e030ba88001031924000c2c0d00c00c0c0215107159030b0b5841c40081400341a42d141c08501c081d0f040c12460301000e606019090b5180c04813050916a20100a10b5218001c2e00c52101407002c441c103550886804450710001a007020035070300110001a04941304025080300c0791424035a104840c0100b8401c20313801442c030f1010000d21110241460030794820001c1c1c1c81d040c210300b0544a42c0c0820f07224803005100601c119500c04240b4a582c0c0502100da2005400008030341610740707100074666032956411042300c0825140d66290100e54807030300540030421402d040c2412240c1441c0d4080e00600f684a0b080040303070180050074030151200e5480340305058011030010848038580010b00c08400701c050f00c1c00d5032012003001084042040a41da15070040000000011110704491003200ca50042d40c03035101d14a24004000582003c14001c3c0c841510070444607c01c5e50b0384540c030340b64102c852504c9000701703542100148001090084048941001c1d0140248440ca8001d540c2c2e0b00880c3d11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 522405908 1250 522404658 522404669
    0x40801060906051002030c06010b03040602070602030411010905030c01171e04050c010e0901141e12100513030c110415030b0a05100b040b0d0b09130521090609040b0a 73
    0x2d0720001000a442c000038420041906030003d145084034a561460300c5d100b050140703030040c2c00000042006c2000c1541102c14003500410211f440703082c03a1904994000250a4542c00903072401008141813401280c031480280d01610351b40091076400108420500c8010700c1d01d00081448120180b52281000c00c1034425403040c0c0c040c01d10040307400c001401c44080d07441d025028094140c0140044043c0c44510f050605040300c80e003285c980f102c0003d11101006840c10340d0880207810074107030552000901c0104014103108140038130f903100741e104080d802101c00b014000500a42400c0042000c20714231070800b42c0050000b01c0c000f02c10041e0746800200070307031003110120301c50310801c00c40030031610682e60024003800100030b282d4a001002e0700140114054244141c200080380300100e00c0c60b9101c2e45820742c0180102c41e00e0719000c007101280042c90b01060340c9034091100e00010100c4622148c1708440da030703d00000c0c01c0401420911030550481c0702601d4200e5900c3d40182115030754614000018403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 522407158 1250 522405908 522405911
    0xc0f04020d1d150105100e0d050d03090b0906040203060c0c070b04030305030a140411120102090a030804031202030c0a0b090c090406051f030b070c02240301030611070c1502030408010609 82
    0x2110380212403620894810b000121051880140305c560784800d0b03c2042c0380728505d01030702c1c00b600150020303090014a520041151213681c0140d8003994142d000032904d41d009600402041d034484000ca0f84440c01114020343c90b40111001840425044019106014201d27080b144402d07102c4028440f1540700d0303041500483c40c04010400035090602a120b01e100d107500104400e41001d540f8108200c201e0640c80744181c00b030a180701d4205101f54140c07101c4000c010600c181c05170b0f07607003005505c692241c00141c030012560039021116038000421102d0020b9040c00031320311007400e620380d4840e8400c0a03144000d180120f84c0d4001c0c0d242d503448642401140105000a490b0074440c0f40d990000124101c140d0560740503820810124a030b034045143c0c0144a41420b40c0d44600030710004807000154000c0c02899034100180480e8000c0d82c0c3c0c091070503a4461031040010000c000a848424012000f00919440b0744400a02041400074032601404e80c940c01142d0406495002c004d00f9568950009510369 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 522408408 1250 522407158 522407201
    0x201200601060c0c0915030221011a040b01020607050910030902031606030605150d022506061a07050309010309080c0d02160f080322030602030411040509010e0c0f04020d 75
    0x4143c1c908003400a2042c600300f000144011000f1b2000822a4031001e44100c00d480c680740c9400b00302441a0f0b90205142c0c000300207041400c0d01c15403240b048058042d014615110908d07055500004a56000306070f0380c2c58580c10300881320100102101d80c4140e084c201511124200010389007041100713243c1c003944010b501e1290030720740c0050484015034002d512488000b610f201c56000860115002e03079004c1680583d48246c00d902918140c690056101d589941081c03041040c44202e03402203082e94a8010151a04d4000a032040040d0055140241c040d07001001120803660082d407044580502c10700380c01d420b1542031951710b8100100c0c102c0c1e15016801490384040200d9003160050050328a042d08005613506040d00c0650381c0c000d4101c000b0b08041070b03c10210030900c0d1116824029680041c0566407480c00380780c441d40d880c809030800750040d41400d010070003030441030003080c40b803100040c010040c02800310b040220b0400d80d41c10164100707600308290b020b00c000c0c1d4025802000105000c81348407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 522409658 1250 522408408 522408413
    0x90f0e0105162f06070203070317070e010302090f130c091a030103020910080109121d091620011b050703170a1b030f060b03010308070201200601060c 66
    0xa4400042c44019030720486421035a01d150030120360072811403c42e102e0007952100f1000190070340802c0c18405218400c1c1c10800000c0c5900100a01c000381c807940e60318088040d510141c20380d410064030410085401c1c0c115075030107548030354060701205070028260070307441c0784d100c02041401d07801c001d20911007a20340d4407000d0040d41001d0207400500b109000800e420381001c5100442c2d01060000038404c965041c0414256840b04402d440a000a54000c01c10001c2c140f0700f000d5115030070b90242010494056008058040104614855107005005015280c3d0f81c00c6c1c04405c4456180201d0060158030f195088079002030450003a4001c0c030f0303003000141000c3c140c801520000e11800d400401c002e41049607000103540031403040b400002503450f9811075180ca45046000c0c00301000402c0040d54a003a23603188085d415000000b103840c1e03d901c01c1142c25224420001144024000501500e07070401ca0000154425003104d1000d881110f00700f50203019421908c0d003019030a0388034200094001080e2004e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 522410908 1250 522409658 522409661
    0x22060c1a090c04150816030213090503120c0a031103090604030f0c1401050703141b0702040e0613030e1005090d0201091505041d07080a0506030c030a080d11091309020307090f0e01 79
    0xe02d06c005942c0d00c418a00d1580001c1091102c2012041801d482da04442c040013030800030741b05107403048900d29a02e8a000340501d42581c10001000d00002d0524400c10490a504800c50b4001d4042801501302c540c1c0307648007590300d28003c0340310310200130785c000501c4045204204024000190400040b03017a04015000605560344081360101491529081c170081d8903181006111960315840c20307603102c0c100c0d400010000d00c40c01c081c0600340d004990400c80d20130540884481d04611945075030000062100c20b000b07132083e591440c000803031420000c03001649030081e00c50f10500e00c1407624400454403040ca050070745540c0a65400402e0022900740001c021003c11601491005040280a0710700001c0003010484e011780030300c4919965001040c03407174400f4006c241c2c10841c040e084035035080a500c0c02c68565400724151000d10380c5020b246640c0c50402d1004c9612606009200300000100869148010141800c0483e8103103d6a20006001002401000f0b2000410440058280c107810390030390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 522412158 1250 522410908 522410923
    0xd020907030e1f140a0506010207171f150602010b0a09150b0f04060230030403110102040f030516050102151306050c0301261207020a03020622060c1a090c041508 71
    0x5450501b0081002040e0b40e002841c01d0490340c0c0c0c1c290590031102410b6100c0d041c07005c4449205122224a040e4802c1030b01640c02103010000064506a09669918012822142c141900c1580025160400c000c131100da41c01290111048403040c0c2c1010b6070300d0a41c402554085e640590780f81d40c0c00b24003006a00c0d014800c0e0002c10070390070a11003d20350100c156240d80f1041c070106000003900070020406040c460598035005c07d02e100300031981d41d41c03a039566400600d01844101e8140c49004a200300102d011203902c0f04642041c4c004000c00c011403040243d1034400248202e50658120800c0800b01da1503000301e5002c1c50703c0804a03540ca50400d11101c2070b04501000ea15100700200344030070980b0344006146200c0305030f68100c1c507494604910000e04c02114036031000e9441103000c03980c1e808484880017818280c050401901811039a559410b940d81c098541e0f016000002c511070440e06038285d0301103070343d1142504065604111440000408403881c0c0c0c649075044502c0c6c90003e110b600f40410600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 522413408 1250 522412158 522412171
    0xf012f01140603070e010501050403120e030f060603011d030711120d03051b030f0711070306020304050610050307030b0a050c16030c0b070311070807020102010608060a0b030c0d020907030e1f14 85
    0x888244d810500040c2c07040c03080d882f00900002158074411265403182c03540e814041c800030251101219442c070742d1541c54009480f401d20035460881e605101d040016045162000140040d42c1018040d45590a0b42804114100d41002c13104c0f00203a140d88043c40304801c07071101e5850000d00350514480440c1040ca075500a50b003540010803c0c060500030f50710141c0e6100c00e0501d80340341001c01c0d0000d003034104401070340020500350020007031004104004c26174030b10640c0c841a41500165030b6200b09580c0d0354061201504940c0d501000c6007004d02107411059000000c3c20300c1c40d02d05883c1d501c4008220004c11400e41c0090f828107019020000a0298160819054176050181c409008140c4030b107840341c0000280214030000c0c0031002c59000390000c5000b0a60403041c2c0c2c40b68588001e112000d0621499034911030f005e000d042c101035103030400902d11b011b41c0140114007240d441d24400c0d00240850040050180f1819016141d01c1050b4442d41c1c106140c4030002080350b10802a1501c0d40300d4014064 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 522414658 1250 522413408 522413429
    0x301090506010c020603040f151d0c011403010603020703030b12010b0316062f0f0a050706030203040804030b040c03060c0f020606031b130b090a090b060f012f0114060307 75
    0x201c070140e030b01c001c00c2e65006030301310f002c8c104200c4061401d640c8140c0e1449140b1000707800e15445d80c100150040c1440b00402d0000306036202e007041e003001110b03400008154140111414030040c4140c606c00d40c0a0064113100b0b080000d00c040f80040080e100d950b003000d04d00d0a60b0f4480010300c0e000c0c1000c0c00100010721415032010221030810a02a107000a1040b5007442101c8040d10304c650150344085681c03444203d881540e0845c1450b644d07441d11001900025540c4d03105040700000d00903c6032085070b1080340c000d14424145400c40c2d6510314044005001a11070494400c00031002c01e226124154201e0069120000510b03001c0e0006400c2c403100070300711403007a089880101c2c4840b42c204e80d41e8007800c100701c0c0c481511003d19019600204069000903410003a400200891000e0980c445000300340642e40380c030a80c0d07035500304110500e42d140800c00c2c002188502d805210303420716040e24070000403041c180d80213000010492401c541c03407441d84c0c04200c9440e0f02800b0207810140000e001501c1c1002c503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 522415908 1250 522414658 522414677
    0x6030b060f0901051302070303140901051b0c03042303010609020a1106010b070611070b0f06010306090c1e03020c031305040c0807020d2003120103110d0201020a14070317030109050601 81
    0x1a040021076120170300058000980d01c0426100b6881002c400381c0100c031010707080c00c0200340035009100842f02c240c041128135840c58941136071f02081d50000001c000043d0318141c20301ca503d540b0300410141c0c0340240b038411500146180d80070700540c03003d040070721380040c0c4800545000030007428010342c1002c41500b1084c018400300861500b287c4440703800080c003080351407650881300a9842211001b402d42400070b03007400041007000b076056000da0703001d90301413016680365800781080740c441c800001c0105944010301c03594884400f19a040c2c0c00305905005050540d240191340c02c5a0042c100c5245403001201d047c070031458030303100d84c141100c2c480c60541020314100802030341c1c0c0c81e1032544038400d022042c07040c40703c1d0104908680300310442000550352102c015246480d0050310a0008880c2d003e2007288038601c5051643d900301d54642c050b401441100c010b0380303406608200c0140c204100d070180748400705c0031501d042c03001c052001581507003039503940c50000018211031016101c03078100000c284 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 522417158 1250 522415908 522415919
    0x100b090a030f0f050303070201020a080c091e0307080f011b03020703091a0412140d0f090303030f060f151409090a02090307030b0903040e090609031e0d06030b060f0901 74
    0xa540c419030707502080051040e001402e04403244001080024403521001081150701581074002d071800da00765445a4240f512004210442c9003c0c03504a6a000f003400003031040c4500d030019005041c040007600b0348015513200d56010381032040c110507520700340e0f4461904d104100304044240000f0b00427071070210708003001550002c004285c203110366280102030b46260b4454980140885004258611944d041030400d440c0000103002c0e0307444640400c3c02055072420110f4082c1c46449230b040703190303914490954203581c0d0a0b40181154410142596510f05c0c1c007045103c200751042c000340044000070614000b0f80f07000240031a4940c1d520790031000c0244000c0405440302071030503810030000c06002d83ca805130f22021a25004090b171014008804690510800300004030040094448900e610384590755203210541e9501c0b001e8641c0da8480c3d00030840d0240c0550080d40c1121806020000685000f045560b00ca0035101c040d003040e01c22441d0102401281d14182e44003200200064414038055032421 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 522418408 1250 522417158 522417169
    0xa1104020a270b1306030b10090512190b0105030f0c091302031c031a030312130507082a09040f03050c0313030f1406040f030c08160308100b09 63
    0x1031242c00d0004201212412400035121248000741650304100ca40f940f4030580041e40166680c416071011a1821176024982d0a080800340d403180c4980d111101403070702d050240071709007a0301038113058180151602011182014151161600d000322203280c4554104003c15042504804802905611028007402543c076404105507020300040e0301e1842c00305990001c01d080c200155650109004208599501d41e40c06a12044140361300c4104121254507040a02d6564419441d0302c0407182c14030f00002e40403a0500b201045242d201d502900c2440d5039a90440f447c1001d032202803001100c804614120f01d11840080c81005a0204c400b50780904058a0302000510701d01000703410420f00142102c1e017171100b0802c4800c00c05410b403040a40940d07a09040d200f07010414400c88240503548181000c020b00052614080d64002e050004001e40315030f01a204503441c07080031160080207202d0704140441410707828080c0c80c0a80c98488245c50529003035000c50605403c02840d0440611004941e51a030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 522419658 1250 522418408 522418427
    0x91206011d060120060a18030203090405060429100801031a091f090213020301051516020d06050a151d1504020c0a050c0105070f0204050a090506090a1104020a 70
    0x10444096040d02c4070001200e100b01d112904100081c000c41e042048020f001910910034034001008111641c541201c069000d00084405401640b05004a51851a0a038030507500300a0003000010b000c5080100c0038001c060f07185503103d440c00d41c10003074011801d21540c404050740c03d91900d0f440545c11583d5416080e403204500c0c0c00e040c00e001000071414101040410304a04001040c00c3d18002100880c40103084003002c203d029514401d1900740301401c900071349040c1ea000802078040c42103c041180d910390454001c11070040d805110100160b00c1d8281c06441d014060035010400703242000c03050080d12030107492500028041e902c01c01c4030640002c2c0c40307002908550b00c90281506c8011010850010803110710fa0701600c00214840d484000003020a103061007803040d80c60490078080155040e0082040142c222403520348cd00d0014909130348010f521200903a07000405540303980b192072911070100c80c85d18090b0b1080da00c810501075469195800030400b21815440c05040000040c5404107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 522420908 1250 522419658 522419699
    0x6060b09061c0e0f0309210d2a061a100503060103020a0e120607080709060e040905030d0f02250507050418200906030f060415060305060c09120601 65
    0x15000300c0410401e080d046600c11101e00e1044a150800143d0304031784070b0340109601c610911200c2c3c661a044a055110880f0281c0110040c0983d03441c0010103490122080d0a12040d0ba2000f1100d191b558000c40048691280601c100042e003018241c50035034140182d800c207074400c82480805030303000e9510104407070b8049403c2c07802503140d4100745400d58180c030000d03400c1035021300d40724032080d0341c0d0304005402407084595540f100c50544803440c0617212500240507550000e0300c403070701900c45c0b8100354218204080c801c1c8212031414119600041c119008014480e0072181c0000340c2c00d0100c80035504144100c0704504808559040360307902c066503004d0710b12840307002d0f41c0c907901c1c0350003481901e2030300c0d00765a60880c00096075800c0d00b80f00e0401102407804410703c203005840214142c1d040c001003000001c03445000404450b200e644902000d54600c601180e01c0700e84841c0e02100188040c8a210f000d022000c0b093b03034469804004002c140001540024030700d030301441c0108404e01850380c0d0703030a9142 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 522422158 1250 522420908 522420937
    0xb07020601032904030e0310020c06060a061b0204021e130e070302120f060a0503060403030203061009180e070f0902070b010e10120305091e0102070e15060f040f1206060b0906 77
    0x241e44c03010a0500c00420949234002d4401f03c0e00b180002d6000c1186031251500301d80c8410f145880300020f42d2440f040e000403010306054400440014101a030040c030082c1f03500503440581d818005603515141e40f140320850700448400f0707010002182d00c8005590004032504055081c401e0b06502000404c00040101064450f40b101082854540b0310303002000d014050290740440c50a4100580654811303240180900c01d64041007003054469800c401c240c490120340d13441c85000703008404005c2d105032070f64a030560090440000f00001441400c0c0c0040904400140e02e40e07906062100018405902c90401d59900308200300031f9000d11001141a039186c420310249401580c00c04440d14001d01c029130b42c02c00c0e0600c0b038480704d0885480104000d40d2090382150003264803a02d0419442d1f42c00da0b0811380041c080255042d441c5080300c040c0114418841c105801e043e90351982c888164071990080ca41c990300a42c40909000e01800303014080c0c00380c2e01803503160003540c80100b80d030392107400c00072156403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 522423408 1250 522422158 522422177
    0x28020c030628240f03210507080c0f0d020708010b040506060f0c01090803040b25051b0a0804030b07200604061107020a1518140603040f0b0702060103290403 69
    0x142481266140040d80d50942c54443c140c131030424508094142c0010b80d0768600c51100c1c00e4800c69410101010b009680d42c401d07080c20010390790804250454075440419010b040002d200b03007d41000540880062980201669450306d5455400c40c0c5580c40410b0041d2b0400f810042d0a498400440d10b800711641c22142c0e031a4058400316006108604008000c100700006000521021015240c0030f40c5201503003a2203040406e076403411002070960904080b03603007404841c041d505001107034003603600030b0000e45444490580d5402c4880c1d1140c2c0044480c036101c801840095a440011200c005007031701c441000701600c2c04050380d91450003c000070500c540759040c13201d07601c1c282e10664070030b540d001c1c11030b6103041e841c0e5101c0c4800c1d0a1012a400004403020030004c02c12101810b07010890f144141c4000401540c1030074003046030301c020011340c0e91804099801c80081c500300005071091101e0b0380600f06d5541549080c002201070458a2942506898440c0c3d02403801203400c280c116600d810841501c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 522424658 1250 522423408 522423431
    0x606020f0c060a18031109070e0a09050702030d091211061308030c090409030306030219050603040b06040915050115050307081618060c06050f1b28020c030628 70
    0xe0b1021a80c1c014074440444c0c4001080100c60b0b051654021012120500c0d0741d40c41000450f102c00306022940c1c0c1c4510b0100003003001428990005400c00000e01c19240f400c410211518151203880c402113072850010700d03459048903403200d05488901200380c080c0c4420b04101032a203800010102c40035104d86000400300341c0450348401141c104001c003805c00d002d84d517650b0901900401d5144000d9010380300141c1c9100c88490140da0103000d035500201983c0c10345e1202d8465820341c031802450680c12603039035101c00d801f140790315603560000c14030708a01080035810b000300b407a001d9911000400a101c0309106000f00700341c00102407613100c5051405c1c10041e1007841d4007101e50b03603500b140298404510361004035031140c5c01000e4010080c0a05420700103900c0b030003540c030603080d4211091001e00c0b606a6100c0404041c0c680245003504c1d409035041d00d0450000d00703010340c100d0192225005039014040e109910708041c0700b504c0d032040ca040c4120400c81c10b68004d00440c00782003d103c240055035603241290 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 522425908 1250 522424658 522424667
    0x3060a1517060709050a051e0a03020a03150e15040609020f12010c110703020d03181d04020102060f0907152a0c0b03090d050c010914010b040606020f0c060a 69
    0x20030416081061052001e0395540c0c460748261000c10004084640210701803c000211104607000a05401c400150300d83d0517150149196542c5688040d51010002c0540e90303c002500107107014802d90140170301440120001c880b6100010183d98200003015000006d0091410380d004d5005034000c500104a8400144205400300b80180d100c030000620507040b02c815401070200912030b132a800420505d10780c5a580e034550b548002503010a59446442c0001d200d1446655100380b04091909030540750060007401c1d03c40d15200e040da40d40c400003040150b6904216030f5800c080700c6521307900903003400e0781a641c850741c60740596080051541a000b26a0f4480d0540640084510443c150a81b41d0700c900703424424000003040e10f8031140c0c01c1020405100380000c503401100144010015004203040540e41500078125200f8a9540c5e1004200468055660080002c0501e000004e0072607501c401c1000307d460300e40000b01194040f40b040c00407003d0000c2d11340e07048001120025142c0c3e448040840303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 522427158 1250 522425908 522425951
    0x1407020727230105040c09051e010c06090b06090f1003170d020304050f060105121009140102030a1d070f0b09120a03020307060c080c0306040c1e120f090203060a 71
    0x6210002c005608265060740b101a18141c400848050040c5005c0303410032107100d0558050180d100204108596030940d0218452108401c1818070f422035110076140c950031a0f03803c0e0f0303043d00d90040440400c00c9501d009082140d01c0740c2d10301d118101d5424124202c1c2c1445044e0300004080d00b02c0ea440c408a2000707001c003594101d1480e04010342d42ca28103132501c1500c4140d843c00e456a28400d0000105503440c1005d0814180c5000b54003c0c101d80708003507407010241105240942d003c5410010703400c8080700a000030f40c4100110003010915040c1d003c24400300176580071240390250801c8200307016103c0d004450804540c080300c1d030342c1c0e103030407183c40021b495110b80b4085903480d00c41c4032030010070160040003070b14210740034071420032a403d007103c401c2e07802a10483d94404261b02c00c0001032001d1074594849040300840c0d24140d4545003c07410043c010b1088081010046078154240c52818007080c011702c520312680841c14402c64250360301090340e0f07072405400700828640341d4135141e4400450200e01e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 522428408 1250 522427158 522427181
    0x7051216110a0b0c0f0c010302090102060f250e030c01030c1d04020c0607020615010503151309320a02060a050313020301060b1902120a0309081209011407020727 71
    0x72a83c4005801d0b44e07a99a9601014075460346c00313406900c111070740c028400d6450849040e0054080c03669844900d101c3c1c400000d1860007841c20b0403e2642c50390407a0102200d0b200d022392101e01c0c0d0b10350304000b09464031003004540c504040c2000c0c5a550100c0e4001c115541007150002c00c1c19030b1010750000030700603000e5140c07048080e124280c10008a164000340c503902039100340980c1e0800404510045805203c01c80b549840b030900b1700301342d8009080010740074010a00c54000042d24820303541e12032404041d0003da060b58041c3c84e00d281601540c10b11201c1c00004222001407862a445034040f41542c003d40100c0c1043c010080700154100100c0003540301800d500500070098141c40344040001d6412011000080d0b241c14000006400c0c000103440c0d0740626030041c2c407402d007488050104c0242c42e2204080703441c443d09109035001d8040d00f460b001e02507490540007280d0003140d8011419070390710080001d01191300031030003007115009503560520180304145002e84914050b00041000e4002c0326200b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 522429658 1250 522428408 522428429
    0x17090f030d031b090312050a110604050c0a0b070b0a0e030c060906010314010510090209010e04050c03071e0e0d020609091503060106110c09220807051216110a 70
    0x2000c14954541d1001d06041c0c40c00500180001d450f44085500314014000100b0410400c2e041504290080b000f800308515245030440d6940d00c1c4550580c28004140d41c1240c3c15840082e1f58079403440c203090031001800800341124248507032915001c0c002e01001d0084119107654108030a40750300c0600c1240c0001000c44c0841c0c1380c90400b03c202a503207280c00d1100399202070b00380d4542080580180642d5005107880803001000508003c9000001d51204c104a030500c41c0828002001e03450314014548115030300c008443e02d82c80d00d004040c002900715604164849131480b0000b9480b90402c2032001c1c0c0003002c1d9055078a005051002c00c0c403a01c01c0b0328036036600c003011008020784101904502d00f0004010760590300942d99592058071118041642003441d074000f5084a0014203001c010950310582c103081045411640e503030492340b9800c0003d410749888600180703003000e11904002d0208a10b044a400c9403400b0500c0c18042001c0a0b10030b00200310007904011448103544200b2440060802440ea = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 522430908 1250 522429658 522429673
    0x1112030408060709080c0105070f11310c05120106080c040f0b0702130605030a0201180308300112060c11030f040504060f0506070b071419020609070317090f03 70
    0x240a80d0014410013156106e28035407400f81c1d52054045d558441e6124103510364034446aa1505501101750310403d0f00011102c403020042822030407042d54443d4042c1040c070b104140da811803400d4800d00024041845001c000c00d1a240c0c030030810a5045841034a00940740b40c541d01c00d0640548203da1110454841221021845036280700c0241502882200c41d074900344618407aa000340c882c60301c110b83d07058122240003400b40d40561425101240300b0034280c002d2036100c0d1350b400b4a0b41c00801100e080703046a03819074078203180c00c656030803080046100c204030b06615122022050400741e0703800402058490340d480408602500556902c10103d50540b6142d0300002155040d43e0010710840f0310950070108002400d124003400d1000340c80002d40440d29244864035070364a884d00c00382258040240005104504440c8480508840d010b0300050a1030704190745c0d070080c900000540542c51a810035042000000c2e44081503030082d17100380b40b4141d00c2d03d81003000107152032a4480466050b001b45a0f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 522432158 1250 522430908 522430921
    0xc01021303060b011808030d0c0302130e0601300c020c15130603051b07080408031225020a060e0a02130c02010509071505030406020714100b01020a111203040806 71
    0x4100c190200c40c283e03075003081503c5518817901c0c1d1060b18810500140c10801c101400480d00f600511461900390a01502c0c210b03581d9000c01c0c01d01041c0e885641d990b18410f00f803010130b603072000310360000a040500311120005524200c0c20303455070282d403c2ca4070641e81c50713605040c0c50080c81403003510302c1c2c020098455081d848901d080651b0100d0800c100c0091204c001041c014041e2144a010708038000f010b00a00240bc101a5125400300e002a0383d0a0720510000a03090700030030040000000000c0c24054074200000246900030515501c0400c00b122020a0030000b6800180d4092094005402040e000e161000f400d0070410164000303904003c55081072042d40c402c642100030302ca19180d00803c079603074806002d191a50070030b005031890140848107000040388100d02854025018540040c41d00000347c0d29114400507604c0340d1400d81d00702d1010141d0780c0f50180b1035060001e2003030018190005042e904e0a1084a101908900c11710b100c6050700c90403e001c000b580e02804c05071044540c1c80c103240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 522433408 1250 522432158 522432161
    0x212090a1203080a0e010c09120201200c151c1d0f0307140c01020a03030f0b040204090912090f05061c240605040e01140424031a090703080c0102130306 67
    0x201d411409441c05e18582d00e11510b4148940c0c042d50b409641c442501030304001c19404020080030341030f410841d100c0242e92003107030703560900c00407281807000910034080184180010503090117200444520f09000420380c04d9429000f01200303014015000a4200c400340c40099883c01000707903540c41c1d1050050308050078600100a2422900900340400103600081c42c2d190345004d031011060040c1c00a40070b010000c0e0098000103d620050b940108100b011000130400305d8000754044c0c94610389400d0280c3c14002c0010300580705030b88070700d003050340c0905200c40c0b040c800391103108880c050103000038003419103020000d40441003034501c5c04c14007070308418111b030301c480100d05070800e503002c4228040012054016000c4804032900c046503060181c0ca418005210348069507070103a046a2180030380031642110461403980b0703514060159220702d0450402030040b60349c600d041798043d100311040c00b548070030001d1104122980304441c10340d2000000001c50180c054110681c4078a020004007204000c0107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 522434658 1250 522433408 522433411
    0x80304061d090907170a0b0c030106031b05090f0310150510030e0a02060c011d1606020a08250f060219030b01080103030f020f0307060617030a0212090a120308 70
    0x10041c03207807441c1c01c0108001c4440740c1510103000d1a0f005140070480284110315448025a8040582d0350f024000d45845005c1c08049032039240c075140c00001032003041d8042c850920400600c0020980703030440d10740301404a110f40e0307540600c00d80a1003040302e0355580801c000035810550403001e0110240c0e94080d00103d204900a481c4103808100030259854400d01c264060091110000c25550289800780f00c0140e1018030020103039501c5690490003280344c0041031080c0c0000c0c000400800107103154080e807080c015040601113400c104c05c4000412000810344503c5102d90303041c04040082800c42c01002d0240e100000c1130016031200300700510003254080d03c1e019096003007da180018100d13040b0115112500c40b1030100748a000180301282c03148180d102031074018011160160380091801d45903800000003140c525031603074010b020b038035a01d28800e42c1c4a054000250308020819902949451805052500b40c44000c04d240041c0c0e40d42a0b100b0005007440c04001152012a0800a000180 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 522435908 1250 522434658 522434687
    0x23150906042d0e190b0414030313030f170f0705130923040213153c0b04060807090510020a0605010b0c0c0f03120c0706020c04060f1202030708030406 66
    0x10342100307002810f0000c2500303580154111400c2d0038081181d034400c04110b1000e44152103c00c40210256028281000290301a200b5019405004241450700604840d00046c0b08170400400316070409411445056003900f05100e06d05541c2e255030307000001c5802d40181520100184140000090302c40b841e54046014100780520351420032070f408021310038401040c3d900a4202101c0845d211400c54664041c1e0801040e030454542c0c016070f552035006000640400e85113058600302008036540f80044822400c41c9011045240c1d624030b8209560002d01603403041000303012106e00085c0a05120781c000700040c090042036000c407012900700007961220705030b05c21511285000004113070140020261800001200014000d1038000424400c0c000d2003000c10b5509031040c000d001c040303520800064203404400400074203815240c050002c6c90300c400e4034000c50183e4501041409007070030403917000c8145c0c1ea0132210b82c0248400341c401b181c0b03084540c0d070040f1100d0001060100d00070758040111b91107940e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 522437158 1250 522435908 522435911
    0x2a31090c090501140609010c11090c0c0f010606141e1b1608030f1c050c0903120901050d0b01051c0b1003020f0301091107120323150906042d 62
    0x7a04e542c0204042c5540400b02544150305210980c0b007503200c1d1201a910300c0c030482041c1140d00c2c41c031012940070501030325581c542c540d0215000c00250320400c05000042195002400007a1030648003600321484484844a425000102c41c50305640c055083d021074016422050307650344081101c480300c004401142c15441c0a41148001251003e5440b1419183c0e03290156140150140100250f40d000140d040544180d581a8010001c401d11445204a407a030a0300c50350781c403041d000c00d81080b6a4188012040b4024000c410709079901c4000d58030001580d050015503061342d04010380e00c500405918024401ca140b40e480721601c0c0980040384004800d071b903010824000002d080c3c2c1a8022908503001c03051003070004000c0c43e07005420600302440300c00b07085460218030740c40b90391503255222003e6004c82c0e100c0d081c081000c2158525600b080d411041d4900c00d900b00382000c8001c10307480800440c402c60140c004a52182d40d15172200362007041118140d101c00b84032004108021011a84400040d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 522438408 1250 522437158 522437161
    0x120b04080c030406260f1807080a0807030f08010303050d0c1b03020d03230f15120304060e0105120402010e04020d020703090f0905070921080703022a31090c0905 71
    0x178440b420094000c8500c9012010b0540e04c251000c0822005880049414440e0250009000005000036041180921445990f40320b070307410058803001d2603a080a08106d204001040032913400810fa03070039600e8111001ca414030190303504540440009800d088200521070360f00c1c08154001600784011001038a00f840b18501e0425035103440400c0c0c500780304000c00c5507800216000c507000940c41d4002080c0e010680f003040c0f0080030a03040e0641040c0e42c102c40e400000d05000468011050695a00007464618948100c03050204010341c0040c10081c14860300e0969982c140d13860f034050b104c0e0200070910454940340c090400038401525403040091703030080c580020990581c2401a14491600c1c0d8458003c1c00307180c001ca150100c1c0100032640100100b0452403000104841c005020860003a802442c80e55a40341400d20740744003902070114141c92000c0c0305000ca4031a0718070386481c2107003401f0040780c1c0c103080204104500c16001c9800b1109107801c01c50b02c100000d501048003520004041080b45 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 522439658 1250 522438408 522438467
    0x804090f0e06090c130e060708040308060a1a0c010605060c0a02150c070e1e040b0610021b100e062d04120b0603032a010c0801120b04080c030406 64
    0xb10041910910442d0304103420031451130a010110449004981c00000f0380082c42d5410107090080641d11a400903001100303002c10b050b80140381343d801c01003c5840600c02490a0184240c980d11454400801c00d004500d6099040b4290321610007440041e209a90b10729070089480d86a4900031005ca1148042ca0743c4159082881001d6442ea84200390007820400d060450b82d0a01d0400248401e00c10b0118401c61b0808106c0510001d005512503040403410b0b081c100e0410000002500c0890210352100604070b501c028059441200c01d54152000340860701c40000454128a560310556000364001610b044010100c060304400b282c0c0190014210000c19107a8035118462842010840c106035042900460f014001c42c58204800408483ca0986840441210346181e80c614902018aa82c05038844800a000ba141222070a1501d6060ba40c10011003241040171940060009840040010100640300c81120003032890901101e8649a40f58001440f160310b13030954188220b10707210100c45 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 522440908 1250 522439658 522439663
    0xe0105090103080c030c1b011d1503090a02030f0a06200301030618050109140c03030a080a02070602040b0c0c1c02031c0e12031b060105130e01090804090f0e 69
    0x16100000c003041000e92964840f00e4480d0408041000c0714002004183c074191803c002a42e00700000e808002107103c009400035001507004021800b00752600107446c0070a0b83c0f40740e4001050003640182d40d407170b9200c5424003842d0040c0303014020340500c40e02e6100c55501d08000b80c82a00d01c0e20800040c000580e0780b12803070300511070001e880c20124805000610009041d07030000344200051845090034181561103090944514010a40d444482e8100e0003081d848180300315907880d4029401986880010800101003501c0146140441035000c030740310080000b280c045070300810348101d20326200c0b045099095103900c8030140803841001c422440305800d2080c0800d0007043d640040240070341d00480e0240345459400d009400080180410780c4c450240d58a403031010f03401d0303003c10055032900200b482c10704070ba070401081e0311400e50006004100303641e118126200071025960001c22211500a8a07a001d4204032800500e000d0011401042c1c48606a0054046291080e400d002e1043c14180030364 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 522442158 1250 522440908 522440911
    0x711010906120203040602210402010e0f0f0d020307030204111209010c09031e020a120311061303210c05070302011a010203030612190807120f050702010c11090c0c070e 74
    0xc0031030503142c400e0070794030802d82c007441d0b010340515009031501075030705100703a1002c201402d1022040f98103070503c000c3d940e10014014100000f9105403600c016802c002840e95488000002c0c45040080408011502c042c010400253f9000d4414014a03040d2190f207001358100e070031103180c0300d0031000008400074014090309039410f01c19250442d526045840c0d50f0101d2141240c18824010b2284688005848281c0094003e003102d405c9122107a041b49001046000b03c2000d0f83c0160380702d00c0510400710542ca4041d40e02d070340c0c18201620403102140444e0b03502051001c070350f01c8407440d0080d03031641c10790840b0003441c1852095008104000340c242a17888078040d40000e00380180d1060002a005007002d4450404026140044030700c250300c0c5c483d51018031003031183d044405840104282e000c11507000c15000d503000a90601c920000ba409400400700c2c094031101034100800400580c00f03002898590f04442d4001800007596440c10300c1021b00c0c0d9511407080d4a889200300c1030005007100d61071140c02e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 522443408 1250 522442158 522442169
    0x50f220b04030e01030912030c020d050c0c09070210150e01052d060c010f0c03050c12070e060403050a03020a120e0114070201050f0a0801050310020a050909181207110109 75
    0x512203481e00e8070110f0300d01c01c10031459818583c0c0c0c0c003941d070040780410b8070010845c506c80d5070200c1c060b051100c0c02420142d4505601c81805411f000181403c200840e00c034140c060705580c0d5a0b082d9803001400ca2400381c0c81c00000c48464500407900764401c0311401080255414501c85501590b6900c0c2031280d00a0352056003d086060862806050301d401c00514403a0a402048a81052004800982180c0c0e840d01c03d440e00640e680b00441c6029094040d0980c00400140c203070b428003c61840d03020315400001e203048204120f0b400c01800f10b98170181030700c020f15001800c403031085030750b0b2902941e544501001900d120251b030001030141d6100344011948078106035200b48403003191f42e01202503030b00090012818000c003404415424003001c40900201c5c070740c0e685c4060071549030000381414010807415141e00e132401040242d46061b00076041320106138069594050a50784c10400c4050300c91803001c2040c075401030a038048101d00840c2c0c01742185074000e43c45201980b46003401942c1c20f48042c45507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 522444658 1250 522443408 522443423
    0xf030c03150d030509120f0d0e1005270a030f0b07200d0804062d0b0405010e0f0a0e030a270e010b070c0819110f0f04090c0801050f22 59
    0x80c0400d061200340c2c0c83e00103500340c0c1164842c4c280c84141505240d01c03c080e10340042d4840300806582e15110400040038030752400c180785014050189a51042c1b0000160140c050f01c104031031a00b901d370411500025034101034482c038564400e14152107980130603542070001568146000d0138204400d0307404002482a40f0080c0340c12000d0b813005884100c0f008205440c480d0341c4e0312111820360400a01028091840f60076075940d203151950342c8080740c0f000b0524034080c924100061242d420500c03001038100307102e900e070440700f83d032941400d001410640300850343c41d00001c02c040d8029a00060700d0201d00e40c4802d9400d486d01d0285590721840d20070352081c000d40303880d0200100282d0040c04010131010740103805080e00e0130b44490803a0314005420450300d40c8500b41c0a021000c2c800302a151403007a04003291a1030f1404281030000340c02e02031402e645481a580c80c4206010440726810f01e82c014002d07a030003030007070386049000c0c2044130724111004407400311302849040808190040704408a0352102d034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 522445908 1250 522444658 522444667
    0xc09081b060912010f0f0606090b0a0813150c030c1b0b01060c0831080f10150801060f0911030c0319061d011703070c05090c0f030c03150d0305 63
    0x100f0491502d0080c080065542e1510414a665024043c00e004c03500d40181c04148249800c400070811801ca81c000b00b14580309000480282d43d100000613040b42c2d0b1b00c2514400f450b0ae5007400001c20100344075641c442c0c0c2c40c4c0341c100c054403605030b0004036114080d40c4a112462060900325115602e001c00d008000c00d803907400502101c0d0040c0c031200181c601030f001240c14414080340c00700480e192050944650015034a400d1811003c8480641c080c10301d107130142851222500d12907566011064407640c1490300d844103080e501c01001690801401c204000344106030755100015945c1043d0b009002a45040954906041200310100d03402400c10b003000740c0c5940d071803e0f4064120600f04034803002464640c8000125030329130b2400d120390b43e04107040c4a04254035014032030b11118080d640c840f0041e00140603da01003031084d20040d0866009a0310340006070750340718000c980c51080070b480380d030081004024040e000d4003080c0a5803160b60b00300d085803101344200b02000343c500d1a413040100002c10070403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 522447158 1250 522445908 522445927
    0x1d0301020f09060d0905070909111c120201150e04060b0103050610030e0709091505150d02061e03070c0606080606090a0903090510020a0507150906140c010c09081b06 73
    0x3c00070105107189a500140030040d0b9554141000440d60100458076290040034042c007032080034626144204440074100541c10102c000d440020140010f00140a801d0040ca9600c0c000c2d000305d80070740c0c184103203210b0194030384000d0084070f0030584050f511149041e03541d052550091048a000320340042c4a0f550300e10800c035040380a82140701116800c0e02810000042111a40c006c0c003c0702c6110783c000c0c01110210812000480e20300420000c40f445400075084200d4881d588403010454060700c40725502e00c4200d100b9919150380c03007034100720b20800200700304110340d00c5841c140c421442040107000395580c0b4009141e0b10b0341c0548089500569210101d41300751082d0744001e100622900340340050580d114009108030391034407081e40c00b603041501e0b00340401406009500c05080c1d0b6014850f042c1c00f02e0440200740d140c06000380018002c00080718003c041001059a151030001002442800300c042001040c403801c40c402d004c06403040d14100030207040403040c2035441c060068401c17030821041c513 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 522448408 1250 522447158 522447169
    0x94109030f120a0212010603020304020108060307050a05060c0106050a030c0e0a020405011209051005040819020a050a030f140d0c0311070f06020d061d251704110409031d0301020f09 80
    0x10304041d0f08140d0800901c038044030507002d0503008003034a8070016120714081c000940140001480030748250860700c0c061166070356546e2a0416a02c0030f59204c0c0d10f5450010381340d8010295a0409a403000c281c0c4000000c00212226403001e03640c0c44a405605515070171604821380c065400f9590104200c15031318442d5a42d544e02c81000bc501520840d0508007a00d80300c6000c5800a84041c0e50180c40010315408030400a0080041e80e40644001d020880407501c07201c0c0c072540b0381d40c001010009040c40d8500da85120340034540c640d1001084041d80c52040c00a0400181040020a80445c0c103007130300c000c50241520705035102c04d90030241e0b4915000701590340c28001d40c0718402c804444c0c1d5840c100450140e5121040c040d91944551552005003040c02298500d44c103420030340c0d081c90307086443c2c1d600d042e83e00c4040e0345d0b500103c83e40c05040ca40c0b81c9182c1400410301182045400c00c0c5894550004d05a104807260b10380c20409048071a42c12100007803500f03034469040e00389120130701040049480d0411 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 522449658 1250 522448408 522448411
    0x4060b0d1b1b08090a1806050406080a080414060909090102090406050a03020d0303200a05040e0604110d09020607080a0804020a06110a0803090309150a020d09050a094109030f12 78
    0x500e0f170521903480320a0000c01c0d40c200c1c5403140c0c405035100401c0c011381c2028440e130402b6015040041a81d26015681c412031071099000d0385100040601400c4c1861b1101c00588001c490001d00c000721600d4241c210900035000345080c1032041d42001c20010325410441601c03400d50360040e1034030780d955403151410382c06040c2c03001002c516440401e03c001e280060902c081c02d030361300e4650740b03040d507440c50010039004c3d0380c40280806110707600d4000500ca1200000f030450340d5850a03c407001c210090940002070850080d80c001420100c0300041e60440d4031380c0035040e140300f244200c580302080d94030b4030000c035120180c0031000d00095018541070303408580314002940d44803401d001101e107081c7c00000400c0200103090f1040c4001440883c840e405141c0610040c0014402880c000741c68074a4030002a40c85501132140517803072503660206146d0103440a413015503a800114000e0941003a0307901e1001c03c103500062000600700501c0214800140100c1144d604003801040c0301d041c800c4110101400050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 522450908 1250 522449658 522449677
    0x308071a070f2007060c020931050f03070c03060509210c011b02010204080d020c060405010c032303011a030c041a04030605091b060c070e0604060b0d1b1b08 69
    0xa500d201000752074804c00141003c1c0205541d45c1d20084180d01c140070703010360f000c0d1020018802030301082c4400c048030681a07102102011440310404114200242003c405421907840d5000004201c828842c84220f09070403648a21710800c180d80da010811900c1d030840d118003040c0440d0301c6031071000f006031000182c62400d8285000180b11604400600d00018101041c0c1c0050307500458100070b001d4060001406400b01400942112013074a40000da0034411802020b0500c00341a82050034144646100740c0508600c802c4401106810718000c07000d50402d22942143c00c1440d0781da0007008102405807801200700c0d4001c0d606290406000001050303060324081c00c0003c05000c0040441e080740505030041c60000082c0420381005141b900d54080d008144500604080090200764140000d40b041180d05100c2400d1741c940750240000d01905840d031009040a0340441c0e0540441342c0356001c03050013408102c00b0600c0007100c80042c0e442810110203450030100610452010420603001400080f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 522452158 1250 522450908 522450947
    0x10b0f0f151801080601090e060907140304061407030902130c030e0a03032301180c02010609060b0904061a030c0a030b1206060306090f0c0d0206040b03010308071a070f 74
    0x42622072980065049034014000000b482c1900581c1960400592904038400786000000c007410283c1c0240c400502414032406034130360f80005040c2d00e204480250410405801c59a9a802d103802e08034090f08100d41c2c10110540000c01283d2028002d10813100229409004400250404003116008000035001a400d0585401501083d03001c1030000448251007a10005401111000a40780104c00c1c0560344416109000051003a80c1c0c2c644085080c4407a0128045141415510b0407030250420781e100144550421402249004800c0050b220150003a201004880e94440e601e99480801988a40f440e20342040410008000e60f00144840030306401d011a032004114049044a2014101350740703c2d80154080c4180c0b85010b03c4640d0300100c64100410a01c003000c9500790b140c40285c554140310700340c40d5100c0340031074803954155070013000401105500e960752030a10034825841a501210910302e24001035182480d400310442c052401541c418680244500341603540301c40e111070901490 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 522453408 1250 522452158 522452179
    0x908030307090620160f081f021b0607031406040b012102040e0c0403031e0210090f02030a0501200f090f042c0c061e0924040611010b0f0f 61
    0x1130410008204100702a18401260b1030005456040c25031a00100d0140d003213201d0400881c01c180900c589400034140005070ba80c0c01900c03a03580c0b104203840c2d0542e001d0203440100155030f50160301401030321402c402240100d9842d001004100c1e200c402c40c1e82d001c50351201d10362100009680d410014101c000704014a0a5202d40ca484000b80d01101d82448200700081c0c1401019401030280c41d61007880e4038078154003514450040e485001c00f0f250b41400c555950b407104e090080381e5142c582c9154002d03041d900050100e00704103020700101030595078a00091464a241040398908903071418190000e280c0c10501110100071201b4002c419003a40191158200700102458a00d0900c51850b15540480d5420141c08041d06094041103440d01c0707140141710055013220000c00010003101c0510a00d80c3e02d40c00c0c000020303407058800650303941e9558442c4880000c60315102c0140203442413034444940700640b0701c0d405401e03110b440c00d6007500100040c5041640e400d008003811011500184252942d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 522454658 1250 522453408 522453467
    0x50c03040b0711100c0e1e1005070609080304020a0602060c0715060b12062107090905012304031e050912030405060a0e12060108070b0c0102041a0a09080303070906 72
    0x82200e13580d01e42c51495990040c0001154200e8414140d101081d6030520030008683e500c650400d00d11702d1000e0113030051564054020748140300f1100103541c080d4041001c2102d43c00c003241d07950022a002c1b0b01038661100b001c40c0e030500001d12948146040006589032421a0b59414940182d410911203607944650002c94440980740c0540018002c0100d10252460084104449208811003455242c1c8e810141d14040d4280800e5806c1030b52100368000c1145007003031a0990040c10110100d10011409620303403c3c0c50441c000c2568040c034001c1d40d0741c11922404541400f1103440110700b850214100f000316030814241980c86010006202003070700d0a290b40d4402041055100850160019000d240403241c2c1c0d1407d0080c03842c0d080e258800500042d03041c00c02e51952000503000e403840c109000700e21002e1001003501120050490389a4904006140072803400843e00700c110310002042d00c129010030200c00000660b4407c02240d61100c2c2c82926040c81581c01032203408241d0703000c0c03201500c20320f503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 522455908 1250 522454658 522454663
    0x30504230a1403031605180411070c03120e010e09180a0b0106030c12060e07080a06030206070828090b0c010609020f0306120304050f0105090d2112050c03040b0711 72
    0x1041071800510f0b0382e81742c410030a035842d0003105002c2c3c040c808203001407180641d480d0000e0302d0382402520000361031b030720460240c07015014004005000010025000c403c00c02030030300190755800e0584882c1d00705043e280040d0f5400e91500a0180c0020821001595440990114844c954103000c1660401800c1d5112403400d61001d822505c0481d0f00c030207040c20304aa020f0880e80742c003503c0940800c141401c2100705528007001624900820a204010820400055014100031a40100700035a2140d00c0e02d4803030342d550040c00d1001c0010703020343c24078070010b035540192001802d20742d902c0c0682a410800060002e8110420080e4035650316400440e22001c50701c021700243e1441c0d501e480e26481e2500410004240d610f0460701550400d10040116031034508440d02c24400908009865041d00c0b0701203200d0726210013016100d141d6042c07004500d0a40080b18191210701d03580d0742c4041381d00d081101015144c0607a025201c4010800c00076000c203500354076a42c1c1003000d900c0d001c45c542c40040103092 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 522457158 1250 522455908 522455933
    0x30b061509030615180907060305270706090b0c0a030516050709060503060702031e0d0216150b030d0c020609010e090108030306011706060a0c150606030209090601030504230a 77
    0x2144284c038201e0700d1450307140ca0701c8001401c041d02140b00c2c07010300e8040510341c0c0762120344c85520141910b9101040e140082e407030000d03140c0c1d071040b490748440490b04158969165100e1040501003040b0b1040840d075500d09200700c900390b800b404000c0c02651010b650407182940414000d031284451100c19200242c2c0c24044071005084903038000c42c403c1d05040815081200140152b0700b9580f0410030b0007040b08030b0204149102c10a1000681c036101b1610102e4041d100b10036100c0c446003040200c0d4010060b4190240302d00701c0002c05c08025102c8188141652101d0514103c00030886400241005241120080195410614000000c540440c001c0f8180340d00070b81064601e5040401000040d590142c54146007151202c43d0388014240f540124800e480755100d0b5208102c10025000144104071420754408100e0725010400c40b80d442c1d90040003500021102c610502e4000081241ca620030302071a4000c0d038008101d014600b400310380b4100c2e500d001c01e104003031502480381f440c0040b411942c20b84 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 522458408 1250 522457158 522457171
    0xc09020d0510050603061804020a0513021822050a0e0102040e090d03020702091303231c0204030209070507060b03150a0e010e06072102070507030219030b0615090306 73
    0x3260600b854000660341c1a06034000a008103000c1c820403090b0307501c119441820742c0c868400b040c11501e0303070300101d2150070710340d00015000f00f010507144448007450740c01883e014100e50f80d04008000c510f010000d602c051140100e6644061000c845010403180c2e2100303801c0a50b0020005002c0c0f40e0001c03460990b086940400c4498480343e04200f6404018800c4400000852801710700e04401940028081c04016101d0100c08110182510030180112064070340f680c4c010b00006003d0b07640180340f00e09688079052010250240700d00c01c181001d0203009072010b0fa41d0040c90400c45a80f0b40170225125080314006031041038903400d0b4100301d80c5080c400401c1c4400e00d41c952004034907100580030103484d40d501108503241c3c907014540700b8107603022aa9980040d41e902d4020300440c000304121a0241e089920b000c10303a03100246010401c0340008040f0202c0f442580c1c11000c98003200080d01000c0040d22024105100c604d001440c0392130041c03a0402c4242a0002c510304000c0c41c000428688241201c08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 522459658 1250 522458408 522458411
    0x507030501090203070906081902011214070e010206040b0612031209030310150c02221d16180b0103061d041502160615080307120801060c0f030c0c09020d 68
    0x242c066040a10541002d080d0060701401300c0c4d8038018245598401c0d101c1c00c8072031110800c0744c4804681c0314404248009020179824024250540f24003c0c9001043c4d424401081118810b00190b50011543c244a59000b0b080804140e5400342072000301210080082024002008070707a01ca64a001c6525008800202c001c645070703c0c0c5840c44d1095510360b81c1001e03200700001c191684245500035001c03104994159400e180302001e200840001d0005c510070000e00c0780c2882490f06684408044226644803e4800c40e106100c90140e02c1c0038083c558004e191130840108000d40343c2c00502c0d0840c23040004103242c0095070f07640e1544118041e1007401c00184110030040706010034090040841030302112603400443c5880382542940c00311402032000241402d07207071005000c4c42d00300c0f5108480180048002e503546c40545151401c141034901180c003000c600041d002041c1d141c80b9440710b4850079070003031480e0710145143e00c040d1090340b1070031401c9901400c1030706d0201d10b06a02d40007030300544014050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 522460908 1250 522459658 522459671
    0xe030604051c0903121d041a040c050a0225031a04050705040b0109030b060f090705030f070206060d020618030706090302120a1e0f02090403050304140c0a0618030507030501 76
    0x2144111501c0d0b031444000b04843c003003052001c11401c104e09241000182003100c4d905450145051040038040c41490b4020b1804a020b0800c400b090b0051108260464003000041000ba20659241c001c0da0350250059008082c07207400c41c02260f0419001b51001040d02c200b00342d03655a0043ca0030606220051019907020034081000000c0252202406040701c0c2445030703490300000284020010300c006408054540e01080f030940781d01082c1d00302c006018150308820314140b0400342030b541c415110080700203042d0b00025001c4c0d101169a6000e1040181400322850660b0208580e6070400b0041581400c01c521600032241e0b0304105480c002c00d40ca407142e401152442c0100108044803c01685a6400908c031001c0050b004405c903c00d2400d80088400484c07a041c24007501d01501070900940001030380b0188001d054011b800342d0f20591042020206410110100c03035198407008140b81d400c240320100a000850040da18168070362803503003c803010280d40b61107843c40c0078042c2e4400d9a40d40d55850 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 522462158 1250 522460908 522460933
    0x62c070215041a0a060b0a0e1203071209080705090402060307051909090c0302090307051215100f090b0d08160b161103030712091a0a0e10110301090b010e03060405 72
    0x200c03c1030b84481e0901c000c0021500c1c10300501541d1080741c5036201009180300321524203585007540c61a4031081c2c0d60881e82c84154614241ca80e000742406c2c0d200110b60110000500ca6100140b01001d07180043c0054145172500d9081c000b25400103000102403020a00181880420b01a2007510580c51a0344004101d0b103400d0405089440c1040c000d820180100580e107181d0f01d001511004441098610f09010440501c1c01824480c0300343d450b240340348a0800340030080c800c09003a803041c4c030b400c2c00115600d15a01d0611400310f40107003104070781110751a1001d0300812031000140140386444000d01190030196503420b464500c04850100081d10b0a4403510303041988040781e440c1070b0640034011031450600000180840c00968000f020f07898484100070304102498040300e44850059018410700e00b0084510005000403017800001c0e8800c0c4041810b40503546d000d0b0464844400281500d56402e108520016060600286040c0003000d4541e070000c0c0c42c01c1141510a07801380d00070702880d40414 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 522463408 1250 522462158 522462203
    0x602030f041b2402161205010b0a030f030e03030405100c1e0206040b0d110c010e01050604060b0d050c071e0308010602160b0904090c0602010609062c07021504 70
    0x280c440d0810781c500e858280f20880b29003005050b995818469207220702e640000c201d250040c0041c15800d0728468845c00a605000c50380d840800320701c940001c0c8000c1d00880d00340301f442c480610016020322189075007240807a0150305c002a408101070152807130140ca40c03011402606445426400060700304d4880020b0188024280946100307605881d40c0341141d5400003074080c0140d00441c1c0900e000003c00402503009035200c86036001c410000c1946880b81c22050b14000c01c048030840c5040c0d4200f00009441c0d2902d80b0030307801030f01c4100000d40c1c1040754000b10039000b00f400806075414030004008510216032503070388800c4007500201e007080da11401854000d00300d09040c2e00c494255408101c090720181d01c03c80788002500c020014490f183c030711510000d005481d4282001e0b0000001d03120101b00198103410850560f04004003c0c01050f03a01c0e01441101d22981501a070880c000000c102d890038508622160401403600c104d801c603080c49001141a00415035084071a440600351180f02c85015 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 522464658 1250 522463408 522463433
    0x901020f161806240509030d050c0607030b0a0614160c0302030d090b07060902190305010e0706020a1505190f0605090702010207030f110f03040b0a08091f02090d0602030f04 76
    0x210b0000344031842ca0101d2803059031030a010b80c02c509041e0a8030440d5100c1c41802a1050b1610040c00c68000c03455001c0d010b44998445880d400c021b0207a580010700150090060703003140720700a88508140b42c1ba100080310780d800e5601050000500421502800d00001c2022800e403500450080d81d1891651040619000c4181245410705c01c0140c1c0800c9416400030540d04999082100030500903000d00c006000321060460844400c0c440c1c0e10040240a81503000b0070480150604451096442e100c06030b9451b2000b000c002c1c0607001c213610300c050440c115040136030000d405007000c50f00c1140900300079050321164100d036140d155850710204824a041800740340c0041d1140000c40c0750050a0706d00a0181032000c5000003800321885581500e1481080740345007015460040d01d0720340341c0b0b405054032507a0010f401c1d140018100c9002c02e24605001c034192010216a4a80400800d400b212440203500604285c036400b6007417118900124545000642c450701c41705000c510340345800d107810003c9030507 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 522465908 1250 522464658 522464699
    0xb1e09101409030d0f0204180b0306011e150212041e090209060316091203030e0f070602060a0e011812140f071e05030705060117060f07050901020f16 66
    0x907240700380600c20b6004003c5851007010740202066101c0039400340300291203203603c50403181c0945000683c211000d940060000300044081c0d6641e43d99030065540340804085006032080380e084000c2101c09082c40c030745060301900703005440c00c1038a809e000201a810952210b4024803040213890f680b8054005603501130903503100214101a2203401080c00390000400681c201c2102e04d60302003405005180450050010240401012800d4039004011701036100075080d103489071440781c0c2171140002c0b481c9000d1390780650061000b66500740e000380c090103008001745015568ac120201c00100c8040d01075840c0d80c010702c2d134a18408040c4000074240c0b048076000070782d07032141032101070100291401151407aa41242070351450004401c40d080d4a000d2482d0014158400055010b0422101180b0141210001008004c103070b080c003d041900e402c022204003e0326101e00000540e01400760b801ba2003c120306204482045440155581c035240d070b80c2010340b090112000d01008441c40741c210042c0c861340c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 522467158 1250 522465908 522465941
    0x60606050a090501050903100c03091110050f0a09050a12050f06040c090e1f060611030906030708040f0b07050408010b010207050d02010e1203070308010e160801030b1e0910 76
    0x10703003000003414404203010f16810044005944400e0341c2d0104440c0013001c0f41242c040081407000300002c5c0041542100454141440c042e140d00b484c83d040f0750920307980c00c05071104c61404030380c03140c0321039150f000412143c10720055030004031f4070f500c410110101410040e40d1940e248502d50604526086c0340c201c0da4401c541c040c00402000552800302d0004a595800d004070301c4100c60412075041c00c118140031104140aa800d508a103811500180b0450707441d0b441c0d90300d4400703540345255140e210798001e00303410002c10804602c6030f5102d0072071f043d880386c0610800f010300d101da40e403101036007103054600d00002100442c01344411802845213140540342400140760092074070010508250782c2d80030117410301404161420450700e45090460f070501c14202500d55548440c50050400403007070080608440341040010703564800c0d030982c00304070400c0b51116038041e0318542e9241c4401074000d10580d03001242001039441d4030502e0a2250242040710302400020303d0f480526402c031362091100b500c540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 522468408 1250 522467158 522467167
    0x21803011803050a020c0301230619140a1e0501030b030703050604110102010216051c030e061911041d06031c03150b160b18030a0e0a0911030406060605 67
    0x3004001d500d01600e925080c866180c104600082c0e050400c06148150103500f00480f854050b907000c940740e1584041d51404440a86942041c046c5081c03400c108000ca1001e60b040c10702c05409034000c00b100e001d00050400000315110034500c1d110b6071048002a0722001440024441d9617054000c903604003c09500404256282d5141c0641e13900b8050405040c0716225102c80c0c1c002e900c03c3d011103403016008220807e42c03000a01d000f0380d41e6564641c1c0039801c002d80400e072802d400e100b4001c2620320418140188200e44642112036031044280701803224181e07441305101034601000e809800180f004201c580c400c900d29071010056254014034442c0b1940241d180e00a00c0a02014141103e840314074001070380303005188210700d07200d10315000005140b0f00810404201c2d0600f142e070008c07142c4504e180c041c0680b1024203420407078000c504a00141d41080c40402845407161364a0426848000d0a2a02041d51060305000702c80b16010403040b00c100c004100001c0c0a401c2c010b03c0d000b886036280151a2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 522469658 1250 522468408 522468431
    0x406050c070e060d1b030210050d06060804020d0b070e0406140a0e090d2114071b0302100b130603050c1503040309060507050a060e0c12010614010509061201030602180301 75
    0x1d40050f4400500c80c0c0900000301449181c0b21307083c5c0003d184e0141001d4115004c4450140c4070360811754000d20068208440422200c0c42074a0043c0901d50203000d8500d42c6016a0f00c5851145c8024040001c01c001c01060350182d5440f8014400203100d102c414103003218402c824416400d010b5080356500205400c203114550000040c150f480b038025281c40a10194a50001a440d50311841c12104071030502c04c1d811000740d4000c84d01406200d0b02d4039400d60580c9600b00b0030303181c0008000c0c0500580c114805068441c1004e4120809900006040c502c0916000351980100c1e802504151841c0e40480c1c444c8070b0608003110382903148005d602d1124118a00790350008c00020740303401040d040107000b051410400c0800c01811401035840417081c010502c21800d1156900a80d0411502c135103412003005d0301c80d40d8188110300a0b20b05410103d40502d10302e40c0117480d186d00442c0280d070495001c01c603a2810810120319940178510501c0c000d0f0340d5001e00d0590404007803054507113500c2a40741641c040340c17 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 522470908 1250 522469658 522469669
    0x204120b09070b0d060501170f160507020604030b07030605061602010f0c05010e010921090e060a0806040501060501200d080c0d181b0803220b0406050c070e06 70
    0x102035844104035030035544814030181490250b038000354482001150364980d55180d40c214000f500e4082e030300e036001e07801d45240c00071025005940510020383c4074008036000040f0043c601ea840201814100e1030800c541e40440d03103ea00c40d520580d601c2c041c240600a07402d038140a260b000b00001c840341414a1803170000d480300c40d40b001500905024420346c0c1c0c003401c0c900038045131100ca41c0100080020741211507039240030340003103501210124032080f2201800c40040a40d2107011072640c0d0b444800c0d50911780100b10154000d043c255001c030401d500000ca4101c00c01c02c692295108000129003180703010005401c9070701549000800c0c2c4100c03060746104200010350940402c5a520780000961542035031038a83e0300c01c0d51030005807107042500b201d03c10942c0c5461501d07501c2c400e0a54401e0800080c5080780542d8047c0038010f00c0f03410070018020344000d00d000c3c0404c01d50b1072464004510766150300e0300107140e00903070100700400c1d008950301e64074285c14401500140b0181d0129456458404001070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 522472158 1250 522470908 522470939
    0x10806060a0804020411070f0b0105092a1e0d23060d0f080c0d0e0612041407180c0e1234030b04121403010b030405100c050417010204 59
    0x10208060303900050f0544d80c4640010400703200b0303820001d40d1680b030380c02e1815900c2c414890070b43c2c600501000020fa1400c00d07042c114444c180d1448120230040d00c1c3c140702c03040f500c8441040441c80c85d09105220344a8450030340035912151540c1c00641e01c00c2c80d64481c809540c00040c800c841c4c01203200300c1d5081019028001130323102800f21410003071311b0347c0c0389400d40c0c041c0d0041001404100c00070580d4480701da80090092030841040e1548250290711000300070b9107200e40204200080078010214000520412030b04101c3c0c510700050780d07446502c5140f003402d102004400c2c40c564075120030f00c45d03c203da005002501600c0099076117240c510407071a0342d243d0fa00f0558801020800d003103112000501c0104981840c44815810300d0000d480e075a0508604050090702d0a5940394010500d00250a0042408175110103900e441c150842e0b1821007a054107400060058926010f0342e0540e4203000d8961041b0000b01010392242a21713203040200116540000351215600c9030b10420040c01441510425030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 522473408 1250 522472158 522472177
    0xf020604080307020a0624050a12031119030c0209011706060108060609040912090e041a06040e250b12010902090402120c090414150d0c0503030c0f070501080606 71
    0x342c0c0c036143d00702c04174a80b08984034090101440c4c6884a82c411804164007400c07401200305a01c0303259255000c00c6644111072080f400c5d2444614281400a801050f029030030200c0d10041c1d90b48003440009100c1e2039406c015080f000240100d84040862804411003405000c030041c100d00d0700140c5600180e683d200240c01c01c0d05100030000021820380d109011108540d4004c0d20611071010300740740000850404560200100e0402100812400d0124015501c120b80024107111070000304444240c05460180c60942c02503251311140e624503100708103260210450200180750000251000c9901009541102c070b4030348010040e155001e481400111b06540c80c050006a5071008940014020302c0b58a103a40c00003800501048000c4210701e002d801215410f403024400980c040c1c0c4480b841102c1240c000c0050340300301c078022000c3e0606500043c1c915201d0074030301c688241c544d000079255401144030303070f105544051040460100103103e20401000c00303082c07981c19800c190303002412034010711040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 522474658 1250 522473408 522473423
    0x21204111c0c090615051905090a030b090c1207060e0301090b07050c01060504021c18050f0d020f01090c1205031e0c010e1609090c0e0c0405010801060f020604 70
    0x545400c0d5192101180c21001011401d114514945800740c5182c120303200e90303090a40307000b400140084480702828010311540d550103160188480103403c03110b280d40132400c1000320903c60340303040351541d0351001c010310b0140c503c4514030300d020403a05103040c0c0000402402800805400a40c030400010414140d4400d030602c40101003074540804d00510507824042e11f89803074001400500d50300100180f01200c2584000d0001c981c4070402d0000b07911555059074110710300130407400040d2185603c54400d80d401b8511446403840c140e22420310b0400010000355450b040019035480340740c0c0420410800c00e400800900c1100c0d040c0c0c84800801c5c0452060200102031041c2d140c04004050044031102c060124200500100d40c00c2e141c080b0341c1180d40000200c0d86408000c0903000d41c0022034003181c032855282549600c1c2401004009400440c138129100d1380caa5402003000e20341c08003070520901c4c042d900c6a4544d8075003000140102410790040c3c042c4101d4000c50003810f0790206105502a070008032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 522475908 1250 522474658 522474683
    0x5130905060105120f07060807110102030405150702010e070b0d06080712080702010c0605190c03050f070f020a1703090106050108010b09060304140609010608010615120c030603021e090a021204 85
    0x10541c5c200035066007101001d02032540d001c42c1480c0c03c0360401d03026690300da03103400c0714851042c42c00b03080744810382e00601b240e0f1041141c0d400340142d9108441d0700002610000c604842c580481034984002ca030023a51340341501003080c141c5400548070f0034005060031001020340030f10300340351709a0303038080e6a4019003200b0b000500581135900a240308a50103a02c00010802442c0240c1000030003481d0052020505090062401c0350500c28003405000c0e01d40e841c0c035642035499011013643c41561300d01701541513003d0600c034240428242144100d02c100002d43d078982e40c1c03800700ea9050840311103801080c140310000c0b0060180303c4240c000e60302122010380d041036884c0c0340c07410070b9031402c2c0c200006130410f07101d40000c109401c50190000c1045801c0440244410b546030081e00194206458000c7e0008004e50903c0da4200e90b1900100043c003550708001030030b0758403074020909599428105a07410500440d05060718101144410f42c400c1d1880030031802c0c620310a00c000d812110251016180044c07482 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 522477158 1250 522475908 522475939
    0x504020906040e01030803070815031b150d0203160c1502090a05040207063c05150301090503120106030b06070b07020106081014010b070f081b010c030605130905060105 74
    0x48a003d4000d040440c546903a40c0e10305002140e00403201180003850010109030140c10300c80f615a00d18400038007038403050f411740c000d0800041051a645512240380e164030707048000c1da035008001d148000c800c00340e520b00d4510040c69003440415031460801c60344401035070200301c444c0000e01d04000113080240e5102100c6001440b021703065081160301600c0000c0240801846900c040c1f1000031840300121040411401c0e400e40c9003014801c8400741a2069000c40030180952005601c0041344a00c250040c27591030110742144c503040d500300c03801d030700000d0f08006c0da10348005142c0c0101101e190502103000751a0109078a03000e50240140801c100401090320707a8001e40005c40a088001c0c125000303d41c1180c1c00401626646c95604052101040003041038203441d4110758003243c200301001b60240761075079039101c6580320b9103000f070344860b00c500440e031014820b0103540c43d100074941c2d0104202d030030a02001100c000c0c05c4c00d0001da03c0d2800851100007a4082041c2d41120002c4030805005440c40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 522478408 1250 522477158 522477169
    0x141b0f161a070507141206190b18040b1b0906070602070602190e0a05180c091c0602031909030c03050a030b28170604060c0e0405100501020615060405040209 69
    0x50b00003003403802040c0d40131404074010702200c04402d400b21540088015003005294951505a80401e43c1031107400402503407a8894100c034220103000781507581140e03415050302c11180415038080310440020350034000a1039990701074011403001c12440c507107860031080001d150b6216074500246401d07000300c0d01c40c0c01d0003d0350381582e154500b038104a00c030120b103407080240a54210203081b4401c4010305804106414040030600228040101003880e5880d11202105140c21280b080c580c003410003110301e05400c148d50059a03046105910146c0c49007042e41c0c204c90120701010843c190f10f4544040003012035808803440c407903a80c150601ca80d84a464500440241c0b6280301a26001840710301c1004200d1085003c040c00000301c00c002c0007080e0303101c00c58105001101080900c250b03220001240100380940d00070b000182e000d04005411780c42050220f010307104111140d00500680070001c10155805000b079560060a2030502c902038810b84001544c103004078000c59009643c007040590268170303034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 522479658 1250 522478408 522478417
    0x63601023001031b170f010e010e03030105040509010e0f030c010c030b010c030819021309060b070b220b070503040b07050301050d112701140a050d08030601141b0f161a 74
    0x200f0002d90645840c44030b0596034002e00d002a031b5540d80b070309038840c00501c01849904100402070000d1480c41c0d29110400024100c0501208610f55075984000c140880401c07185140c403034554050b584440403007890b2404c548103680302c142414104045818580c1c1e2103440b5150351645401e040d403803929401003000a038200a00021902440015501380b41d00840700c01800315208601c06000090b1a242d503640240280c485c0203000c2403640f400b081c0301304920a084000e4201203c2c00704000e04468480c01d8240d40300b52050004214000180310900021803211079200300f860404c103241d9413600d0082284a40131050150003082c0741800040c0070b540c0c2942081900340d090f50300c0b003040b10900d0702d584124402032180130a24094445480c4041c105601d0350411580c00400050031a02191544035140c1d100801550400030121042c07000362000c60094944c13814600b0380240752082d020022490240010200a40c0c0d600c2481e00403c030f520940c0b140341c2a242d540300400c0d050b081c0400c11240c103014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 522480908 1250 522479658 522479669
    0x2071b06020307051002040e0105061c0221090a210c05060a1b020703021005070302100e16090e0303010504090c0806160801090c02063601023001031b 66
    0x2420000580c26500202615070b00307010701c040d180310b000522161400c038400c0c1d1080084202c1c05000401452a0030000790242c600d10f0242541071020010842c2c00300d9004605500d5001f02c444c0580d00b0b4a11104c2c01140d0041c03548000b0b01d60030000e5205c0e008101d0304240b001030050001e07400c201004e0320562108a080764000d00f01c0c1c01d80c2c103200500b003000e04080003151076030100381c2071002a40c0344001180400c803034000d4010301e030036a03840c2c0003120a680030070406e9080d486040f0b150756211141344104042c10341040d014100c043ca8168050b50808055030050321403d041400d910040b8101000b00c904644045500041d0344a040c076211040b00081c2d4480e4141f402001c040104005a03000060140040c90f540d48520303a8035055510100c0315500d802d0001a4881d400003201102805601080c07500710408010000c14614500c06041100c000c00103004d0350041005801c2100c4200c580146098000c149490382c074074901080c03241c40c0d05100140003662070f04005c0c0450411950031a01811 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 522482014 1106 522480908 522480953
    0xc071a100e070306170c0907030915020702030705030a2a0303020a03030f0e030703030e010b01090e07030207020609040606020a030e0405070e240a090e13150207 71
    0x1c1d40100440141641e440000c03851007080310010390504000c0c0700400b40c001600d8107200900002074000c50501d420194010000b0318060f004c0e06402c4549200180c40c1c81c0e42d400000e1405201e81d000a8050141080400070311641450031890828104500f21203420503503110744204055100c00740050b0040184500040d11903000071b0340300305041c0804600205812506400d56111010803000700795112501e40e20b5840030b0055800000c3c090a0000c14580b07010340300018100010001000c06038006050b17021551000d0542e000c010020b0010840191692000b942d40c1e08500802e0340422a0340320039194919090040702e1080c00c40341d4034554002e5008050000d01007401c4040807118420030342c00f00103a6000c1c00030300b54010550742c4010350700d40b0f442c4004071180c070040c204600c0c00b80e007800050f0105100e00d6403103150760026400141d8601e444d01382120715225a411000410 = true := by decide +kernel

theorem cover : BRFrame.Cov 522302158 522482014 := by
  have h0 := BRFrame.cov_init 522302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 522302158 ≤ n) (h2 : n < 522482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
