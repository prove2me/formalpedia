-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1575
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:47:36.708531+00:00
-- url     : https://prove2.me/submissions/e35fc7b3-fd0c-4f5a-bb40-2848743ba60e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 283093525 ≤ n < 283273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 283094775 1250 283093525 283093529
    0x1c021e09061b0601090b0111060103110a0503060a0501060e01050a080406051012050607030f02040602060f0a290f010e0310090804090c0c0501050a090506010b130909080c06090133 79
    0xc070b070440c0190b8162040340d079185000d2146011990074080468207552080a174503d0901c0d401c00180701a900b541d135951001c5004683c01d5803c107817501400a00356404005641c09150b149500044550512900529040300c4184090500000b00400507045900c50f414641c416000603000585840d0320080d0200c1c0e042590101341e089288801c25420b1000c00b10700b46001d588191020841103002000200c2680a07a210740380250300060001103241c44609009a44042e001780700040c201b1404e00004c034801c91329540e8281c0806181a54459400c2c4042805005079090070450110300700c800020760f4030030724000b103d502d26499541c1c072000c11002c4010307a006016001c40921280b295014010188120204185c84a40c28000400c44440c0f1070310a038078507140c01c407000d4640c0313030b00304000248640d10100c0034049500400000184020440c460000164405c0700099644c00400f6501032802101030034180d2103914281071140515819610390b2840e40340c2210440300701030305200703903060210360b5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 283096025 1250 283094775 283094797
    0x160e0d080c010e1612060504021201090c031511030a1a03030a030c030f1b0804050a020405070e011e050a1202120a05010e0c03011d0a0905070602031c021e0906 70
    0x880c0801c800001900036080b4020a0f40c11540d0b01600c900c2c0192841855100d43c600010702d401c00030020035001d82221303074080c0c0081e0407114500259182c4030700f1107880120503036103e1100b82042c8200b0001c01030928048495040c02e1144415071010354845200241180703c1c0c00d80c2d140032907461089810002a00c000e4002c3c1500e4880b818000c02a010740307507258800001170325004000c001030100d84503040140710001c4000542c02100c001c184e40c510000380c41940d1074482c2058000042e604c9000781032203921281e0702c118060164400141000481d503001c20803015200303641580302035100d0147c13510201546480c000c21f0000c1844d44000740b00d40c0c071810818201140812404001a810980c126448446d894005558010802669000a01404035404500c12003032181260b60345941d80c10142052001448012a90303400e482c141c02035002c003000d604041101e418051460303004020204540809514010351280d00f00035510b0404034000d808500407554000d65190b03481903912032910 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 283097275 1250 283096025 283096027
    0x40c02010c02160e0606130e040f0b070509030a1b0e100303020f060708011e1d16090302030606040507201c050f072003100203100e160e0d08 62
    0x445100a000e0401c800d00e840151250380201e5001600a82c0c0070000c071090b5103031212654841008004440c5e02052908040404100000c24031410317500d07909008a00c03540341c81c864400b181c50440b20642004000c182445000d21030014a5100803a010b0344444e803182c2d04420a14402c4161185400240c0100482c9040030b410018001150000701054074005c0d02140d07101180e00c0090b5a0300c0c4d4013220004002008403004001940d00742c03c0d002904411031129a0819440d0040040507888520072000c1c0c0181020606c01140e42c40007501c20049058581030311110f0031078020940e02e440240c01d6038040c42e96440041c0582c4d1003100c000681c40c40c10741b516105503019504855131050001c0d070b200c005400007001c1105d900d01400481d103102032000501e03810200d15868428603a541c0b080130325165001800c84817031955061142041001000c41c0050300c904100440c41c41c4200c10340c010051a010031014428154290541007180b01860310f820111010b141022031280741210000a0400f00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 283098525 1250 283097275 283097291
    0xf0906061303050106140307030c06030506031f0507090e0108030f072904120810031104090c0b18060a080415060f17060a091101050a03090c0f0f06050a0206150d0204 73
    0x10f070641003501181ca07183c550152400c003c2081603240d8015110082100041000c1006114001e4210307aa000f00001e040e2108040d0107902201c01c85001d40140200c070b9070747c0d82001820b5401600701c2c009050701c0000c0751211341c10010910340e28440c4558441d1030b004049880b10802c50034845e8462009403109030151034030f41c219a04d48514005580031070b490300d05110300b46200e80c8200d4409100c5c0111b040d82e2222249151644090100110011134110303840d01101c20100f041c0d0642880104801c0b030340e103035031030101042e4080340420841a251081d84100100310100390b20107140381d00a600460f1140c03070a00080e500f00010003c036072095011a6820b04000b52808600340c01c0d122119a2909443c1c05a803a900d14074111072403007400510050740c0030014031841d4860b201504047d0800d003000541c20040e0348a41c8404c04d82d40d8440c920440348800d040c030124101903090350043c03c0a0800900344044001c01a49451000300440004040040241e4440c1c0d140d1030b45d501d105801900c00c102140c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 283099775 1250 283098525 283098533
    0x2e062102060c0706170a0209010e090406090b07091404050630060a0207020406050907080a0f02040b19140a0e060a05040308070b01031214220f08060a0c0e0f0906061303 74
    0x12080e030241c40807001410000c6c0c111495402182d80c403150583d100c1d144961214202304201e10301600540c4d06a503130300f01e44030000d40c0e07800000380100143d80319007642500d01283c007500c4218124103d03001c0c0e8105800c0c40280d480304281641f6407009550501c1d40350000c0e100d90003280c440604405400d2041d80148034211b441e070360083c2030840c02502d0500c929901c500610102010651b00c42c4001500300d000103441e0485607201c04080c0d1041d000c05450300d40c0d91b8046040c1d6402031501220031400c891a21040325030000d45441c0d480342007654081c140491440007074601c00c0c183c040700d8058030707001810f4140180f1501c200d5015592001101d0f8482a9a0500705001d160902040300c5c039003001c001524285016603401201100007038902d51505a004030140c012174a14152005038103504d400110b00080c0c609481c00103010458010a20740c41c040d8541002d80e8914010401800001070200e00d10340c4a80c0e0410070040c1040d500600d00381ca50340046140361044000250301c00b54983d9000c4100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 283101025 1250 283099775 283099787
    0x7090b090a0c0512060415030c08150105010f12060b0d0207110a080c0d0f233003150901120209010e0609180307052e062102060c0706 59
    0x581400d03218852a80d071010189411150700c61201c101140c0706000c05401c50148642c55a4050005040840c92600d240304280c3c0210051b04212108480340c903050119200800c101200f0724000c6008001b0341d490000064029540325140400300300144800c0303540040c007a0401402021201680e0b0b607615a08000c0d40003d410520041341c4080940090101d680380050301001915649000340003d82c02060400001404101040324181c0301000c0710004510512041c003800a2029031184041c0b5854075560300303010802404401d01d80104455416400d04a44501c00e128000d030245035481d1280c050b004c0310350000305100c980c0b081c00000040707001d0107160b031000d148500c00d8912600590302e4104806040350200d402d241c12644080c002011308403048000110700c1d003060192450000075452301c030300703100000f01034500301d2900303001c0c0e940007040501c46031240418840042041c0f50030070080030b001020301003c22407480c03c003488040a56603600100c600900700d900481d20345a94414019180e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 283102275 1250 283101025 283101041
    0x706050a030c08090d1d03010e0c09010e010b0d1d070b0d06051c020904150c0801050f06030403020601170111071b050105040308030106050f0d14090c180105060703030e0709 76
    0x40e0610007218460350140c09418004e1036007a000d0019a100c88100701c4014903a0f03425828424041c0200400b241c4081c0b150010030503030303403004d400355a9070b2a050107040401a031154818030201c0004000d038160000640348420f03e0b4102c0802e0082421821051514a00c07504a01034000d41100207441c44030100142081e0340406002d001c010b54810800103988032030300c0300b103680b030400c0ca01d030000602c0c040340c0c0e99034424451544045030001d50790260040b07510341c4504101181d001c90041c4624a410194103030400c404a800502d50302d40760383d00a45920040c4140c0110341c03504032000303900040030f4010422554459840d81c1d156540c2d401c0a0a142c0c20701c5004c0040c81c2c00112011915520030400c803030a8941200f0003038656480c2c030008035041e600240b114180311400744000c44e110029409840040107000801c40500d0030b040c50b001d421304581d4030841c0e100e00380e1081c4002c0700c0450810703a6811500300310307aa141c4a007840d041c01d5001d0807c41c2031a040700d001c1c404010034280e569912800e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 283103525 1250 283102275 283102277
    0x110316030c0b0c030904021308060a02070c0f03020117040204061203021b01110307030c050a0209090a11010e1311071a0910020a080c130513020a02010e0a03090b0304140706050a 78
    0x1103010ba8076000480140b280a42d0304103150804c101c002014249a0010156a00040000b0f4000b41e5102001424404295030700840d158000a48106001420307031840081c007410080c03580000d107140d0018001d02070603a90300110800d0fa0380054155039441d40f144000304050343c00c08200300c41502d0000d496200e0381c01c40e400c940001020170441948035440c07551110050724000d42c80d20200351000d030358018501e4000c075400d204011501c0010b81f00c0240700d600511002000f8a00d030b0381c0e00d2922404001d18248554100608d403c10032600e80d0f180020301a019810340f00008680f04114050001c51094a40141c03c0322240310b0041c00345240c0fa03001e0340c82800d0071026509201440d0b4085802e038401d0305aaa8006641a40840c0741c800741c507401896462100d0081800c01030b5644045034508185070030004000d0380c04101e01c0c0e0040c1c0c080c0118204d15035140042c000710800d41da4054103400c5d250140300c16210002c03000804004a207410841807900c6442210003d44ea83c0c7c1e4010059400007035644 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 283104775 1250 283103525 283103543
    0x1806010f0303050901050d0608070311040c030c051e04170c030d05090a06050901030b1005190e0604030609080c100914011401050909010209040e1018050c090411031603 74
    0x60810034689804292a490382d0307454588080e410044030b0702e4024411000c1c206039160320008040c4d1040203a03400841c4242101407524046200b044101d0714001c010000b41421f200100c0401da034486c04a60400d4014882e5921030522802c844003140115008490662860b00380c01c07480303070700c0041c1d49603502d0411412104030200d0160212041d00400c1105500401b000b02c0a0040c0b9000341e000e4052420185030000c0c1c0d10301c50400003003080300c941d480032000c01c00c0025030301001001c0c0b0780c0500200c402414072668803d5901c01260042c4103610018248550320440c48041002034030881d1407800c0c82c08126081805046505802004d8001c022148a102d5003040d010615043c041c180c0455151100e80e80720f607203482c09000d0000310050100c845550708120f24041540c0d80c0c454500f0307078003405009083e40b01428060108a4641d11001004182c1d5100c2280001d9400a02a502603c0c2681da94405803224504464101100406258103000d01003400c009128010291000c43e03015440704 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 283106025 1250 283104775 283104779
    0xc0c060c0703020a03030b18160f0f020a080c01090206070804090513021c0c15080f07030204080a120507060509060405010f1503080715060602030d0b010f09181103180601 75
    0x8240e6104608009000d0b8100c0103030000803030300036804030700745100203401459140841d440c032a000740d40845200d4001014000d0110f0011350009041c004c1002c40e0500c03080c00940340b50060341d0340b0383d0201d0083c0106800901070aa10f9002c1d0000b580503540130705880d8513000e07903141c0b0482c2c070b800a000e5084498a00000901d404190b45002d000e0180c028040c030003968100c0818643c0205804401d881201c0903010010380070310303403001e0000c940701e0fa641d8500c01820818800d904125002c3e2810040500502003400f0394030300800c13003908041d44040320704801c000c00d003001e8806000d21f6002410b0b262602c4100140c1c254081481c501c80d511a800821810b0314144000b41200c18030080150031100c2c1c0c40040c1f000401d420700401c900c0b40100060100d0054042031803040d80e80c01d400910058102040c0200c5041640c061032540040900f0720b00104584080028108000c61103400c004400700f000001510342c06600804440070240c4c5410b035a4030b8000e540c0f07020b40c078080c84a440c0b40d200f28000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 283107275 1250 283106025 283106041
    0x1a0705100c091508060d11040b060c0c040e0a03020304180933110a0f02030c0105070f02151b1c09061a1c0807020616050a060e0319030c11060c0c06 65
    0x20340f0651004001c0c00788001b0310b1f1a45841001b2440505810940d100c002400c1540c0d504042c0c0031110050000307001400311642440151080380f41d005e086580940210000243c011050f501960400c015012500340b01c15030090240c02d0300306024096500901101c400c40000852103024034050412100304c5100c0240f2040c02c4502402c00010140820711030320351954410a054060031403a48116407c0c98007041210303027103540c2624000c0215503c2040041080c0c0c05200035489102008450305035403a090400c000b8552050103130342e8860380002120000c0342590000d08102c2c0c2d9000004010900007440c100004081010b130030b4414124040042090f84ac2100c48003522000c000801c0d016070420795581c2d40c064100041c102c2c2d1041003030003240650170680c00b4140f00b0b180124002c0c13114108074103100f0b080f220b0f442090039031074000b00310301d141e080600e465400c082501c42c600000d0804101740111180c08400c41c107802c540c05030b06d050000b07282c103030800340480c1c40403c0c1c00e4072550740b00c40ca0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 283108525 1250 283107275 283107287
    0x620040b03040308090c03070501140409060801020c0f0a0b0f060d0f061a1e060318030c071a0c06072102180406050102010b011224031b08071a0705100c0915 69
    0x1441b50307048d40f212a091005511030b50a6403500703500510400e0502c1c0c0c0b1021040195402c54200c18030716903001c04c1d0403c003800c3c200714200060758190042e00d041c80040d100c0840304e203c000d041e01201e01c0700b1344c0441c1c2d450b158105a480074941003104000c1b200c41d00d00d412009052184002400c20321013101498136071034040ca403120807149411000070706036425070900250b5040201901d41c07018810f0044060700d54240f008000d80c1201e4000781c0303500e9043c0b504211541c00c2d540148010386c2814001c5541541001503e01c3c1c020a40b030414080d8009464030001030020a40c024031f00281c000309280c8083c082e280c800d9000c0c0f503000c542c00e200f0240c8a000490072502040f04c5180000d600d885140030510280e0b02c40d205039070391114103944400868191800c84040d0b64800c8580074829036100380c07511100741e086000703030030410040d20007549417410381c04160a00588841022034001140010080104540e2484120b107040074400350300f100c80064000b942600c901d80d040348010900c1070f600c501c291 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 283109775 1250 283108525 283108543
    0xc0f12070c0b01150c1401020408070e1f0312050928050102073f050105010b3018030d11030402010f0f050a03090f02130524030a0620040b0304030809 66
    0x25841600700e601035201c400100d6a0801c1208403954204070204ac001d40901001025242500c0c80329010b0034401004590a8800051558040d0007940103000080c03908219045c4150140b800341d03154040100001c601c1d080340000c1c1100d4400c1c0310303c0654101111840310084900903000c1d54040c030764030b0340d104031340c00d203165005100540002c0080003078234106040106d11203100100c0c1001c8088580d1510308580d0203030060928100042200140103140c80c6441d512170143c000394400a542c0b8030040c54101202403c4681d5074503042c9a00d11480d0010801d55817202e956100a2144000520030720507030313a006460507800181000402c504490150101480400d072665030070745466415070089004020b54881220000c01140250001d80d45000a9142d0f49120510020703070b504005409221030003103014043c070500390750441c07480340b507401088405002d078211801140070116003d14103035a050005912444007400306001c0361500201008d035100d00d200b03441d20141c6840340c1628a0fa00c5500c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 283111025 1250 283109775 283109777
    0x3151e0f030102250305040b0703020303060906010c02150906090d060605040b010c0c1a0c06090d020f0708070e0a061505030a391101090f0b060f090c0f12070c0b0115 73
    0x2101c400744d2021551941c445400c0c3c000e1400074140354503012a1441d91380460801d400691012003400004d142c000e000d62341051003400c00b00042c100c0b513070109600b01150b440416500c5404154803b1a4444101b181d843c07010040601104c0241440c04070300510490241c18003031403400c0c618024039405004c0545c665034201d40950070403450080220340c1c41035220700580800d0702c140700303510214108115035401200c01502803c0d10400b0908000e10346030304244001e0b1142c2c0072140070030a10402203101000d48400d031008810707a54800110f04080c0c4406c0c1c0c4100564804081e448a22590040103140a0710380c84209010b000c2c1000d4104141104401002c2c00d0503e411402901c0701400381c5002c49071b0003e500344400c21100e440440c500f1941c10003015144001100817010400214010855000000722076100080038944045000920000c02d0803150500005161440350540001d0f21499034a4a8034040390b4648010001c00b4901d1218048541e82c51200012500d117400c48810316614102d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 283112275 1250 283111025 283111057
    0x30f060105030103240f0603050a050f01022b021207021b1504090504060902040c0e09010e0708040818030d120507020f0c190305030309030a0801090b06070803151e0f030102 76
    0x5034905c03103004101103800303c10095680419440c2c0055900030035006601800c080d04030b2442904089040030049909004580d10402c52920203c2e46414284240b06900d07200012200010030000024400d450201000c6440d02c0c0402100c164001200c070050301d09402c0d40070140003070300b090002d002662103103d00c0d9150f090000b801251460b51210340d010f800741e0300100d00c1e450b41760045000c03a40c0040c80f850000d08000561001400c024140500408110307054030543d00d001c6000a04515015100600e0f45000041c08119400c0802c020003001a008003501c41c0c05030f030703508090001c0c2c0319582850400d50508000a9940c1d00200e02c1d413001100550290a0a040762010041595004d2111203041500c8403000300100340c0070405103201e00560001140d80707640507035000e0301380101644801c000e5801d1400c00401d5882d2402a2414a0f0307010f140981ca940f581105001c20401d51480941c01c064a0307081d01052500030000b0084043c02625824150701e030f2141030600307034455031003201002c40d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 283113525 1250 283112275 283112303
    0x30a020a030f0c0c030620090306070c030908070f030c0806090d0e150c0f010b030d020c090403031404030c0c08030405011d0d080705100b06210624030f060105030103 73
    0x2016605407040c0010b903240c0300e4a040200d580c1c1090f400259081942ca003a95440d1410f40b00c01e42590b80c0700c06008480722203060030501c400080c0d590030300804c940100074061580c3c40426000d502c5031000b81c21044281e1b080340b600c514203112024001d01c400d5030118104040050081004242c6901800620020f0510042200c00c182c40c0000301d48445900306140603000350448445002500d0024103d20141c40f0208000100f10300b56021001240c1c480d401001c7e01c040032540005445050000a503060b900e103664034103083c0c00901e1b405829101040e82001040b00300b5500910114005124090402601d51903800300c582c0c80c0143d01600e40882c04001e81d030451400350240721045141d00a2403401801c110341d0b00c81c4410b82080d04c0440f0107600c1030101000c9408140281c0b640a08290348150a2000100c0d0f090b031012000244040f90800c46d03404102c3c580c81d010429000d505000505c40c40003400d1614020056001301d40c190748040d130b2400807500e10744c4a807040f203040301c0d002084208024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 283114775 1250 283113525 283113527
    0x2071104150504090b01051806130e0a0212030a08070f140d0908070b0114010203030f07030209010e0907020a060f06270f1104060e0108041e140a0c060f02030a020a03 73
    0x1081c100d07000c005407500c040c1c00040c55903c40c0030b5001d500c1c2c421070a00c24a549040b0602012081003220403508465201c200141c540b600b60807090040d603520b030082a0fa120341d5550a0a0811520010303402207415100070020500010051215002c69918002d244d07841c1d507000c8490110b45d80c1400c001480c54000003048560301070284c85c0260540200113124541c55a42e40301d03130341c49640c0403a8810510390040049184145401216141c2800a1455450b1400c03d46842800c0100650145940802c0b891843d910440b4000140b140c0541110083d04060501a541f180b9410b01110181c0c1494050070700c8040d140501402c03658407004480e6044d0b240e0752840d0f860b24091300e0051100703955003140f50602a907400383d0709001240120141d038803030500c0c0008006c0c20940b10100d041c4a451010702000540924bc4040c16400700403640000c0c90b214a00402d03071101c42c07151001035214a0081c24284803104403090100e90064445403000010100141c1e128014000c050000d47c005500c445c0c042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 283116025 1250 283114775 283114781
    0x3042906010c150606020a15090201050301090504060221180a0b0601140c03070c030309050108060f1c0b0903040503070e0115080c04030f0b0f07141c090b04050c1302071104 76
    0x285108161210002d03c5207540c44045400e141e102400581c07000300b8210501080e051200364564803400c1c02c0c00f080701d071600040c0c014070040c880e90f00340c56900c00000c1c1c1400610790503185c0781c03401d00d0000c4030008000c036171060940701d080d51124045542c0341e11b0498003020004001003055804000b0f0352140c2e4a84006560210f000a41364540040030081010310850070f10085c0003e82c400e2021121031825414020858505034020606115005081c0301c141e5441c0540034030f041504031280089000031001c0d0a1400421000c000c000700c005106026003000e01002034400c2d20019411141180c3e51541d907059400403c0c410781003203003c491840b864980c400c801c41ca0740300c03554a119a01c0e15076281e0395030500c0d10103d0b105a03500d140000c18002417004025525411100503e03120000c52207801845c0d00d10b12072002c024a180305c2d03289503954031800320341003000300c070f40c04c004a0607040c6024105942c60b80d404103082071081c103441c40c0e52200f03450244240c44000d5040b6503603885c0c0c1c0f00c400003480f0007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 283117275 1250 283116025 283116047
    0xc120a05040f1e05010f0204060c060e0f070f1401030c0f05030403170a02031603020f0906070213060b0309010506030a0b0105011b0c1401080c09090c070303020d110304290601 77
    0x61400e4030500680855010010f4000c071103403c4000d110315591a0900d10b003111080070000031590700400c01000304550104414022030740045e00000c030000501d0301e60380f510145002e00602400340d10000615840303441a15411035404609104845028000450072504c0c404032160226080050585e1208d10850146034045e101e410101070f03049081110301c1481400710340c0c280410f5000003c200040403203149091408a85040c2035050070304c1c841c002141c501070122400e004060114400c0190340c2d070f00b039114000401c4a001004a2031301c404400c01581d0046440c495950b082c0800301c0c0d103904000944070b440304c0c0c21149002e100d0342041b00450f0720b03940c031410500c100d0710488074130707004a0813051041004048003007046685080040c0058800301000300320141c1c030242400091040d44074025520b070720402000e40156650403900e401c0c0d000f03004040e00d41b01d109203403e41441441d103207a0b0085000b0750148082c9001881b00c804440c011400404c80d89038201091400b01d45194091810482 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 283118525 1250 283117275 283117283
    0x10605030c03150402030f07030c090e0a09150203100602121e03270d02010b0d2a080a0c050f04090507031202030f0d0606090f0305070e0414031903050c120a0504 71
    0x2e03e4a480000180076a0000d480d5122116076502c10b0007500f98061007100c0300104035007402c01c002e40c584060085000f900802000324103441d4403202082080c0d448101990002c1c8460440d2203082024807822401068001c1c4000341c0320759030012245940e001c0503141880841d0b02c0801a0011500b0503102e2a007014002510504a0f01c80b054041c0c44d18003134030b210f501d03010001032098000c803480080c252110000b4207030080803070040590100d005401e12244820f80f6150603160003040c1c5004c030011800592107681759005c2c1840d5002080005001c160440c0c1e803c480070310703d0100f814200b00456846550040c150f6101600400c00514803265600f4a5119401642d0500b0180707038226100e07900042111030f20903a150010b206482d0005900006450480e00510031141541e8540c0d54440480c0110b40b9103c4200300001c0400c050881001104101300d41034075281c0700c80b00e40e20034079001c071107240d203010900340030005408060010035a0981c40100d40c0d218040d8071600c21340d40c01050b000e04259 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 283119775 1250 283118525 283118551
    0x7020409061803031b050c060c1303150504150218040b040209060c030409052203030b1c140c01140f0304171c0f02030417090a180b1305010605030c03 66
    0x1c2e071008114400100401e00945000c6000d002002c411084091900303109400c0c40818014080e01c150000b85159101015150f85d85e030340c032050003140c0301091442d0b200400034950100b0050400c103550b0041800340d44501e0410550503c140400016400b030880b003030000140030340c00c0841d00c1c90b00e03400c15601d10388003800c018540700451002c01c040e903011003003030305082d40001001c01030304880c0d1051551140a20000425400d0001c111190000910801408042e00d41a0b184803550f03400300200c024009403081c149290304c075841c11150203500320754031006900801c101448c40d940150b1154000d0310000017098501803010b98040000e80014000b5a00c0c0b00880180c3e551f60f041760300013015072090700d0035044905118900d42005031012203031540d02407401442880f00192022400d248000155410540ca440001001c1440000c4682c481803507010404000b40105009901c0003a8600c019103017145502d07405076000042d0f603000e2041c040020340c200005a61002800d000e140c015030740e01160 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 283121025 1250 283119775 283119791
    0xb09130c09051006020f01050c0919091a01081602030406032004031103060a150b0d090606060815010c080405010807090e01030804210506040305090303070b160206010b030c0702040906 81
    0x1450450701c045072a800d40c00383e24401440111307010811016100c112a00038403c910f00850741e207115020b50004c40303004001d1002400303809414044c150b4007800644004001000038204e444840c030008050880c0031412a20214003111491254081c0b00403080d0000c61805240940490042c181c0c1e04018418042c01220340415240480c0100300944c00b84268002c810704400c1014100303000608840502c1349011040d440428240144104540d201060103071102e00d042022000782001c000000c120a14001010612a400002e550b0181000c021400348070b00c0c3ea0001503e18030b03c091806440e402d81030108008a40c0302e180840d41c003005a140c80b40702507039110001b0100080c2a00100d036100000300e802e10060100624030f40c1d96611309a001000d842d00f40d2100b40d01c40030041c1028040040c0058001100d03107040003180d1039507520207440100d6142c01000d40400c100210a24001401106d00010382004a001928003940c9403904a504d0070b0450350810004240003541100c01546039509 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 283122275 1250 283121025 283121039
    0x7050d0525052505030309070e13081e0c1501060c03120513080f04060e010903030806240f04050915010f0f020a1e0611040b0d18060501081b03010b09130c 68
    0x4854442d5201da1300458803407c0204009083c40c500d9000604161550b004104030b440c14107040e02544d542000a142e503075441c41c1d1000140810f2080c009000c8440010601c41d201400251180d5005140c4843c1c0b0072a6200c2070201c071a2402014050005024000703800203021140d0302558000350314000890910690350390f00d16043e042820706058420010904200c0d0725004154080340f06003d00c0c00c44141410742d503004e000034074043c0040d40100c45a10641c0140120101d900c0c480d044a004142e440d1107100c11548001d84c8540903007401042000046110703074500300c0aa0344900380c16143c0310094203075080211250024a41e01000b14418100190042224010007048105180c13100628500c41070601c8030507501b00000480b00740f40100010071010b0545010707618071984101c80850580c8016840c1a041d010f540e03000b0740213a141c5000059006000940d041d002a91816070100180c10181014201c40c1c0a0241580210100303000806c1c914188107800c8495214031000008141c980130 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 283123525 1250 283122275 283122337
    0x213090506040f0311030f03070f030e0106181508150712090f050f0d020304181410030209010902070f06020c01090f1211060c040512070b0307050d052505 68
    0x30b09840c8510305071034100078940d1200b441042041c131400118600841d145a5a8a80c400106800100404220342c2c07022107119401012980708a080244120340c0c9034041007001000c90f005c01c3e0001031404d1110320610903411254001c4500c0075001c1d11500460000d107081c50407000b01b40c0c0e8100540390508ca107000314903224940c111802071410700260b030900d252044c5003808610300410b840d0f00c041c01d491126580007007214140c900640006601c0329a02803008060440003650a1a141064040146166180c50b111040700c0c02220f14501d1a40e84000c0401244110355003d4070800d0f00e00280d0000c58015001440b005c62088000554410140c80d00040517005090031118516000060440580e0040c40001d41d0308840f00980320904005903501c0c020300c03581c843e26008105103410400075003424484200181000b080940ea00d03d07111324000c100d030380441242e9240d2450400400c42c1740001c40f105a040e40208031110106610505040c1e9142d081844547c4c040414008a0030000007200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 283124775 1250 283123525 283123531
    0x902040e0a050702010504050c1207120614060d0c05010503070905130e0d0224070201020c0304091e0209030318060910051c0519050702030915120907120213090506 72
    0x1610034400d40c101105440140c40d4090403440031a8100011f00010820100f14440c0d2200c044070742c000c040c4613a070500c0e400c04031942d108a48080d07281d190755060280341d803c14602000035107039001c007590380c05007000b00c2f03804103d001801c052041413043c09254058070043d0740062a504003200c0d440d6480d80000e0344c250160744d0130140300341c0300c103c0b0074411071082050b1100ca030041e0029089500d2994110489004590702a1685c2d100580106100900070340c101d80d01003051006503681c80341c481120001400d000c141001e418407030010b504645036028804da50410740028081c5250801c55130004103821000340d284c40c0d1101003080040d002d5900c0d05480c40b5440900c0c0c594a40b19005443c4103103402600e081c4004005040c0010021000c10a480d044440a812200002c0d25290504102e266025000940d0340120190000e40c62204590303002d010070981d03008a0401a960700445280c40b0501d500c01d0110312030395925103200510f0311101c0c5000101c040180011000c029440d41480d20000b9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 283126025 1250 283124775 283124789
    0x503060109150c02040f0e0d0c17070516080304031e031e1205010b04050f060f090405010303050d0e01060b042612090a0e0c0306040f0e10020d06060206061018090204 73
    0x541409011420170b805080000c01c1048010800c06850711082902d4044601c0a24104400505003004102d024480d080344006c0b000c4400e0344400079464003e03a604070068000c0c881c900c41510000340c0b503a00204a905807036100e058150b20100700b14020050510300380b811400d02440c0128051008113003540380003590130640d15254000c0044c00c0c0081241d0040e0800001c5c80c13010042449141c650200791810620203032584c980d500703d88219500980584c08543e507200e414240004145907000700034203512000c0d5402004001c0014124034200d80c524416505034100034401049025580100d007003c0f4040c09440000f149007010502d800c2c1186101c04100a000211b40032166044c441c035050050a07800b0f401a40030b007400904120f0720f001c01060f00d4812500c1e00b8107000f8034141ca4001d0300003200c209003252480703d00c1100079400b039040b40321320034100b614240780003400c24400100e076401034501078040507040c02004070450303201000301800d400341100d0352000039030f0418605c001e000030204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 283127275 1250 283126025 283126037
    0x9090f060a05011b080a051b010c170f1503010e100614060403031d06090301090b0f100b0904020c07050a080312071412091906020408070e070f050306010915 69
    0x120300e0422a00100681000b4108408444500040d0300c000058041841d004115aa202c2e10103002c21156441450400c0041103c540b00010880005400120700c4600d1521a52402040054000000c074412550355481003240c101054141400070998886100d000e400816280c1c03209019070b142c040429601800103a031a0700c00c100d51444100c0000c4200c1d81103c1c164902455030702c000380308555115210000d205000490740740c0740d860340d0480d40f40d14000740090220111700e041c61040240b08075144002d82c000e10000651030003a426109050b200305803840340c1814440750900c0001d4000c0a030300790f0507115200c0081215650713908480000d08401006640c1d8242007541b403805e030300003d000d901c20f020003690034140c07484055060f62000e00c3c548000140c25518904058a07106141900c0198050003011100601165170028001e9655060456881c255a8001407207510001c503074090020b0808034000584078481e00003103401480524062134200d484100c0c40d1440b10343d039280100810b00e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 283128525 1250 283127275 283127281
    0x609070c11061215011404180b04050106030507030b0a05210f0a05071514030a0b0d1203020d1d15091507030603150507050f2214010914130e0309090f 66
    0xa1081001d05005428a4191228400c411b081c016900035802085902030501150020120721548138441c440b40c0103000340700f5542e41d0f400c050010324060b545500003904041000040d4101802c50204441c3c0c05800c0140400ea0f020882c40e00e00c846001c0c07004180110070880030380c200100300300c1c582a400303803000d0702d4040c1c58020102c40c0184550b00a034140081348009038001440501038a9010705840004290380c00614005510426051401005a1603a089440c07100c2e03455400f51420600e104010418100c0588d030001c154602051013160039401907960540708c80740425010b4110000c4002c1b24a48038103801c4421420b0011100c440c00a651020100b041c000004000521040e070072508205a00341040c0080c6203210b91045001070050029050324904910703590341040758204061082030340d40f16400d4514456072401441e0000e540344d107001c038010103014104540c50340014030700ba0000d000000000d003c0d0141c0714000d4058002800382c0266503c070054107503c15030038206c1660b160300d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 283129775 1250 283128525 283128541
    0xb0105160b091005060d12020f16051801050d0609020315041101170714130503010504050f01060e010b04090b0103020c0f010902011d0a091107051c14030609070c110612 74
    0x240c50940f051059030500c0103016140c1c85440044400940114044554056584051b451f06148400c201107174814410403048180c03185c6222820f90314101c40c0c142859603039a1143c28000b201323009407680203004021b02c5002424941c010301c0e13242c1c030160071b4518103002c011004a503010f0843e015540b443c0300011008441d030f8014195881500e40c41c0b241d00700c6007401c0310b0048c00c00010003400500400300241c17107540c01c41c1940b184001040014000e0050749414a801d40c1c8a000d000e424440d15070a040010400d6108110020b0603103004045c4035060900e09442103001c0e010f480d108a0505608101441905400344004506140c544001042d411107502c001003030203240e500f541c410803034442c8841d2a50341d540001e0308112040a070020030347e02441000e25004c0e100c0d901c4001c00034483c0041070f01100700705810103072505440341c9801c0403810003004034036424841190000d900811080028108501403101d07030305000c1c0969041521030b140440031401c10392001048a1529084804120500e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 283131025 1250 283129775 283129783
    0x50d03090911030115080c0d0905070e0108030a0c0818090406051e0114010305100b040f030501110403110910030b01270c0801030209220b0106021b01080105040b0105160b09 76
    0x7820424000761556250a040b82a82110701c4e401c117040218440100e01400e0515040c0e17102c540d000070f020001c0742160710702503903519403074828047d0b130304940000094164404030a80d550000c00762220010307006036035a0245d403948a1070101c0625260482000740c40c0c0c0f1000603462190380301c2c40300091107003481780405a8944c00950104080a00324006120421810b90b9003020240203003000300301030311980031203441407490f5003000462800200e80015600740f484036180480e801900200000051141c070000701e4401d40c04082c002c014000001103032810110741175903001c02103507082848191240d0329000000303820390042c0b40d84040010f0f0985918545540382c49000d00d003142c1040195640000034148550500c0044d12038681b4100240d0040b0040d410b00455044002861035954428500302020340020302801005204001030848000b5024550304500b410503142d02d0116840d010421000e44166400c0782d04100c2d0620800075804141030340c40a90600c54001e1100510388004c0b4a0310b4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 283132275 1250 283131025 283131041
    0x6060804140607050a0c0f02180613111614060106032004050f040513140d0818120d06180902090c030c04090218180601020c0d030e0d020109050d030909 67
    0xc550451400d0202c43d50300700b0100c5160300e20500b0003840d11a540d08041d9850000c00b400690000e0200f840e01080c10158929580700b50700468000e41000c00308007440c0125440b040f0800e40390101000303a0240b4845088a02202c144141105503100c820b240765a800c0034420381c4100c02180d201c1d00302e2007600b41ba0b02a03d00c0768804802140741413038036010000304080e8540d0805401242ea40c008a00090442c040ba041c4c42c98014122128405410004aa07a4a9459021030016050102003020321144482900c0e94202000c01031580801140030f5084641c0402521602940c0c0d50f1030009884224000203c4501008440003035160080d00512812110081501021110801c00c220358040028242d80540328050f400503100e41d41c80303c01c000c40c0351920400350307031210007004560350351080e40500d04d21504080e030a95881c40c0c1d101c0d0a002c2c440c034144074000d002c12600d00561000d0305150880754003c500514240e5803060759440490f8501580c2101071f000950310f4101409002800d0040502c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 283133525 1250 283132275 283132313
    0x1090602010e0c15070c0b040503061005210c0d05070f090203100317090603040501020a020d030209030d0e270f0112020109031211030d06230901210606060804 70
    0x90b2400c0e28000c0b030f46502503290f01e680310312009400004110303d01403da0f185141d000c0115400d60380c031000d2a817119086441620310138400c003170015641c0c03409280240d044840143c02c0c3c0803c01c01c0c04144003064500741c900242584910039104a2580c2c6504088003001e001f00d01400c0002c2c240140c1d0302d5840c8841d00091080307401002441310454041405038201d07074104250210043c02d04503460102d2180c0902907910840c0401440140903042d4010100201503808441b02503502c010164240e014502c4150f5040c1c01042010f03042034000e03020b8002e190801040422803101c01c04009104003050228079241034007042c20001001140b00c065405048500c000310b101e203159a000070115000f0340801010743d8240c40001f00c0c5180500c07441c00c1c40c055030400b5030380c540030800f034084000c2031181700341c010780ca01b42440e0305441c030110648421010030240414489a082a2649000581c5a1b6138052a85122900a00494102d00c41c010180140f03039100641130515080c0503c010300b81c071511031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 283134775 1250 283133525 283133531
    0x301170708010b030c060c010e0109230d050405060c0c100201090b13021f020c150c07051f0c150207060911061c0b030304030b130201080c0a080604050c0d1a0109060201 74
    0x30b003d540000d000001030104446d5981d031a007003004240e000d01080903440c02a5800e090440080200c040100e6403003065540040520301045540d240d034885a6030401404a9002c1206004d1402c18100800c80c0101101c00c58000312503850200312a85c078803801d1170340184d64070039214080104181c1206d4000d0400b0b008a50f0100b181d0300055103441d105080c4d00901800300050780d0b0b11034001c0c0207041c10510020300051040350081840806548074046002660152600215840c038105a03150183c129000082c03010541c540015035410241c64416160400342e00705d001c605041e02d0004010321440340c200031448080d00d1078950100309400104521860b018404114141040c3d41c04554080c10120007145043c20107001c01c1c11440ba0350805024a90b00d0010800200040303030011900d00d00c01c1ea0381c82c42950b03440b2420342c098054024607200080f40c59000c01c44929203a000143c00c800b1504070103140c40035400c2d07200201d415041c4024400c42c1123841d075040070741c1c004c43d9420050031316000078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 283136025 1250 283134775 283134791
    0xf01080f060108040c1203090e0c0703020a1518080a17060d021009050a08030c060606070503073c030201140618130c0609090b1503010b0d090503030117070801 70
    0x3803400414001c0c2110304200038280082d040c004d100c0304200c001c203914880f00c0c09254241c1402018803446001c0c0c2c0c0c21101b0580041a01010302d00102c52166030154050000782c120381c4e4800c0901417404402414240c1c91300d00e0001840c1c40c400110380820b20031038265a0b100078403a4040c00038400078104400c20307640042000b00c15124a104683e6981d41107990160b126420302054031030032a241c01039504405005004226180000300920503407000c14103c40b41c0359206001c0101c00c2c0300d0000002c01c242c10a210301000282c07003c5480758004040c201500501151160705107041d01003080c9000d00f55245c41c0308006054082c41041d0440c506040c0080440c940600426210315610f882d0356051151940000c594029500c40010300c1075100207214010755550710004c00d40a000d001c1d0440d620328000c1550410700e0940110b4a80307088a840e25419030317180034018045d5400084202c440d982c2c440d40c81000203072051004601a240d09c11201e844610700c0003890b450500e680e08041c096a00d05900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 283137275 1250 283136025 283136041
    0xf15090f030f1a0a0e073305190c0b0f090d0e040b0405040c03050d050403150f02120a02031f0506040e070c0501050403120f29010504051e0f0108 64
    0x100400d0300e030030104645040015162503582c3c059807901c0c154120840300c0c00e100e00d07440103030017400c0008001c5044038103181d190b4850344e010300c0c0c900040303459006401c03035841424045001c60700019486030520780d0402902c82d01e1881c890400d208e881d0000317100422180200b00c3c004181c0d94126a031103102c041c4d603184c40c035030444c0c1c1c0d03840b0001c0c00002e000b103090070400d040e5544d40000c0f11444011b041402603003007901d01203c80c147c2901007222540502c030144540a40f04000f9a4110bd40160446000c080c228040e50001c003125881d06c04955020001004030b665040c0c1d00c03d0080003003074030050b034910f01515440681d000301d01c2d044907000001c400812140d640c0e40c0645081d512040c0d480712040c0c41e108400d403101e0000d2200280305500300402c010905400801c848010543c0300d000b80840c0e0b45580c0d1100844240c0170360540e21310800390401c4244039071302c1c401644852040c10020700d002c4d16240040d18040642080b60452486c03000c0380d01250501e8400031000300300a0900d80080d040c503600c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 283138525 1250 283137275 283137299
    0x405070c0507030c03061a03070905060303160b01030b0105010815010e0d060c0e131109042a02031207050909070804050115081605030601051e0d060c0203090102011b09030803041b0f1509 82
    0x224000101d901c03000030a803243d3701801251403119880c014012028000d01d040c00018109100903600704500400018495014142c41031003080206551010715201a0054030003d08840655070441e0000a051000071981e01c20300d01038001d0b54442406140c40d00c410000000e0a100028a07203c3c01d09206600d4020450180d40002108a5000c500f03c4000440c0d84500b404600e03200c020f00c200c00010040e40c64001c4010100f0850b202c0440440e955542c1060b43c4a2244031103254110035881c00290106114614551f0030500c6400045405a104440f80090740000e07003002e07219802c24110403a14121014003800200341c281d0240900c0c0d894000010440340d045144ca0f441202207110300b010f5543e540201400455001204001103003020380d0003075994122040181c0558a0203900109941101c0c0318080403200c0341e40c0d0030bc002400c59945018036000617004481403c4148903c1c40c2c070805242c40b001c0075182039144000d4451811014201400c407284542060000610042c4040d20b0744c05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 283139775 1250 283138525 283138529
    0xb072d1d040902063c03010909050c060c07080c0d0b07080a0e01060b0409050a05090c0402070503042d15020c220c0e040c02010203010b07020405070c0507030c03061a0307 75
    0x2005408a48203044003040180041c280025803102c4001180d4450b00da0240c903a80c440141810ba100c0c5802c2032400040c40600c1d5401c0c0d10404010510041015405036000120114414000d4541c180c141c0004503d803500300d0309040c8103940000e0001d0143c48410002c15042600403901800702e2440d80c0c0f40c0000d102c0020348140b00b0031405100082d510301681d000f46280020181c0200195135039811542803580150082042040c2031101080501170180590343c0101c2c0c00e807000d4042c2d018400c2c1004001d61000380115400d001c1400005040003600c84521200801e07004003404405443d04420480c1031583c00050403a41c40b44001c0c0b90b00ca6000a065890301405c0e01d03030144031622078100461580740000e8103003001c3d041c482c0311048039a1200a03030240c3e070410b45003404100700c507040903800d0740800d004405d112202408903602510749508810b82010103030500c0800050705490312414241550010341b203800f01540100100501807040c1004210a4130829030700c00c0c2c640000035101c8004c0c1c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 283141025 1250 283139775 283139807
    0x60e0616031808060c0405010e061309150e01090501030b3d03150b030708070305060a02211302031c05070b070e060c0708071508220b072d 61
    0x1040700410b444070340005403102c941121601c1c50a2a05450aa806809200c0c001480864401d6043c00c0280a5030041d10303542000465203402d1880810040c0744100100445103090800040c500c01400e5581c0d0103000c2294001c540341d030440c04e201c1c1d920440a0540002150007000382c0300d0345190780b003120a0441001c0f0314089584850b8880c403030130304c510382c1000d400a01d003400302c40e0b0b01005560046019900c01d509403450355950710802d41e10b4a1a600c40546140c0081001401c6011030350f00420f0385021603400da0a0914050030f030300c3d148a90444030000c824017050000025460108010b04850400c140d440342500718540b00108a802440310052505080d003004c00c10042c05649580200200601a5515803054405003543d0300e000f442400c0b024003c90170007040041403440c2c900705081464640d20920b8071075200118885681e107204005502c2d243c1e142400044140300a54010012035031200d02c241265003214141080c7d0045090000c40700030604502a40c00102c01c45080c00c01c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 283142275 1250 283141025 283141037
    0x304060504030c060204061110050108250b0310030b01120317040c080d210501050a032307060519020f0d051806030a02220b0706020702031603060204060e061603 71
    0x15901c2c1c1a11a0050880d004242a00215000c682070350b00c01c0c81070200340540011605124502100e64080310020f01840d00e1a4100689244007050300707500105540038007030010706881d5074500500880f504156003000e0408000101001072001c800c1400340035010701c0d981928072421558001d00804001802c1115000e21900014180030f50109910014a501e1080d105915418000100000c69658040d2060b0381c204030400003030000e07845401d06840002d484251841c0c20340d02c0b1400a5074454490303100308880e030381d910100a0307402d2120000522960311010f88902100a400040b001030444450455009401e80e00e032240d03001803005070035140c40c241555036289d1164620311010720b044d4141d8000b6800428002c8007031495005202408100c0440003e0042540b510300d02c0c41030a20548030520024042d81c000300301141d006110300740c4010101c0300c07400040b01143c10f031420b09170300039583c543e07010a0130004a500030700d08a000003800c80d20185456504514580e20340140b820190030802 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 283143525 1250 283142275 283142281
    0xf01090b0d0f06090c0303050306040e0106030b060f060d0f020712020c01020d03200403050a0b01240807090e10030b0105190b0a0306180f140c07140304090c02030705070b0403020603040605 83
    0x10710f80d800982c06036004031794900032a1312800c015109510558240380100e10301354a043c00950180714401c10380303a1080783e050594444a003001811030041c070703945a02013020084101c00d003205200e40d040031505d41d54096100c21490034040701900c41c0c220f840066401450520400d0303a800700d0b0fa40c041003040e040c000b40700f20071099106203400851807075028036140044d000c010301c44000741140081e449a0340e06007003680c0b1000d4900c190110010b80c010906441c0c00c04143e46801340d440c05034030000d545002d100345039030340d1043c8140180548a0100e8902c1214081c4107010082868a000d0403095652611070941008008800d50709440341e070203440804900300002c02c0c4240c112030300824425a56442030100002010010807100c448400c0035450203d000c01f0010142c4140b9104424141031282000d4140d1a444c0080790768441c0e003002400200408107001c42ca40c071031186a011180d0041d44c40f4041e5241c09841c2c8142c6404c151030000c4c00340b10410040e43c529084aa00607032110020845031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 283144775 1250 283143525 283143533
    0x60e04230711070603050609011a030c07050309043b0c19090c1e020706080403081305030c0f06060411071704030b01090f0b191a0d0e01050f01090b0d0f 67
    0xc4011502c00700c40c0910b9000080480c0c2c5904000d00400e0125225020f99a90b0445c7c0005074804208000c04a581440011005c0040d00302800c001405070064034580540c100014084942c0f59462902038000c1c140e45801703580314100c48098510320b40b408900c01d0742d0f151000d10f80c0c4800c0079820368400c64202e11040c2c0c008042001d45070080061600a11850164210141146668222401100800d1049604c0503403002660000b120220f890b00c2c0d81d00d40322501c04075110f00c4014401005503039038215400024004000071320391081c40e0340c042c050041c41241098104080a000681705505200c26214000c0310383c002c44d0011980040310103030100f07402d2103508070f90140342d001401c1c0d0030701c20000003140780e010b400c2940c01c2e6200800070403201c48010204004c2050010305070921090b0140c0c03d1010000818840c50702034464848681000c03120840c41c000c0d603c0c03500c1242c500d651500c0c2400f000802404030316004d003501d58010704c5000644804100c01d5501001c3c081c1041084840e041c0c248 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 283146025 1250 283144775 283144787
    0x5091c090312091a03130206030408120103031809050603060a1d030c16050d030905040510031b0302040612050319050d020d0504020306010b0403020d020609060c0304030c060e042307 80
    0x6540c055a00c407002660410054866807040c40707070304c3c0a00a00002c03500003955401c1100d00c191302c28800e00340401d149400344500c0781c0004208940d2924104040804c520070100303428001c40c0300369640c00648041e0020609410340325848150514203140c02e101031941d000c214164440120100080d91250703102058030403000c4100030070300034000002d003220301d078102043d4690480c0b000300c2c41c0486541e8400c140300c240004040e014000546000062215250580040790804d1407407100320b0945489845541d01c0700c03828405180410351500003001141440c0c043c85008162140d00c1d86440311032903c0d41d1341c41e4401d103a007040c030700c1c081034140100e02401107041c2c800a141c0c0c01d50444d1954003441f01d2100601c804c0c3c0c0d060340f02e40f050000018140c40607a01300c409482d4050034070840d0800b59828070420b900300d82400c6c0d0b4003420038400c4004010080018100940c0175100c54207030240307000c2000d0030b001203082c04280141c2c10003880b44102c011002d1001050b031160302c990340c1903554010701100c0c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 283147275 1250 283146025 283146029
    0xe030309010b0f15250b010e0f18060414010b1005070204050109020322031e051b01110406110c090f07030c0503070e0909150c30040818060f030403030f05091c09 71
    0x2c103295100001c20402d1030314440303d1280274a050780210703d40320f0403004480c41413102000729080d0300c0140098005000603000c030500c090f00303c0000c00c00041d90400540080d80d500511000a04042940f4080d45001c2c02003070f00405040700c0c214690b040c502c04980d11a480008030040c8029640f00c99000c040c847c030400c1990354001060000340050003400204603501c9a424403141a14060b1041d1543c201032003611348904062241e940340070b03c0d140c002d48000c2540c4100c6480e502030704003074440c0354590580261041404241c0c4105074542088050103c81000c2c0d00142007010034010171240907044952014040c0046842c0d640c10396400803081e141c80844501c0611640101c41030013038412940c4064400e4200001160010407501183c001b4145030400c0383c0701a2102c4000840d000c16003880081458458070b005180c580754009011440541c0201d000c505d10500000c100414194540300c0c824800b14081c42c180020709151114954410021a05c041074441c6100c480c544203010b0b4980d600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 283148525 1250 283147275 283147283
    0x30e010617070302060f210603012a031a0d060207020111070b0421061a030c01020a08030a022a030702012d030506010c06060e01050108070906050a120e030309010b0f1525 75
    0x18014800f035260080100c22364817940a0340c24001031049410b60082d17100c903004500d081b4000c034a801c101d0202e014100e505092a600056010020b909495140780145424055800035a07140481d200040c15003d05e610300c0c0720181c0042909208041d800d4080300c1c00c852004030b983c45101e0100c01503003d503a006000041140c0e103840e4018031940031303100185080e9842101541c40c0107008000580e11002041c0c80102081030410000d0303c403507600c0d400b07000c01030304110300e14020b0144d039608d10f0a28904d8001c180410303070012414404569000254207400f009140c0a03080d8410300580e1402d00e000000061024907407120002500d50340704100d400d111680109040c49040d55800744200ca2203000c1c00b4181c00621604001020b00d40506903140445145980d0701d4a48118650304888441c041006414040e0701d48015054454042000c0c60203035200500020f600c00203441081111002c0b212054000c00d0510200c1910000b55800d8602c4c042e002000b01550040c4082e510500c1940520014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 283149775 1250 283148525 283148557
    0x90109080d08091006030209040b04140a080c010c110c0d06020904090f1403090d0f0c030b0415050105030f0c0f13150303030507030b0a051009080d030e010617070302060f 75
    0x90342d11007000d80c0140ca60000307031229002081800002e952075400040c0d0021100c2003c200018048030b0590f6025004100310012014002506400c24403010815144d114000c101c060300700400384100e03003a00485003001c6400f010020f100680b2088203c0f4124401c0c12403022500601c0013a030100c0728228070082040040652078179045080c0404001d042d03030510304a4001321105a4000104d45d21030b200101404485038060340c960a89040a007421181d0105103e00040050b4804070101d0003240300d1341d00c3d0069505e1042180307003210300503440184a644101c034082003402012982d40c0c4600c41c2610100d0000e25440081110030001500e0528540c0c0780400b0f0400002043d0741d40000e4a1103540c0900c107540740c41c24100d094039044c2c507040e0350000d00300508002614140b40441d42c14401401d200070241d964030307161030a00c0b14440c001c901194072085800084a001e22901018044000440f10640d84408a1542d116150700000b8081c14000828104002101e82600d80550798801e0003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 283151025 1250 283149775 283149793
    0xf0f0a0e0c12070f0b0301060816020f16091505100e010905130902180c0906071532010b09152503090b03070c0204020a03061a0703140301150509010908 67
    0x180c0c0c0c2c2e100503100e08541356251510204894907004200da0499403160b980340c14507103441848088041c00043c80b1029481024007100907030000303200c1c40403188940c2004c40d404d189403454007000d9803054200944201c58041042c0000e964840c4034045010040c60800842114a0010383c2e81002c0c03a0403060384103079181154441c2d18280e80202d48014030a43e5034044c00c1c40402c0d01e0520504042e01d00d01046441401201c4250800c0406890454003030440648481d40c19124042203910307501c4208050a03d4444080807002c140021030300c8060410b9001e0300f59071410540000f90301804410074843c44a0709810384070007032800140c5001620700a402c280c1c0700705160710003000d03106038103040b4081201140002035619444064030b108070780540f510035440e8032550800000b5445142010f09140d540e030008035404110540140a4003050608150b640c01c0c5824050050203c0b07a0116211070f90810052190b81c14907029141c0185490905903280c07220400146c0e424006600504134600c101c44d81 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 283152275 1250 283151025 283151059
    0x150510050d0b04030e06030103200103090605090f06060f1318021e0102010f0e0a03030c1b030509090c071a090102120c070c081c050c01020d0606170f0f0a0e0c 70
    0x140b1402184251074600c0b00b40400c405000141c0070912014000c80e03c40c0300b071003550044194a414504c4814500043c042e00350356111800c80d87c09940515803503001c3c9480000c200d008225440d00005c08841c3c4200d48425180002d00c0c1e140080b070248101303600d980d12382184a59451140da132560b03009040201d400c05107021050101d524080c00340c015800e240701c84141441f03a1003555126000c1001810502d40b440d1020741c050683c2c000007104110f020038044a0441c01e0340c3c00705404e10b22a40d0780c10b5a4804544c100414584060200032641c40200302d0103000984030502e00c0d0200500341c1d0b0034961640c500070a6802070144850491351003004a04200b0320742d1441d401020818030500300c01308000d131903c00b540e42e80d001203c00b8a0030303074691114040b02a030240d40070704083e4242c200050314042c1030311000020787c0d8880e400301d40072840015010ba604003410032060760003400caa64103c03007840d000031403c1d620a0054a00c1408031f580707403d041c5540c4030138000b03c0d2600030003503d140c00c3c95006e605 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 283153525 1250 283152275 283152293
    0x30c010207181806240e0f01031202280308010e060d0b1e040303060e0a090b0112170c030a120b0607200d050d02010c110c280f0e0a09150510050d 64
    0x80f00242044d080c0000c190244407101b114000d41c1c160000c144603a08664405180030103006e600400d500c80c0c101f40117943c00d0021020b907518103100002181d00141741c076024000c203c060300200d40d1a0a11004c016680d00c440d103509501c00d030085141030071b5841e400c860b00c41c59403c50441c1c0c803000740707140104000d06806400020483c1e5409a0445c920350303039004210700300c580c0014001c0c035490384a401084031345800300910980900440c00444043d06603070485665038071100c00b0000c65040401c40c1d100054000c1d10f4410409103025040c0403054084000540074031894400802c84003942c0c100c104140707030b50300c0c1403600c0031005004407642001c5801c0407650b944050800030015030810240703c810b94410040c007a01401c0400081c060075400a0401c00003000503181c00072010351459026544412140381c0350000e001c0c8071042480c56062108003815840010517070b50046081c4658840001d903050704090044130326110008990b104c6c0f2820010580503a884261700c514501452418002030b40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 283154775 1250 283153525 283153571
    0x1404032d06060815010e06010c03140417010e24010902070812190c0f1b03020a0b0109050403090905010806040204052703090f150f07030306090207030509030c010207181806 76
    0x184c0b2075060783c1e80c0740171080a0786400c98005000035840c20041000a006203c00c0003142c2124074002e00703042c0c448210400f0f08859400e00c03041a03444109480d040354040c4100ca00d60080c0c02c503083c00510000d64040101501881078076192507000440ea003d015941080d114881588003010fa568140040340c10f801529522081400904e81454006440c2c010303c00040b444415456180c10507030114521f10680d405204140c007913000786581e103000070324600c5101d4081c2403544000a06c40c280b80c1030081c5046242d07000f00c03400a01d850018841c0a03400500c02d079002c0c1d812a000704da540c5e1413004681c5400310002100045c00b074056211a840107021024117100a0b0a40d90040e00908900402850b19010404000b10000400c50f0a16100e0054010b1040b1402410041402030f40e0b120500226031144200740c5c0081d10108102c0c50030700c1d05015010b4019001d2000301055400e0611075209403080c0660480d0440d0b86034080340010340f142c50491507080c2c00500801a0300e0031034a00d561105c08403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 283156025 1250 283154775 283154803
    0x30705011e1d06161403040e0112110303040603060915060c020d140d0f020d023903010501060305090d0306120b04301404032d060608 59
    0x11040114165200391a68070501a400318104030550312004103481000d1407010018104503695100d289903166200104500160700d49403007000100340c14190b10542c2c1030701e07038001242c0080008008911005c40c00c18151010074014044540c2d10f49071020303074004440e542d503401d40004030f80000c1d07103030b015403250080310f941d4403003440b0060344d500e510070045216002d0384000c150031000023000b50410402e40103060744035509100344246048031403032a100d6903440c5000010b00c0d11000700700695061003543c160300541d0000f4030b007800781075104c481d014000591000b0007603a00032041004a2240701010140c490140081129507140c000040140500b16120034941c85032400421841e84a4403c500459240c01c901c2c1c3c50301d00895503104400c42c800f80007500c5102400e001d031003420910004010f581d0b440304020154800903004e024090b02d15941c51491902400d0008101151141e005c0b000200c2107082c0d280e240c04504207900344020380c4020054420342ca403107004960b41300001401c514240f56 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 283157275 1250 283156025 283156033
    0x20f0616120608030703080712020408071a0a0807050c01060e09070609060203070521090301050f0a05072a03111207020103050a1e090201031b0c06060605090a0e0c070f030e03 77
    0x1900142e844a1003114100e5000f0000305000c248560849500728400703161001f8034030608a0044180c1c2c2160b0030402c001c1d0848001041041c05407107006421300701c0760007030b6803c00060201c080e00b1010028420410321000040f180071010081d40440040c02520b03074690b07810304045aa0b03d590b100207000d07500100d5003201000c00c0b401d00000c140ca40306a40f00009100c0c0103d9540074030f81c8803066815810081c074061003041c000340ea003801044c2c80794580b404018410720f0100c4104e002c4c4d5a015040d101031048000e0342c03c00704160710495082c4412080d60020048002d8981180c00404e0301c1443d2095004500d400140140e4503c020708482d8000d82e0280441d0325000c07018030407034190804d200503c1c0070210403001025050b07007250000034014140013a007041e0501420541002d400341800006240da2404810008288108405050b69141c040e08100310301000c02c0c6003143e01e0080b41d0722071040c0707000600340c403500c28201ca40f00c0e984041107410781c800c02e20307000e8040342540000ba407190103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 283158525 1250 283157275 283157297
    0x3030f1815120c0906040f0605180f030a03030e15091606080105100f0c0203030307030f110f091c0c0e040506070e0a09110d090804050a14010e10020f0616 68
    0x820641038499485201601001070303101c840001c2082c1e80b20388113a64210100b4000010b0417a0300d4860b1900400007a16059521a801800858510070180b140c61195043e401c0340f28207520001811102207915080c000340d410005c2034190300d052814035041140c80308a42c108903103888040b9521143c010960282c80c02c3d5600d81500b40c60100b801d0040a4005d41042c078248102886506810340c032801d141807400f8520440d4010a0450340100c0b0403001190702c0300b292540c03413030040c85440d1040c04c3d1142d1050604102c01d2002d01f0314810749448030300c140c10094240f036044600c004e00c41d084c07983c4a02031701d480c113030355002e0700800b800212070039202d902032600014816402204881000b90700104950f20300e81c1450111001005500041551000c091051aa04041d42e02c02c2c98070042c06a0b0300191140e2501c4200b02200300c290300030b0022050814604c80366641c10442d8042092003c8070340c107a0002c5a10702c00c0f4030b03003c10700740b8207100d51090005101c4c21500e96003c9601e201c641e0740d0380d407807228 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 283159775 1250 283158525 283158559
    0xa050d0203070f030e010314070e011701150305040c0b0301030302060609150a05090901110418060f0b030a020904020d02160201030b060a081620010501090b0406080c0f03030f18 78
    0x1c0100b51001d0a034001456104000034410500a40d210005040024462a41c2a03100c6a1400e0032100c4801003441207120385215038100001000b140d0181d03450092a40c10022201c0c40c001024005005058580380843c2c20021500040310151035242c0e6404d84070b40e500d04000755074520581d00d6a00541d400c1d0041800c9039248210300b17800c403c001c0c1c800d080c9580b6100900100c80c600415080b420b542e0380000880416551b40108000c050f001c0358524010214034400b0120380c01d81c2c0c841c600000b0031036400c1105490f0481a030341d000318000c0340140c1303a03128000850b0183c800c031540c2007040761001500380c5e4890500020000aa4002c2e601001034440c818217001c02803040340403610100f40e4007030000b203035582d2642d0310a401007110b2424a070150004189440252a45040b5000c01c0c1d4407800140082541340c885d000001c1c0048506201807890f255071540c03509803a80c0014080c40e401e105c42c0e0980c3e18208201d03058405906103030b40d514410b8007851300d449001000c0700b40c420000503800f00008 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 283161025 1250 283159775 283159777
    0x210f0f07150b0a150f02010b0301060303020c030d02010c020d0c0224070605090c060711030c0a0f030302011a010504090c0c15020a020601051503010e04050f03030a0b090907081018140a050d0203 85
    0x540c09542030034200a504c1507080c0c0e110441c101c03a004c01c5649500c22083ca40d00c0c00c5c06035038000c1d840b0342c0090821451503070170141055000b00201007160b00d0b10151085075540001c001201840a0901c9886d0380800d0000c2070031882131516410320781200500900064624100605060707001d900c00b04140d0321046070090f2070306803c5c001d442e8812400c0c0b00324404544000890440680b008045400a2020501180400c45a94040700c00003210382c004105140c0c0a00868a80010411040300d060007000c0c0080c04501580c010b0500042d175800c06604001d0007468800714440d00b108880c000000300e0b0448601941c85170a400c4014002e2707400004c0c7ea42098440e103012141c3d088806800c42c2e0a0056400206000400549981c40b41750040001101e081c4000c0d806080c0d1000c1c0403406010a0041c48504c000280443c0b0a075440744204211945e00451511006141d024001c82c41ca110100740000c541035458000d032140002d841c03803d03c4140c000070160070031480380c4165000c03412030b441c007a038407 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 283162275 1250 283161025 283161029
    0x1a190b0d02030d11030702090403030e2103070f030e0105090c010216050a0918060c120501290a0201020903013303051c121d0f210f0f07150b0a 63
    0x1079100500f15054107026441801501c101381c4112410070341250005024a481903c0a40100c0c1c3ea90200700c0441c0342c00e01862101100004c00c851060303614802c0250a440018072200070400200f207031302003151080d008040da80502030000d00c0700341400700390180c460408107103050261089050303040b10074011084c408200d86000b480420070310314100c1003402a048100c1e240d001180400c03c4840001d0b100d01c0307501d03070f50708842e92841e652224a117501c40c2100c1068001078078070038080018009907421203814884003611040c050751103900020060340640078141000740d15509181c4c4000d210014079500c01c400340741041494820161f01c0c814141e84000078080a400e58100c8014400141c061b15000084030645203440d104004032288031034101c2c1c281e00c085c81000c28003640c601000c3d200400c48202c505543e50040e185c80001d100c0b900518104c09210401504c8021807400480c007030b070000351044000903841d0139548079130740e00c2d0503c40c003210700a110121350301d04442c04905007410041642 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 283163525 1250 283162275 283162279
    0x2010c020a0f110a0906080d031812090803211b070b06011709010e0607110c0d020d080327011806050a060302131d01020c06070c1a190b0d02 62
    0x4200c8441d0300d4800c0c01201200b030aa0701c204401204074450b4865021200c020301c100c16000840d2410000418240907110b501c01041500b089a5070307259419a6100c1c0c1d203600d5210440008050301c0176829541200107030302064040c00081a492421107800d50600c04000c1000b00103901d5503100901080d000740000b014011410042c0b00034400100c10b10030031900040141091810310325101c032030110b82d00c400c030344480c0165107070123062034100820403030079401c49114204500c174000c03108031007a900c0c08035000b828800e0341c1130018001035496a07014645203030713040a40c66a492401d4907603400b0642e07000780c4204003805102c007042c0c8280c03010300c40c6202c1003034582190b50704194103880d448007800303003c0c2c40b420010340d69080002c016540d00048080b03031000010086540c0c458052411620792921542000031b900411411886190110380b0981c40421410810300980c56818a11001c6030407000c100c500074260f006102c0d83c0301401c8015440a03204c0041484510020000d20540c00040c0b00025 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 283164775 1250 283163525 283163533
    0x506040e0a0221010219020114010308090402070620122a0a020c0d0501050712052a070c06091a0a020c091503060a060302091e04020d020103020d090c090c02010c02 72
    0x1880d080410a0050900f90501c400c40403c6945150890b405070051480c034500340203111506a40a00420305c2c20325602c0143c0c0f10a40c0b6603211510f0901c074084400780308582c00030341c142c10030500398030000c05410100c01090018080003051741065101c0b0ba002d5a242d0b50034000a004152822003440c01c002c0b503070401d00e29195080280707810f2500003c22903401d5009804418a443d00c40c0c40d94900814010400800d1030300706a03c01500b00d250000c0744208460a02c030821000e0650290840302c44100d810f031001c04d00d0030440680c281400362034802003d00c880350300c000820a84c404414402d99400c0d00c2c400006003103400041d036881c8a2000c043c0c1c056000985015810300d045025103500c074074640145065000610002030619004494814880b5500c0c00300740150b0a05e1524298000368015010340040d1440c1c4203415031035001071000f842503030003014120459100741c0540c0d0305600860400d00007521540f0b4031203000383c000d000c0c00a000c0c1c0b400e00c0b049501071050081c0e1010b480c0f20b4002d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 283166025 1250 283164775 283164793
    0xe0a061a220b0d020913030f05040308040b130b04030503181027080703050718090213020d060302060703050715020a17100803040b03011802090105030c07060f0615030506040e 77
    0x6240604202d0741c4065000d5180502c140160f107814241910641c2050042215504946400303040d101d100d00607a010413030700740002d000254080045506440e589a501a02c94070001402440c0b90020f805c040080c201c081800000c0042c004040d0081c1e140d18441c0940401f614000d20a03200194100380d00003901c801d0800703245440c800b114002104448460180840d21030340168038205055200f25101e40c00400d0400c0000840b9803d2419008510f000b80a0306455800064408a400085020b510790009503034480c000680c0c0103030001c66002d4410b41d200c82c5c1e01d04000d02250860407065408030f280809550780c04c00c00344200c4000c05115110601da88a222038070ba095224000c3c118480407400c0b90b008203000030204051320017400202030042d5290304200c03200003c00c07104103040c60700c00cdc0180141000d070f0780c204050741c0e4070a50701c1c100705440714100d0400b1005403100300d03c6051900d14201000c5a400c0c0b0050328820340108540b400c3c040c13900c40500303000494584108034680c07a0441090 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 283167275 1250 283166025 283166089
    0x815040206070c0504021605010608072d150305092118220b0a08011109060306130f0605010e061207030209060d151703030f010510030e0a061a 63
    0x42c004070303800b0348214021103407564040340490707105981050000c14404030a1082050902a05010700309140c00303405013500d0100c4810002e01d4034035200603e803403800c443d05510355981a2604c0109000800300b41403000d120350140081a0985950416002e02d044400002551800740908904241002072504020002d20007443c0c3c92818443d501c1216400a400c84a660402c60b1628141c031240008030001c58030708100c06c0e0320701948403900076410401804100040a0706481028800f9209203650381c1d114800540c0342d20011000d1201c040c81c01d40800e000440702d500c04410b51f0000c0e203c11203076486050401205000d154554041420414001400203100e82c026040032200a46141d0a01c4031107103858013603400e4104152800c03801180c040022540440500740d5480c030040245145d41030620100071106014000d40d402070700740802c0c0d2880140320341d10981c13000d06240241d43e4103004900d040006428000100702c26542c030036050603603e00d8100d030840510400f0019280b60040000d80f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 283168525 1250 283167275 283167277
    0x810080a120503071b08090a0501020d080610050c0a0302060a0c14090d03050f0309030711060703080f0405120408011a060a09031e02040c020616020f1f0204121b0815040206 76
    0x2c02820000000d0a618201c05c803680d80032040341c440c0d0202a20342c0040000c1c007541001720341c030890441d030005400b100c400343c10140013504a0815960304000c103841200c00d403058803420000000902c00c60300d20300f060503401b00326213000f51542041482618140c140440c1c1c24a818004402044010840c414840c940a0361500d520b03842420054240800b00409c004c960304111085107554000203014410000d400e07040d0030103004215031242c20011552002054080001c1004884d507101801003003c1c440e04100c101454082521a2660f8517203501200b03018003000715140c4c501504d88c00142500c0d103001e01c19254440d01943d1030722455841c5032240383c4d1610f9000c40140b45c0e000c0c0c503440000942c48500940e0309420080c1c0042105e0b0034001084905000401480b4085422030740400281690108511401784441088120114140c0c040e0800070300c580e51142880d1580144400c4c100010740503450350001c401c18650038050303503814020380c66007030091000d80b44552110004006182c884 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 283169775 1250 283168525 283168531
    0x3040b0619050a090e0f030408070306061a070b072d1202180d0804030807030f1d0a140a0815010303020f06070e0103110c0a1b05010c0503070305280810080a120503 72
    0xb412071b081e50320070401060860b48150000c100c40c3d001404140240300342401030030001e1007101d2081c0342c102c01540c5010800d000d50b40c030040c094000100450601440744c0d80518403013040c10282082034844030005403200150030001c6012564a0602e62010301c3c5620a403544507007031855007020300d520741d010405012400c400032500100c05000200c00300d94040b000c4c0182c0b0348070361913040034426411400b926240c0075002d00c9850000d54914482d1036107070880c45c94122880208200038404c040c20000325022001d8108a0700352050860b0321914281708140b0904032806030b000d4900003010011125205c40d4111605000700e103402100701e52035482540462000041035000d01d007450b02010b9020b060619120044d03a40005503403c241c59106410b140f0002800242042031225000340d54407078072806510300280901001050455422100842c00ca00c1c1105502d21040d801c1900030002d0b04c116000d07100d1503a12980d545c0003040c1d100000580400d03198200c0e80b500101d0740c0b90103044032558001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 283171025 1250 283169775 283169801
    0x50c09010f0c2411070f0201081003021e09070801080714040912020d030e010e0705060903010e070e07031419050702120a02010b030c0901060801031101031103040b0619050a09 77
    0x4805440b01143e000c1d10521010408445031152142c5421141000d40c0d07814803c0312001d01c030401c4100002448015800c0b07940b0f03070a0034000303101d1f0303510301401c0f24406250340040e4010810b00d4003107545a5200d442000c2044044a0814072520f60140c00c403902d000c2400740e0001d550008030240000c0c0102840d254001c603000704041408005659421248080c0c2c800960140c1d01050b0174006040d01030103000034440140c4003c000d02c00100300001d59480b941e1141c203020304c200142c00d101e25242904550001c10600c400c9500082d40c032811580c0d12081100c030040081d10b000740080403c800c02081da801420141c0b102891003035280c0794a0300400700507103090103511402407100d00130300c503003030191030841007940000620b40c0802e018941400e00d0030402c0b034468190480144101a00714000906590b08140846840d903000c1005900030a01c42aa0070241180402001304006000b080c1b107105090544490106100040404500703080742c1c0149940007107444010704c120000d692081c070180e145 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 283172275 1250 283171025 283171037
    0xe1305010914010506090c1305061b0f032715220609030c081203070f1b0803041109070e0103090c050d05240121030302070b0a050108010b010201050c09010f 69
    0x5180e540b00c280d5045400b51511994503842000240e1800d06100b0fa40219805032062500c3c0a15018030304903211406150f103c1d52021604031009498440034210101660040311000854813900d95500d070009810440c155800c448066041e404032001c1d001c0000c4084c0070500d0a507504061064142c02c101d50b8004030820340b01041c14203103108418440203084a4039800000c50850a01214034026504000314030341c00304454003002007112040781d9018081d4601240d00c104041d41c1211b1031100c0e400510344c4900d02d166010240041e20000314021842922441c41d50407840e0180620b4850855079080031942c16000c1c1c140550086d088042403520074240c084c051625240002c0d190724000714169540d82c0440c4070301d101c846100d8099003c86803801c0e944600c0350b241c2a00e8a008440c00211030591069450021003014003d030145ca41182d44840c424241e03150546801008150034441d4040c55800c01304101c451354018819035000742142c1c000c080c50882018015540781c2486044041041a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 283173525 1250 283172275 283172291
    0x2d030709472109150105101103071203050105010e010305040b010b03090a0b01030609140f0a0818120c03071211040b180403080103210c1b090617070f0e130501 70
    0x2000500044000403071150841e43c01e040e03840e545020910802d02038020b15100050109541300000d90b200c3c103035246050150601070851450943c081c046005201e004900c0301860041d4061300035a040c4c45003a030710b1380c2000e81c0307813401101980d0701568050181a100d01c018050714030548000c40e88200380e40121807100965030b90340d6004030740c242c0c000e030b5200da615040700341082540030125544801c10b500a001c69401c1e2400030340c40d000310010050144400145501c0d01c02c0401640c5400900d00800c4200340031448100c0a45491800301e1fa2482801241004640f00c070564040906903600150b512400540703c5003071000034400c0415442e4005c00316524130070001c07024100d0034819403003603071000ca16502d10f180c401a54070040b54645428044040303078106455209a02c1140c090308071000001d1401c0b00124144400070641241da22035080c408081510409840403080c048004c1e800c4030950303903881e41c015141144900521480c40345540c086206112010811038405016600000d0000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 283174775 1250 283173525 283173547
    0x70c09051f140f120706051804020a020d08090a0b071e03020316030b0a05030717070b0406080c070c0305030c011a310b060d060501120b01052d03070947 67
    0x19070395074446c1002900020381e4044044418000c1c0103241000d440035030829050078006034a40400241c40b40400c502c580008180300c1d0208000c02260f83c10458680b1542499000201500b89094020314240030740d003420300309240310f482141d00c903807010003440040c4c0c08281012005401c5643c03400740d12000d008000b0030b4079901404210010280b00c2018080070704c9050301c0e503040a41c01e0380700c2275002200740030030445590403400d43e40e88a03201030f0b41c65617207518500c3c0c120301c140302d03c0c0c202130220720001c0b4208007036040550009001090005402090034400700030054000c000d00602c1c07002d13014102e0b01d402c90f011840c8400c0103040d206100419a80c0c25a804940c9030742206c10000612611150308008550b00040c01616804c05804180030700100c1d4400608148180c002c00d81124035503007080c001046560000044461810748225940d05007808002d00c0c18100740200d024a156a5440080e020382d601c0040000701558202034075100d00c018500d01e02c1000356003030300c94040c0013004203100322 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 283176025 1250 283174775 283174783
    0x5010c05031c05160507020a0501030e0102070f080901020136030210020d150b090121060816080f030304120315030516030302070609030b0609060402070c09051f140f12 74
    0x1d260b180d4002064944000032040c500c00c15a400e80601c14100702c40310240e2114640341003a00c0d001e090204114680c1c0311454028801d0410207003450000891400070822031a000f4800810240e00903c402c0d2501000c4220280301c0c44c021114540001e0144d0f1441042c3c4103103800d0482c040d0051b182c030441d901c07030a80c080e41d0100011802c03e0f42c0d10020b4081c800041113041e4041c1a000043c1d1307080c184643d00180491420110600031040c4c049076404c244111600303c4c0c0094100c48080d6004544a5101d52006420a004101e03180c0980c0d54595000f032400030070390788200e41003000d0919070040b0f03500c140c008003003803071030a0b0b945070010071701002140041103061450740002c480c908003070b85181402802e189060f001074007000729541081011490340000c3e40c1d003100084032400a1500d60a00050007486034803401484107650450000e10841c11341e2146118170411030b05c152100003182143d480001180c0690b40f00c100c40440d040f90a8107250f91003500000c0007130300011640d202c040e03100e4a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 283177275 1250 283176025 283176067
    0x4140f061e13170604060e0c0307091a03061902070309050a030b160516030315050d0506070f14071b03061b030b0a0305030306060a1205040f0302060601170105010c0503 74
    0xc1c03034002525403260800e00c10340c5001400c5a94001c445240c0e400c0585845050144c8040d00098030740100300c05220b42442104100400141280c0c0c01d2503032164440045c1418022030808820034803007080341070801045540c81019451035100c0454141c216140007500808002d40c10416a0751002c01d0540303582121101071170140c0440e070803e00d02100e0a60a070f50b0b000200d40c082141c11710158241452400c4058a04c65160070040f50001e00045003064038445c1d9131000f94003940007020038081c1300d004074039a8080d94090380c800d002c0c031090070350580b103680000c41c016000c803004120f00004191054208201c10820312065107280d40d4940b1a00305030303802440710365168904031612500e00d0ba014416603025520942d500800b00d451030300c80e25107902004007150700805000900c446c406125140071301c0303024500d810030851030038181050400d03134400c541d0450161046501080496020f140d0300030045111540740c140700ea080400445481c108810115420301c02845012074140b0304030070f8002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 283178525 1250 283177275 283177327
    0xc081b010501031a0603010b150c1015060810050901090509010f0c0e0316150516050a030c0b010e090604031116150906050315040b0d02040c030c11010204140f06 71
    0x400c54510099071143d40c3e4000e405c3c9440b9a14107280c03a0810f4071602802c2e0040140d0f40312858a401c0c072521814105441c1844114207a45826465001c5a034848001826188160b07218102c03a0744031000c03890100280c0c01030b903030300c054510700400c580422a008558495029800814103250902d018820b0310150304020010510058942a050800304040d101d9005007100e8100d071070b80f511090010b02e24540c4e1807601000000106034181d40301c0000024041341c0d01c0400c50b12141054200100803218406049032078800c008000120400c4808680e802a0810030240803651916a015200300c4800180c0020314040c21900d43c08103d50b0821681c001c10700c1c08540108040f0611005159462a80000060243c1842800400b201c901398041b00e2140c183c0700000e410009100180880400c004025440790404902c0500203900d901b0503d0703034852603112043d44040840c04203090b409107002e19003a0690107107804031546000030340c8031454100130300790724a0002c1c0342d080d520401e140c54003844 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 283179775 1250 283178525 283178543
    0xa020c13180c03140c01052505070914010902072301060b130504050112050601060c03020c0a090e010c02010c02030d09150504032102190c06060803030709090b0f010c081b01050103 79
    0x134059000a01c019002e21070b03014102c0e02d1072060001c3c001d4080d00300032082c2940a006100ba044161205a1103900e4118084500d401e07951981c140c00b8040c4021041442600704000107003102c554020385820710780c403100080c00a4480003131603010b0084401144465902c50b180050f02c0a4008018051a001075820050344ca042400340b200703507501a8000401e8600020155000c914017003581410760790107140c500018007150404900e07007102000d40e0fa5106070301c1030000400b00700319800305a400300210000e00c406d074440c038001d03400ca58800b4010800350b0800c00600f00d81c0d03e015070103116018420f1214240c03402e02c143d000001c540c0220b80403008540b1203c0750a03501c113881803212059058412082d85400c07060b05d204140007808103004c0341480b58103403044c020880650818806045030303034100e81e261301c0c0400300200800010b104a1018918007120fa01190401d0081000044030684604540b19066590300030399500c81031005c0d903204106002c0e460011401c4c0078050007113004400745 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 283181025 1250 283179775 283179779
    0x103030f090f0f030b10060912080424170f0c0919090603031206031e0311010e0105100503070317030c120c03060f1c03030510030204110a020609030a020c13180c 71
    0x410810501a040c6c14011701d9466040044c50360141c85c68040c1c1e03c80e030310078450400a510707180c466801980c00059015211020305034401c13400700b00b20024220305030740c1d184001c186c0300c182c4030161800707807082000285c40b00000381c0802c1d1030030000d200880c07018040e18220f0000741030b0703180d6841c0190041e0f24415211304e000c00038558840c05104caa0420301c1000c224242c510b40d5a0450b1645103240c20100c184005c81241c01d05010300100e00b1070040ac2e000078000a04040c1c1d10600810702100d40c88080030825002003002e00340042c200003540d87c891381d41004610b034031180e51110b4200034101d40c0742c1c6108000b100318000310340510500400c660302e121900c0707060003070800880803030003016039001d84002c02d60b50044e00807440d02d5a410320b8141c00e00141d240c48801c803c960004440d0806900039041046013012655140018150641d0b10303030a03030300070380c507403000304c607101c0c4031f032034070400060b03016040c00f40c2e1b0381c5080c050745440c90521650006400ca40200111038a0007148000d4911181c01802 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 283182275 1250 283181025 283181033
    0x6040c09050603070605090d020a0909110111030a0518030c030f160b1903050601050f181825120e011a010203090a0306090f050613060c020a0305030103030f090f0f03 73
    0xc894002c04210040d03c82d803801e0034001400b5001708601c040c400c1441c00f41d4541035444103d0002d0140040c00c50600c6041c10303e00707001400c070650084050006104100c4006043d90100c10b45c2d4010700303d9a038451400c884034119070605d008610007183d05000781c0a80700e005c2d9404000298a4030340032009011a14521a01040d5170403550b4404c81100c50100842d1850983d0384541e10880c511504000407103460760b00040ba1035000c0c043c110760f809000060003254050303500100c010841021104802d90103c0089856603011094600101c401401802d412807650b401d80701c0e030640c900d18a07140c24500400503501050300c1812902e0551039540d40e0510202580c203440c40301706901c003800194034100416001c44c0c5242a148400303046141c2e141a502d0411400d01031241000f90072000300d40d0b55003020074030398078800103213403040360800c1c43d01070fa0158503400440c1d4218869015214181140e01c1e5403810707034800c2060034050040018078080407035190386010f100405046102c0030700c1d2040f030071450 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 283183525 1250 283182275 283182281
    0x1030b010501020d050d020a1809060305190506011203030b060d050603190b06060706061d010f09090507050108070315030b161110240e060f06070b061c0506040c09 72
    0x15045403c12500c00d290141c000c5c003124a24520108010b81c1c49042300790464501012068103540c094560800051000e1503401170416680070f0000d071164211094907030410040c60010090164014100402c00102580c580c40f803c00d01070705000c02c0760342140e400645c950348240100c40500d85d84c3c1e8213001d01401c04001001c0c00c0341c0d4140a00c5920110303034841c0c485400c8000c0801e4403440700015010304001c0d050300524024159003081048406102000301030740602400f03106059856000001a0400903000309266643c0050240031224100001140c45080090202003416161000302c0c1c045071501c50020011030107500d18403014180144000d00040d46001d404081220f0b925070b104140340c0100714203100020b20040016400740c0b610300c81c09011600c0540c03040001e0768410001700420210f141c280316100c2110350a0f07604140300c0411929010340b80004d08040b412800181e000e00b84000c4144003103824185c28418441030341e5615203003040448013282c0300b0695400c1004903c1a80c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 283184775 1250 283183525 283183529
    0x516050301140a050601110a11040e0313090b122406010905090613092f060a050a0c020303090607050f06010e0c030726040302011e06060e0411090904050601030b01 72
    0xd00a00032050009844448028041c1c0082485680c400114145a008920b9080303007100e25000e4416000241c10114011031250300d4690041e03003407510510243c080030080380c080707040700c200c02d0b004039040190000041440700c08884d00007407040340601100004204025568145680c548020b6072404000b41e040381c4080e044a050151144040c0401c2c6e41c3e030034585a104c20252806244100007140960103080022805004004403000825103010143d18182140b80c0e21040e02c510421401e040c0032081c842c016040c0300141060141460750746c1701d4801c41c141e540c0018112424590f860000840b1503200b070300103c490354001c103019919183c05100030b9004001e503062401da00e1424041d004041e11000f0400c2e810031012900c40c2d0200c116825503084803040030074440c0624a8180b8010b8001c05460302e404288021880f4069141c540600600c025501e180e61130480c0302040d03d040c40b01800040c20610300c081d205104400f400d88421400d18413032800b0700000c1049525604144800c1801a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 283186025 1250 283184775 283184779
    0x6051f0902090102010f1b050711040e0601031e200316140910030c17101d01142e0801050406060e07080f0708090a213c051204051605 59
    0x11007051907101c0c7e95041e95030051029400c055646d180c2c0380ca00711219103100c1d00c0c840da11605d440401080d00000240181c140ea00c141660540d41e560010920305012000c0c07001000b11840d60041d105030032845905008124019086540700d940c5400d03d181700c201d03290040c0f1008101c020b40c0c6080c0303181c00080f26030404a01e500c90740340d02c0c7c01c58485280740e04c0d140c015040e856103a07000224a0140400c202c0111502a003010003040c003410010f80c20108880c44003124039801c020880c5040c03403d44803010b000c3d480f003414010030f1017034020024107030401d507e0381402c010b0460000010040c07420300400344114031074800010711074101910b0300314404005d0906010001c4400800c02d5203c6401e41d000d404c0280382c01c0c80d45480e41e5121459281c2500807600400e02e4213030300d41c8c1251421260403489143e1040b5152040c0140e103800088200c12941c0c0e1809800104421101c4101c003d02940c05005065030702d881444c2400c1c007004500a030300c0c15941241c040d40301c6010303c60b072000038200b440054002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 283187275 1250 283186025 283186031
    0x120a0e01090e0105011b0602030f151e010e2106011e03030e01080a1e1406040e070e070314040302150c0412020f0406090f02030907140303030406051f0902090102010f 73
    0x108520308400030014002e43d030506c010202c4590890321b8801094841a510142c190b580e0301d000740b1105d400202c2030703860300c072048401c080065043c41c0c164080d43c49055500400101d4a144000454401000b0207030b0942105500c54042642032080c841c592207a003803c0001c100701d5140c984c915181098540d0845190310245900307000095000000c03648941003481c12030307220303121080f07001c00a09044281a00000b20010344160a21413500320380c21041d0801c0e00701e1441d9554400b444140c401c0502c507942c56821054040c08181400d14030340d9003001503485c000411522242210440700000d8805a0240e4042c180d80b1103080c440c0150303c0c2e405102c1c589040e00b02842c1c16551400940100d00c0244a038811505041e078589680d0b10060051004070300c103104001c1c81e841c04a00030741c8151400b940708d00404001062104136119002058a4050019460f40c2c0d182d80b6074000034040a040c1c040c00d800c0c80c0055100b15088404081c001d0f00681c400141d0740d00c42c1c90000782c00c5401301105000c1b1a41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 283188525 1250 283187275 283187279
    0xa08010e061609050a08060f011403031b150106081006020309100e120111071b080a14150109020a18151d121c0c0b010303030914120a0e0109 62
    0x15010074001e802144280c809a044000c1e58010745119046030001a0401c0e00c2040000314650f0025240f0b0094140d000c000d0826600d54510f200c4803c00c411120b40c056100300f00d1405002030b4406460000300350340c400d80341c00d00110403041246e06000c0c0e000e400000e0568090055101c0030f503c040c4028a0603000551078002028041020221004404400d0014000e04410035403140901c1c0149082d0080003001300038440a0f140e800c0c0d0300030321001c0d18102c80c00f4851100c000321302c822a406559034000103120042e1203980c1c020a609121003640814003e1185058650590a91050181480c00009611740c04902c0005180050301c4c546840b0b12044c1b07900802c26041c20300c0c020700c0125902d10b05807040b03511300042c0400442c1a0421a40c11a0560f0401e01164201049130100c40e0340c1c040091890211040e02183c0307420444030f018004001010040000900950024034020720500c0051032400c58940d5031814550740c2c1074681c1405000040c905541a440820039400500900b40860514 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 283189775 1250 283188525 283188551
    0x406030b0a051e060a12080c01060f090c02060f1f030c061d04090f02040c03060f030f0b09060f0c07110612010f052d030708030c011406061c050604020c0307060b0a0801 74
    0xc0e88520400c103101c203140c0440014801107c088620801408000740102661610302e011803007494802d001880d45012080c03030308244040758441c00340300261160700c03950311145120094803607a0b0303107a08811001140c00100090164120340c0007040307107840700c20002d06a2141d04a41d24509942c40d48210315040d801000a0a01425900700395016500041d800d500b080d025401450303290840583c00b618403d0000410000304988542e980c0300c3c04a010310768407210402c80c0d1394001601d40c2c4100c40908800540303031031038802c0900003142c003801c00d80c040f4810322000305130560701a410381100d003000315005004030f80e0004440700080c4419034075041d5034905084d052100300349c1c1007000030000421108a030065176003000500c2c05466070070203403540da4045030f0125009004c000b805c140b000890000203003080ca024000d0710001c241c0c44902c0310020500c81481c0c80200300090645621a03801d120500c2400340410251003068400c10740041c3e40f0010030704101c0300c1c0c0941e90024200b1703810701e11074060301 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 283191025 1250 283189775 283189789
    0x300f09080d090213060e0103060e030f0a18030c0303050310050a05060706051b0307020a050615060d020901090f08010e011404020a21051b01030c0201060b03070c020406030b0a051e06 80
    0x40e60481c000940e80b002031000404e081c01d00a00002428201080803c05210f00e40e6001d040b00e10404040044000910004d501e81c0100030040c9190f440503c0181031030f074082c0d0500c0b24411249800130720002e07160790341e1550141c01c94005500103807000c0704021500241444400142c2000c94540000501d4440050040d204401004110585507000315000d00c10303441d85010000d500e00f180540302d10f031441d03009699070114141915544144004150050200141a030300c03070b080541031744d00c0c002a5902c020080e41c00090014100b01003d00c0000342099910900405080800008207540c1c920502ca1820340f00c8485051070381d50800420b2000681d07501c06c001046039203190b507100c00c0c0c2950802200c1c4134050310201030441c1c062061508401c0081901e04460400c01343c800300a04081d0346022030803500240100240c0000410108207801e0003040e056040c113100034004100f0940307907030711034120300016940100c0198403442130001d12503141c050a0080c107c1501400b400d4603140001170340f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 283192275 1250 283191025 283191037
    0x319020603071202090307060e130c090e09031207030c02100b0d0b040c0305030d0906050c070c03110f040e0703020f091009020d02070b090a0312200a300f0908 70
    0x511051143d0707400c40b4072994069038407104c030090956200e40d603a0440a04001c0d031a2050701d206581e0003600385480741e000c3c89000c00c2c80700c243e42d0f0088105e040c5420700309204405025488144014443c0307001a034134000116200b00c80d1950081010784401c2d2000c2d05d000382034503e51f82c40f903080204a540940380c00c0003805089410002200344d1b40c90700e0600215043c02030300080c049020004403200303180000d800108c9442c1c031485041002c3d603200240c4400500074620000c06a60110b10700300042070303045e54950103481c0024110340c0f01c6505140020708a178020b541c030440380e40100408006525140402c602300c2c42069407450142e01e8548690f910003000f5004200049038081103204044207a0b0381500c510f1030340032003c840705040183c80640c0e00c0744900c00407000109199100007c1c040940510504140380f20501c2c03111105182c0600d620303400444401c0300b008000d4071000c4030305a581c41d5880740c41c41025800040402101280025030700e030702442000703450a0150a40000d1980011140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 283193525 1250 283192275 283192277
    0x2301030615081f050303041418070e040b0109050d0303061514040b0c03040504060e0612010c0c24091a070201021606021308010e1f0b0904021507150b031902060307 72
    0x1c0c03006a074041003c880c0540307401c100d41610001c18042404011800070030071608003141c4d4a181d09815020700120b01c0d4040700e4110000300c544441c21a5410b15070801c00c44400b0504204401d55114000b113001c4c00150041500042d8a46404128444980c2c1c0d06100c1185c407454641c440f001c0243c0d43c0300302c0c0d00c0b42d4415a070107410000f901550a900038000e40f000780400400501101d543d405900468031021748015110310400a00d0f8250800b0505c140c1d07000d0b40c0a51600c448611041e1512400d041c0f210203401c1306a1110569650024814403400c940c1e40d00c505468008500d050802c80641240100741c0c4055a204109041d418040250134000303066000c41c000da0381700d0340c0000719141c028181d80011041d41c05d00c00310070305504000c00e604024501260070754400034140014030040e10b07004035000d500909e200c03000c200582441003410240c141d084540c686009215610302c0203071010501c00c000013075910501d584c3d07d4030b42030044003c00004080203e102c0a45500050514030010704884 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 283194775 1250 283193525 283193551
    0x9050c03070f0210020711030c0a030312020c0f0f0a030f05040503070e0603010f09030305161809020a0c05070e0412170106050a1202070507030b060d170a09230103061508 75
    0xe05643c404c000300c00c1c601090740303429920740c3c4661800e00c4245842e4039143d407190240e114200d405081c41c0e100041120b805a0350944512100041c5800039408a0890302943c0101119010307014800c101c81030400511100401603c051810300034a000b0000400324104030080008008503030b40081c00b80b064075414000a030283d02c4090000f8014042400038018460800600c2001d054060740000d11801c80300014245100100104072342101c001d00861114106a8405000c003580d140c2c0074083d01c3e80f060408640709103581e1140c9180c610541c1c8910340c0c58000804200412140200808240c50309080103010003618200b1010041c030140615810003001088410520b4461990310850158621003156100354a042a9485805902064903200543d001003006418140e464100d22038006801b1966000054194801540170b100803a0800200740000704901b00c51070401d8040749000861403140f030315a180050b0aa5044c1c0c1c0c07103400880040e9521112041d0012200c039030002a020300d00b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 283196025 1250 283194775 283194797
    0x807061802030f070f0504090203070b03040c0302060301030804050a05040e030d050403140d06091a090c0d0219050304110307050d0201120204081203101202011719111309050c0307 79
    0x1404409590040d500d0301c20b00401c0007080030041032040c160b92a501701014150f0701e4a050000f900d000210003501988683c500b0010080920051740c3c205200344402c9011543c0d0360001107044c1c01c203810a80381c503d030004007008546401e580d4178000b04003c2d1030a1080241c0140499240d01407003c0085030107440b44001410548149110211411050107060312141c001c00e81c0c1000340003e0050044441c0b80911102003401014560101440020b00c41100c6e50b40c0d800408540b90400001c0608464091001c41342c20075141c00d08070100d481d140e403501e481e03143c242841c451016482e03032800d000350001001031220351580c030b5a185a450702070a00c0c0000c88607440200000b44210341c0316410314061151580403c00d403840066010304201c42141c1865612040841c01c010090708000340030034040415652428000301100768400300f10a410949101d04a0988081e200304080403000050001141c0500b4000901c4846c003034598204108800d00e003214410810b880041c0844041c0725103007410b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 283197275 1250 283196025 283196051
    0x11401030308180a052d0a0c060f0e04090f020117190209011e0c1a0c040e040f050105041b0803090306070503180f070608070302091e0301020d060e160804080706 71
    0x85010030326404021510078240300ca0b045210200c440003ca21203140744405046c0007000021180c1d4a10340007004901050f283c070806036003401301700c04000c043c443e81600d1005150346520400c00c0c41c5005400500254495100040403480c02c010002d058031620000d0006070540380010f509032400a4400694500b0002c00680b01c58660203ca03a11f640c50503130107403445550101711018141d2003044012510000e24030031600002045481d0503d0003024081003100d0b01030001031540180c021508010080b030729859090a40d1170446003920040c00d000c201ca030200c00300c01e240b00d00402501016504003200000060389550014000000700710010001c42c500e104010307140000040b00c202101e54030398a840a40b6224046441b401e40400e403d200054500c81c02402201c0700d23804010103040480100964034420b10511640403074243d03509000b002d28540b05441400c0c06455141150303401883d0040c240144440c2d075505550422040310709000025510f41c00340d404c1a0341c044404a416498a50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 283198525 1250 283197275 283197283
    0x160506090415080d08130f0b13080a0206070810060509090709120302010e0c090708060d0c0902120a0c0507030503010608130b04030c0c0e010f0519050409050f01140103030818 77
    0x60300b21428102c1070000208800001420581e48600b611101c580b40d88021104000d1880c00c20043e1100090103e4040022140500c20b9841038180c04e4841c46450701d40c8545586d500606260740140c0c1c414414004219006a992503009201c01c0010f0943c81c103144000b80701c4c1c051484898020203e400224100c0f41c0250780d000d0240c000d000c80e40c0c03240400c5090080c0a4100c00031448901c0c094085100e0b554108150b0261040055450340e846580314035090000042c0030300000d1b6000c10241c034020030084024002440c204d414020401c43d02e08000780403800f03c41c2a400300106001c020460780d4002078001c410380c0c0c11a4014101214242d0310408000d10301c2d4598000140a00030380f42c100b00170142c100040c4108a8042d400711428140c413400701003200789007800780b00c0340141c3e4440100b00078036140301c80360b07011000d142d04124150359440c04907007550300d2601e0446468100781c0c002c0104520910034440101d407050300719000382d49140c901800c11607015006401c104243d403806002d10700200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 283199775 1250 283198525 283198541
    0x6020d0209030d02030406170c0307080712020c010c0e06120106120b10170f100b0c0703051e0f0c090406091e08040801140411090711060108031306021605060904 71
    0x2c0c007540c895540c1140004c2d100c0d445406541e0100d0310701140000d001d600100007611402d038414841e0f103951034441c000d40300000000c00d16020044501d1003591113841328006401c0d4402448000300e2180c0038010042e00d503240c8004158007500050200340302c000020403090341142c806040101480d600d685905010f0500101c1c0290400c030047c0c1d140d00884d501c2401c40099544402c1403020ba07031070740324464400303038800c0d10100e440b808415401c1c8400b091400042200c80c0c1030388119030711130b41e60307690b036904102002c084601045508410b50008d942e09005150750841e220024011801c440c20000c1d403251009040541101e03550780c4800f0420100c0e07001c04910301c5101c000f001e80c2040c07038900000035078814000c225441d420b10244240600c0305031400e60069034445100b40d28074000e0000d20801490040400c030402c024480301c0d0701490414800b1902a020b40009159500102c041845580e040f0b68404811076000c40d007c185000a1124988113450049949c582d03240c6014000a019001d90 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 283201025 1250 283199775 283199779
    0x3070f1205010f09050105040c08280509010509060708090a0b0a062102010f0507031b11060309010207050d09030b061e0a12020a090c1706040609050c07020f030706050706020d0209 79
    0x81c0010035210402460941101c00e03110302440941e13204c005010a480e100642d52021400240c0811005003010004485003401501d0140440341860b840d2000da5006440b150303000d075592410b0141d00003091261540c0240d42d82005d0390b0a04214050360303074400f44003401074080440d1a0118130b4075410785c0c0101c4020164074200b502d42107200c0313100480e00300010404a0108803995030100c5603078000c2c410b44a080c1c0c0c00d84c0310305100302d0030452405450340d03100c1d0040340c10101c00124402d59076208000781d40600b42020005889450510700380b45012000480081031080c100030420006001400c00ea52180c02030354440f044076012490710308071a11031409070741c0c1300d00b1810001c592a0200300c01800d1480c000c9980110040d45d681115003201c0d074aa80410029410840524425152041c0c0b80d40095015000144440d40c0360b803c401144c0e010356007641c0071040090ba603015071070302040002e0689400c901038030300341c1e03e8114041d01c203100f400c0004040e45e0300460700442401043d41696007041e80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 283202275 1250 283201025 283201031
    0xc0f0f0315060c1507020706090501030203150904050610080102040e04020609040e011d070f061b0804030f0807020301050a110324060a030e06090109200627010f0e030303070f12 78
    0x901c3c41419110301ca448845111181401d000426162001a690b8100d401944a064065003404011400b950005104a03155101030112000d26201c0d000e00c14441c40c040c0010385800c0c1002c18208200340065404220603038018041480002000f40d80c4d05d401075811209241e981c0159000300d0044d00050f8010850b035403070710a128a001003000000c20300c1d001601d0980c0d01590305d502c01d811000b40c0500450002801844d012030002c0d5864517068000360003401c00905013903896807802e0400e504040f0480354610082414411414240540303034011001c040300b408a0034840301e5040f0140001000c038121446803d070740d03000c100e0014080ca14a00f60151400c1e0341c1c3c801460002c1c001e82400903901c4807500c500000200ac03104103102d812159a484400c0b2400d00b420781000d203840c94516889a40d002c0341c1009503009144100d0100c0303202c48039407a0010b240c84401070001d4507488034207128200f48003410100d038101b6900070003101d40c001420b00340410308441c04d11044842440c1103140803001d5103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 283203525 1250 283202275 283202287
    0x2160b040311093403230402150f04082d0615210a0210110d0c0305190c1428171b0d110a03030e1603060605090c0f0f031506 55
    0x11809034142410281c401384050000049100b100740da0f0040603401c406c01c80c501080051400d04501c0d0350a984820340c0c0c81c02d14850340310759030300d540c03003507118020562200b214071204200011041615040c14a08040d840924440050300c2e1600141603841d4042d0008070a200360f90349103101d075020b90100074400b15003201250301d5179a0340b4040000381d12440f41101c05025461150458410700c1410304050b1002c0c14603108160341d100762198003181030207401e20412650082d140e040c642d80903c56961000c012703a0904042d000b81c0f07030301005c1c4c1050f0382100340540c50401034400c1d414030f4407004103980000300c410343c2031801c10880c0d22000d0f0b240241e03002990460380b03c0c0d244045440324940500307a6801c3c4c08680c1d401d5541c0076900703230b2085d107641041b04804082402a0301600301107009106a86031520102c1c440903070304078140c00845149a039000b0620a508003030700040e9018456000c50761800d00855010301440c000c203d0045009013000001440822400c504400c540e100a0081a116a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 283204775 1250 283203525 283203601
    0x2010e070609030c1403030403030f0c0f0f0b0f060303070f02040204030609080c011119080402030f0609240c0405060d02070b10061205060a060c0c0308040602160b04031109 76
    0x2c40c0c144030680c0d842c48080307004540c010f4100c50304001804014015403506103960780c259001d406049890b030512038007090010124036550040070545104d0031300b1544080c4103103030103040e0010152082c1c0e541c0d80f0703400c00c00101e910700000311044540c018880f0540f0740c0c66440000d02902c03803a00300400302030504150b501000903400c0501070a0405400a01c1800c90000864249000b072505181000683c8040d81d05130034029410107402ca40044c00742d40c440400443c005140c14404c2e102c01d0301c02d91003043c2018a03c0c1051000c10110340902c09003e06c582041e215015141c003480c05040d00c216000220343c4c405803800e43c115403440340d10255940003860702c0c10795000003070554401e880125034610034070210450280300e4140b180c078000b400104114140320046895010324081152070307401c1c0e4100400807600f414041d1001303000a41c02011021201416008155050f600c08030580350305000600c0000c1510010314402002070b03900d00300320360b15014040c0010002d16400c1c514000104204d00400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 283206025 1250 283204775 283204787
    0x2130605030405071a070201120f0c05130e0402090105060a1215091103040201141b1f0c0c0b01090203060609040c110105060114070b1e0a0b13020a021c02010e0706 72
    0x610f0003002900d0032280da46031000031440004011458107a800c000301d500540c0a141161103c4030100c10018130380c02e120400400720f076281c210038008a400810144a5086502401d0001e0b003903030785040245060030343c040b0f03803244818042c85114150105031000c038107100742051402c2212140b018409600b80c5101a00c40b51a2030240d060158249132508428201000841c0d01555041c0c1d00c2d4611504507050510a540252240705243c00480e5007244114104000c0d2102d0010b95902100c0d2500620005900b1105a42051801c0c002000c410320081940c00a0440c111491002d0260b521f039244400100c0c0c9100318502103502500d40580da60741d05511100000700720302c665000300000e840b81801501d03070180c01020183d102c501042140009641014903541003a403072050b0043c40c0d41841d042d00c100c0c5204503015103411756a10081c40711485c1c400d0307140d841d40b61403160441c0340c0620b80f14000d45485030200d1490700000d480b82ca00b40094400d601172800c005c060825141c815465140003092 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 283207275 1250 283206025 283206031
    0x50304050106060801051309060e070b120a1107060c0e060a030507080a020f072d150c03091110090506032403030a0c2009010f0602060708090c0f040213060503 70
    0xc2507103040707004038210703009400450517210010441c461210072007004402810280000300d600648030682c0d2a040c10301005000050580ca0644645400f401e01d015800c0e100b006000702001800c020324840403881e24812120940d030010307404251103a42e100c043d611038a05480c80c68020200080142c2c80036495030215026442c00c1e41c5414441c1c9030061004181e01400c04480c1c65202d0403c204070001c2ca0760004d0503908420440b244403501003400c00440384030010102501d041e000d1200c00d4020f01c4107031186030052181801e0402500301244c0f510700300c1e650010380c014054114840421078490146004200402009060950741e25200400c0c50b20a00030002d10100c1c4201d45003041990314003c01603c01c10301c61079450110400d91501c078480350442c804512000c3c3c21902c1c05803029034542606c000d01a083c2d00120500b0613107000c030020b10b4280010425420000d611080c04000700d00070601d105131001c09c50302d58080000002c0003500034801d5071000038044003032040c001111500071000d144 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 283208525 1250 283207275 283207283
    0x3060d17030408091e030d030f060801020d0b01110d05090603070c020d030210110304080d1503080a1806030b0306011403010e010518060105030604030504261006050a1707050904050c0907050304 85
    0xc60310300300410218004001c2c2205d0f0740c950001d9840040061080e07100100702200c41101080342031365020382c0d900326170005032401020350f1294003200b0b0315600100741001200100008104005c3c40340e01c010400d01505031120b1040c200000071070b040324440e02200082640052002c03040c03140602e8040e41d916603031440b6420391070801c0c5400708100c1c603200c2601d201d01e4205c84d0081ca0700a110f01440002c0c0b00340c003100c1c114000001000700110b4603c074003500044845441d00b0100b6101c143c86071407004426407050080500b002081c4015440202d403450442d03a1440c0c40340316082000300040d01402072084820015840c010803c4000c0c0d80300c1482d607081c0640441510343c142d172214189621204215800b901040c020001048403036480c0e4480c00010401d2030a490b486100a144d00b818442072000d5100341c26180d03a010b20680c50001c1d54240102442c040385132500340c5440c030b41911056036101c0c00b0320940407480001e007448001d1002d1440364100900d01e1003e49443d000c00303030094105541c255 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 283209775 1250 283208525 283208539
    0x303050a03240510170a05072303040308010e01080316030e130b0f010c02031b130603060c02010b0a0f030b0c070203070b0408010b040c0e0d050f07080c03010b030105070503060d1703040809 83
    0x803030601071a0f40001020044d04000c3e6036545906d00c103800b922018041e0030800804174040303da04212401c4120100c03400254455980c1020708000345502c0042c0c000d4006072000e8130040019a1000048030603c410400e01505d04644900b0141e40441202203d00e80044610410881d001881e0344102039800040300c90170022040000116031901039a180290164818070b82c0c4001102d903009121003048004003d00900c01400700640b00740c8045900444040e5200c802078280b2540a0055a000c0e0609844540314a03142042c0f1105012151001900307204c0580081090b52152100707d44045402600700c1d1a401c0d6145890b40c0507911034814650954680702c1d81200c0c40c607060241340b0304d104007682c68005480e80c403001c200356038041044c00c4403184a604070103ea0340400384840c10007440113001600f007039074989d004c0c982500d0300c0c0100d881c4a80d01d007404005116401c0004d90b5008034041e20308440c50041e43c03900440308203000407040300e2094080100030800203280c00418144a00740c81301 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 283211025 1250 283209775 283209799
    0x6070c0203011a090f090145081c020f12060a0906030f12050d0e1c0215010909030215091b06030405120a020a0f050c0315100303050a032405 62
    0x140200480071180194800030140100360750320461a80180c221900b030780006000380d0320101d280340c01d0b0032105c0300e080070000410080358400c01d40c0c030310001c03600c1c0300234898105031100755280d94403849006c400d4a44404d1580b5481091030195055a825407942d0364419035840c24590400d40e102c2e030460b18244a030703000d1400898000c026025120482c2c0d80b02e0314441000d400c42d51840e20503640c41c040801000400e100503070310f110282c011440c400c800c2c0c2d8090710f2000801188501e034030b504070803200300f50342c4003e51418540c0c5440f128a4112130003000c0010381c0014a1504038180070454500300c40a0f50f0040500040f181c0c0403440200e5031101200307104c2c1b090804404d100650004030f070094403907000300c45910350743c400440081052a41d1031040d80c000503c190380d0f070400460f03505403d64641e0300c2140000034904041211920000300101111050f00d407402ca000d02c003804a000090412401181035a811802030300080d0903028000b81006408650f40c3d500d0300c0c00351030b51081c240705030518514 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 283212275 1250 283211025 283211051
    0x1a07021f2007110103050a0b13050601030501090c051b1c05040f0f030503030f060406170703061104030b0114030a141c05040614071407060206040b100b092106070c020301 75
    0x1114042d9a1080d86144082d00090054000300707001400500c0103503c1b1300c28601c46030754584582c403800c501e4000010b10b03400c2800004044076416000388401524000c1c01c03843c25504002541c3d10760341003010624034074880e03007012410705e04017540050414031004c1d1540511a0004050b206681c10381450f405410341d03808400d480a88180f00c003802d07035002000400e426065864200f80d0281c2c1c0900041030641d81ca50801203407082c4540e4000194000e00d405204204060150750255044410040d042038119258038038110018803e201c03c41c0c49106051407107403001d1000c648103a4002c6169005912125101070303e840598481a0100e4083c0c804400c0c0c00c0d0040f410303902500c1d895984c900c804545902241c2103584404010348984c490000340c1c0001420800502018002550191005041510306030801d000702405203040c3c8282c002c000d01c8180c038244159101c2c0041140c10b0700740c114403c0e40a1300c030038800905441c4030b80510b03010854420b4018044200340c600c00d400802544d442034078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 283213525 1250 283212275 283212277
    0xa11030304180c03090c15030b090411060a0215040308040b0702010903230c0303040303021e0306010f0f030f0606050307021002250c08010c0e1206041a07021f20 71
    0x198154908062014a060b9242a448040d6488540c03d00007400c584603121400b000b0455131000f0380d05d8884100d0952803540c103000f80039030004280e44208041c2001e548200c1c9000700f00d0b4000b402070385d002c43c1c209406172081110a005025142082141d8106410002d02c0c03107004580c255103118003040426006817052060018aa4260703840c11081c02e041d100741d121210303201500042101c42405001c01880c028001580540e21036100140d503580e00881100e0818403440c40020868002d104000041e41c10190b407a004007a24900b004e480c00846000360000c0020a0310104000d00d828000b00301c164106006501505a68086903000100c04400710140c3c0f00f60b40b1000c82443c0c05501e4146c49081c00300300140348910034680c0c42d01e0151512407442c00c40b80c03604460030019040c0c1c5014401400e211203050003404254015050320300d05501d4044000d915580d079018201000d500064403507202780056605e0001e4200480405d01c95105918081c0115020701500b486e100018100c00c1c001c10b41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 283214775 1250 283213525 283213529
    0x415110304141917070204020d0218010504060f21090f03030b120a2315072a020f030102041a1c0608060109090312020c010c170c04120203070305010c020a11030304 72
    0xa600c00a4080c19611040030b0f41380070409000600c13060100400690b241d00240506515100006031039860709403641c3c0c0c035400c010b820b0905201d02000f007480181d038041d0075080c02c44920304103842c0c00c100c202e141c0c11a810284124680c141d140c090706004120002e1050503005000c0d44d018040e0032034080410028401e41c5a4000c0b407607001420700d000240111080e40a0400c501c038007283c0302070b540c41189051240f060a841d46042e0800108520b96401c0025200800c500c04e000750110740c9120200f116848580700040d1107044110881d0b08035030b0342501200c0c042c002180042c0041c201400d01a5000d41002141003080c4c40c0c01c0c60002084501032140900300c40f141002072050340d2038460060018000e010007a01002011024203400091500041c10b030000c5420002613001c01644000b071820045204c0301043c009003000344945550400e081d02c0c161542e6001b201d80c2c40e489440068034009a59000400e036500f003a0b80701d059141c012440c000320a008114420465458a0415803640700318 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 283216025 1250 283214775 283214803
    0x445020d0b06130204143f0d180b0d090c0f06080901020c030319020c06010e061003110a050a0c050604111003020708030f0612120408010c0c1703041511030414 70
    0x140f260821850087c1041040c2e41c940c0500f41d4866410075190381000c09103074456006d80c51240e507072540c000d1003000003c00151a03454454030119a005020391a52040e10980d00c4c94035000c46c50b07503042450307540092002c80d801030107030601d590788a0394082064024460f0034046502d0070001041104180200d401c1c03503102070045c61071aa0303040800d88040580c407500b071361000d1b4284030101c000902008070780d000e02800d00255403185480f4081084202040d0030b48020141402d10200d15589d801c005c0d16030114440c10040d442c3c035040c54040311301c09070b201e1000d415445074005200c1032040840d407546e01d8030f03401e40c5c2003034020140700d206400382d115800000303005000400010b4010b034800d1010980180c40201003e80840c410842a880c1100381070042c2c85a02e000a001c004100d803d2140305061354060908c40152038080d1100e080e8040715014030085144004009000c01c41c082c10003990090111908000c08680d11410b100641c108442c2169520416210141c4040c00003d540365101c902c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 283217275 1250 283216025 283216049
    0x60e0d0507050d031b030e0f01021903050a0c0c12021507050316151406010201320403051b010e0d2c04020f0c0102090445020d0b06130204 61
    0x42e0805201078002544019000c024078600041003681500340d2840c0424020b56510103000161420041400003044845040d0340c0aa0090080f903840000514038050705810407544840f60580103455900c5600070042c0103101202c80402d01070280420300e03c0c42c2d070027031342e04511441401d00d00d01c4262042c580c01030240e520a102c2000c0d0600300301c002d50500c6210741d0062004c5072100071108151128003002079244240a810800c2c5540e0912400350028907a01a0410310030003000b140c49140c800b007030000308100b070740340028051502800460304a000c54030b10f904078010b004242d031802009503503070740c1c4400d00503440000205481861043c2c9664502468844040328498a40d418003221520047c0c00c10303020300c102040781d0030000c0900110500000003580d81c03030a510402c011141810000c04908541c1e141c0580c2c9000d5103880d0064401d01514006a40c0351101c0154a0030950b0a40083d4440151407201d400c200120300f500c0d006840c15148201e0810184102409074091070058100c0c000c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 283218525 1250 283217275 283217279
    0x108061b0a0314090606090a061206020d18080a1106010612090f0204060b04050a090203070f050a021504062405060d0b0a0330180e070e030115060e0d0507 68
    0x201100102101d000504001a01200c19a0400001c00c0111240d5040340c1000c0b0400c242c5040034104254001c40e10542008010304180c800440b955944501070040c83e40400c02540f910b065520240c40c010010683c0821b0800c2483e2410f490f0f40440c56100010b4440840e108840d07c0014110381a907025860384441d0048884885005200c0c0d11000e46031130b03108150980240c1c0340c61042c000a8003c03d84403039070380c50910040c407142460355484038042900c10400c0009a5900c28240d00449105161135950b031002c0150032458400700e0040c14040c55640401c2c44100003e983c0604a03904c8410502c01031066405120400d21016100302d41c0c00890070444424507200f65401035070301b110018a04001103403aa01d130301d00160a0500d05560601d968420301035005c10301c64904800c014a0310300030041c0412260540b0400c0000d100700347c1c0aa252101080c20749000320b400244464000d0001c002050140a0705c682e043d60342c0c8141808a4084100c221413410003041350b144050b001001045418 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 283219775 1250 283218525 283218571
    0x1403070e060705160803090a1211011436040b090604051e100807051c0813090513030e18040b070302070206181009030b160e03030a0305010806010806 66
    0xa44054400c075228001d040c0180712201c4104c00da040980b0880000719242c40b69102400310448054001c0e0740d000c02640c801030b00084880b01d040608000a203001000014080c05890301405034000340aa15640c020b002c4803240d030300c1004000e007500e440001001940c05581031204a43d80300e15082d4101d07400d00d0010380d80741030540080d1b401c00301d800c44096040c0d51056030310381c0010081d518500e412584030010021030a080000300b0160004584400d4070303012180307165241c6503002e00300038120b00e008034581100c000703030407824401068800b0061010b46044100040c2c8135a450030120080748218078503004c0c034100340c203280f0910340a034480c010140d03c1e640c0f507120100800801c1c0c1000c26808016074401a02ca000141c60281400350b401a1440e80a800304416a2140b909031030030031a0070001040440c0701002c006800c00d030100015040e400c0b200c4c108540d0b444201d000a505440005034000c51903905a10140c122804001688c00310390722150015140c200594810842e441c0004648803c0c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 283221025 1250 283219775 283219777
    0x20a0206280903080a110f040303030c0909061410050306060f03060f031501030614040c05091b18040b03160e09100609020c0d02070f0924030501020a1403070e06 71
    0x101e5601c5116444a8068078015103040510840c006000c4105103c1c410b80e140c058041c0002e24000101d042031802d02095082d8041c600c000707010991141000034200340500318010241582c118107010b066190b02240e0050304a40103902c2c002d007290009100082d120b601560f009100c02407409103014444d10b619000d03608060142540111500900b05866404000d4814115003c01e1070b04607540c50740c01e00c0301c111045001d1400e00b5641003000c100c0090304940740ca006560007101c14600302c4d280d071000b421103417601c420345507060000014650b103070114000fa584940c1104807018404d00d54144107040d154626080c8403492050400000c0c000040c801d440035a00072101800c8580e848400740d0388000381d4000b42c7c41000c0250340000c0b11100c080060100c0000004140002d10b02945000d000e4844031800d80b0440c0b444640d91407155008080000b0700c0c213610403520320502c1c1415203070708100e8000c3d400390400001041c800f591004c0d40003498420790384a2405515032000c0d880c0007000703000403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 283222275 1250 283221025 283221061
    0x3020603190f02040e0708090c0a050108040302013902160e13170315090708190e07081005280c050702060d05010f05030115050402070804080706030519020a0206 71
    0x90152500301d0b892501105201920003010143c0c0b12644d14103000030040c10b100c8002c0c08117903281c0c004c05014041d90b01e60724100c0089420a1a0040c841c0e561030804a0040c088019002964007000b409140c80d03804080c00c0c000040f4000c8843c5000e804503420590769607514200c2d505107030300761300313002c001341a0345848290740824408160001d541c02ca948180030740c0d50300c03503903030880d11004000e2112080401c1d00d52030000341c040d40c000c0b80a0422040181010344000c001280303040e018000c06801078000e420003158005c4010403259005d80300c3e41581d807a9000d00c64600c401500c0c08000951000206030001303141d040d001c50b120304601010380020060000d80c4400740078000c04111801c01170b128a801048a0000c3c0400010a54140544046c1103440c0b5840b1600c00d83c1011482c0b001c090030f06040b0422240304940060355184649048143e0340103d82c0030302c5c028000c12200240150f05504901c0c402c07004001010b507020440c400ca0401c9008101300100140d00c0307480090a001054207089213 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 283223525 1250 283222275 283222321
    0x40c05120106210204050627030f030705010506090c0a142512020d021005060a0504020a11060901182405011409151f0c050d03050402180103020603 65
    0x3261600c40e4844840c440c40030380c032010006180401503000020711120344480e21941d0103007507181529110000744c403406049031884824040f8550098901211040381190a20260649650000c0d01c281140c81c2e80180c2001d42daa035003460700051444c2761480d016889908081d0140d070411805000844411051100c00d40352404100b04a0018550b1b201000a84015950a030b400c0010b1038500b64608040702075145040d944800d040701140c2c0d802064a64040b2a864000200340e41c40900250300b102c05076000716000703840004e080b580f2a5004100d05008260941181e00396101c540400d8200c03640d00800e0030301e0080070122100011410300c048080721041560f0b040804042590361412a0310a9200d26802c02e504040c594031410307c00011503200240c26418612281c100011032040004000000a111010304054940f1401454008809904441118200010900050b00034141503030203910618408098002252880b640c45060300d6019200c2402c54a0780f00f54124200f480c0c0007142 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 283224775 1250 283223525 283223527
    0xe0d02031909080709020a1205040b150406030602070b07090f050627191a0909070c02061303030c0209010e07090603020a02010f090b1b03091207140607021e07060806040c05 76
    0x34a05004c02a0b031002c1c0c00a8400140d5907a1816009400021618107112202e41804100070101e4045c48850354004040c8014046d1038800d04e000a000b40602e800c010b01c1c3d5031010442205000c1c0380d0210501c5a40c1039120507a2aa8640701d00c1c0c02004014031600381d00040030401c01d00c40c40060176605603000c1550705007000d60031224002a00459900a8499981180c01400c2080e982040c01404206003131040851911400102260f03901c24020880c1c8140818100e400d421500c0d618116401003145040301070600d074072031400401070810640140d214408030b00011816881c0c0c8c1800703034044c60450700c1d105445403900f4400e602035040400c1103403c0d9540c458910404503491300800d405c0c1340c41002054481d00d1f0010f8225003c040c2c0c95941e501042c018000c1103202000000d8980d5074801c0c0b01030183d2a402c4600d0300142d0304030000c526503200d010b0303d42801003180c3c0014541e0205401c0009a81c4e066a8118071690740f91464460400010701042c0819400e0506501002c0c0d002d80a203009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 283226025 1250 283224775 283224779
    0x20609030a0c020d0f030c0c0501030e0a060b01210506030d0e01080402100210090305030901051305060a0203152112090a0e0a061508150604050114092d01030e0d02031909 75
    0x803000d1700541d0102a008034070301ca80b40f4070130445580341c02c402804007400c082001a443c1d46001c0c1d81c90911010040c02c050ba90021985141c1c00780e048110540000c404c42c14880e442c3c0c0001d00054030098800074000c1c41501c1014591a00841010403003660607074407940a682c0b40e80030400c0d401010102c140640c010f1805500500c403442c000e44038124000d031a080d580341481400c907821120020400214860b004a1140c000f03440800d4850300150305d5180540c981c3c44182c10300146001010040d0f50028904008101d440e0081001401380d80003030b800c3c2c03012601d100303030140918418007900640c841544802400034903548120b4581025030007000069941c4c070303008180c0080c0340005441c4c011408010403c072070006000c10302898494282c4280381040d151400107440d01010b80e4101d200002d0104640c0403685500c0d40d5495541c51000c802141c0d11f018103420044560544140380c0001d040028103440103000069020398040d0b103500641c68010310300360722205030200211903010011a0200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 283227275 1250 283226025 283226033
    0x906071106030a06031b0305072d060e04050a2f0904020a030e0f07080c010c0305070c0b030a0e0109120e0a0f15031b0e0609032104080706020609030a0c020d 69
    0x65840794007404000100142581014410700079103850a1b50154900c88080c000031318040303240d20495002143c502075000070340c08000081c070b11002e00b0b0581c00d04038900010302c1740c3d44001000110380081c1c4082006868000610003504d0b075102d00758410407036102100e01440c2e149240002c0d40c194203c0030b0390070241c0c4940043c050740c1c42888045c00083d1a40440c4920810a1001d03202103c5000300800113245401502c54a031908aa41617042c4010003000d2410305001e04100c442d185d50001c01ea660007070702e03030641004580046c0c590191151925590b8954404140308281c4080d80180d002d0360b100e101054101ca0b017107024a8035980202e00c40400188489120026002414070109002c021003102000241181c0811904000b00c40c0180b200f00303105900304900140140c41941c0c0c5c1e039510030016001c24901000074009600ba00030200c1200100d03d503040c05032060b50701980c00c1d42c00d22540c03458220b0303481400360360700c0721240c1003002510030180c0100c54030100c0c284040c002c9159845036441d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 283228525 1250 283227275 283227277
    0x60304050709110304030206010302040c050f1209070914130809090702011410031e031107120c05040e0312041a04150b030d09061115041b09020306060906071106 71
    0x240031141a44010780038807414001d806020501400350360f40505528298030029030350b04040c44040e0249036100c0c013520301544102c08031030faa901e0003141142c0d560920103250b917280204683c2c040b0a4000c40501060303094032806035a040c1041030b020700480746c03220440c080182e054000200c4500104001402c11605c910700428400c1c07145d60000030b80d00e09210552885c9200c001c0070044c8100c0105000c1c80010801210013824842030304011420192504e001d90b4800104000042c251143c5031001541c15400c8010080781403080c90000400d545c1c4806000650b400b985000030590018860341100310342200c1543da1160048a046e407080c0d05c2911480c1d2404019a015107000c00c00314906800b802441c0142401800150000e029460000b41c00410f48000c9005030010000d1004401c030301d0120401c91012624038031800503d82d8201890321040c1504c0e507060260510b0740c1120700041d81c0015101350391181c4400f91134a4070b810030340b508000c41d640c011142280d0040082c4d10a45007078072194 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 283229775 1250 283228525 283228531
    0x10c060e2401031a01030f08090d05010203090a021c0c1802300f040506011202030c0a0b0912030901021209060d140a06090b060d0903021e28020d080307030b0603 71
    0x10940750765411410103d1085018140d2984c0c0d550082c4010000540c40c1008030a81f1078201042c1504e421340c00c00014450114918090035541c004018400104004606440700130b200f20390705210f1545960611110380d5140e1000340003110b014404000c0c140300c0b00000c1c030ac00d0301d010f10010329001002410740d03d007164000d40746904140ba444511481e201c4041400d4004440300804282407409585459a80105001c0c5800c41c9820070701c82c1085441c104100c0601c040e00906101c4c0f40742d10f80c648010140c1050400a101d610303001d40380500c0342d40100854140c82e006a002e00f0f12181c0d041e2000e003403a0305ca8400203420103401c01c0f82030034501c04c5105d012003e030100c0302d01c0c860b00d06298900005840d00f640014203041d10b0400300450700d030b441000b194524100d40401090000b001d06082e401c2040e20890800514500d8442c071440b0714000c90501001644207c00741801407900c2c1c10000d1201c5680002904104d00c8080400807400000c040c5600511515002c12040140008117074983c10507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 283231025 1250 283229775 283229833
    0x10080102030a0b010914101218050307021c03090e0601051b0c041a0a091d030d091203060303021009151104091b0c06051e040818030c010c060e 63
    0x30301403c0f8103941e80b0400c0d44c1d00420241e807281050102c41000500f44410b0345c4c0d02582400b0011003011542504c642041c228090103200c100c24034815400c01300d45a5016074001c03841001c00003190b0480101c440940c2d916950165108440d082c181000c41d01e01c1310028002c0c0d0f05000040c0715810ba490f03032002c2d440307590f045d0300f5019144107140c40302130000b61070f40f4100041112102e0440d200352a01c46800c050701f110540140406d01040c00c0708050300458031030760190301c0390000048090104000c4c0c1c01150009210700103031442d242404000f2001c45095000c0180103811100030900011003030f410094000740240d0449022030010308c0ba2504031220001040700c4a5404103080008504c2d0380301d40b0b10580410403848094031101e05000b40a4444190001c195643e80e801003464909200d074183c5210100e60115112404c2c03504084078170b50010702280741b008124100d030b04540e040100d40f0100040e4180c503540542070443d50707205c0c00f901d1040350ba02014400c40a00920406074055040f03240460 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 283232275 1250 283231025 283231031
    0x131109041208090d050a030504020a050301090515010b1e0d1d07030b0a0b031f0905030a05071b150e0d02030316030906051303060c0e0d05010e150c09010810080102030a 74
    0x1d2030308081d009510040c20340d40c07a50800202054103a07008001c0b18080211413070b0009140da00c0e03200145529005420450300b540c03030000d240c81008000503e000788205448200d125580c2e13907030395550315031160f02404c4201e6800640580c00034440307803020b0710044103405804510328281c1c4c0306105484040091040b40c56020300c40410030b2041c0b03035030301c2504030340194414090f501565000c0f0760360740d560701c0000c441d50780550510406500c05900280081d40c0c000250b80e558021b003c8000d003103800c400b0080d101d0703000c01810800b011507080e446c0b404403004c0465000752038546c010290b4900d805109116004520060500016a02070008003103544a6004805002119081c001c20440a42c0c001c0c4083c0700b030810401c82400c02e005c41d41d0b802c40f5400800481c00f08070780242110002c5000007201e400001e085e400341c041003010b4204010165200c01120740310840c000100c282000290741d14030f410713001000070700c82c107511600b2001d80c07103a0015650600340317642d29041e6089034021a4010400c5603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 283233525 1250 283232275 283232303
    0xf021e030a0c020307050c21030f091c050c040e0f060c0c07050108070903060504170d0c02060a06050a03020f15030c0c15060315060f03030406020601090f09050613110904 75
    0x5140b141c0c0d020310b200d500c01135041060903503030310341d0b1404803905051161400e000c3e14801c11290584464a07403200d1707401c3d071b1b482d40b0000c1122501030700020810740c401c016002074200c0740c0340f40f41152885a03070024010f044020101b030070f00c40113100002241c1d43d14080c411b0042c04480d8100103260145005038401035541000141705c5060414030b811060400083ca01070001d61a8841c07001811b89400000009554071185460300301000b03a03400c3d0411204003c18400c4055040ba40041940c2c8003e809a4040765607955444c011140b41d401410f0340005012414005030600c0c400310b00701041c01909420300c8050060b4000159001141c00e840718041c002194110780f0002d000f0481e0868003926141c1d0a400e244c4000384d00d03403104c2d1105400b41c103200750015006c3da843ca2843d01d188400502035a40c0d4603200c6000030345071482401018603450620310343c00b100d200c16210f4101015048409088542c940612111450482c158141d40c1c00400756001c5003603039100315200303001f9032040030788013641c030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 283234775 1250 283233525 283233541
    0x601091b050301060e0303120f0a0e010203100b0c0f03070b160e0d0b070e06030a02040e0624220906060f02011a10020f010906020306011d0102030d0f021e03 69
    0x6441103a191005406458202810540110569040d100e0304d0400c42200409840464914045c0e8000208000320748001d1190540349240180d0141402c6c0000380044e21405103003078280c0c40140d440d944200a2901d0410030500118081c06413100c8120954403a01d9000213180d1668001110540b11001d00000b407014440e0000400b004140c407070704002030141c5403900000c011400c1070038082c106940c1c40002031079580c494020a010010011301494888c03c0400401d0029000760080d0500d05000801003003851404003070b0866505880c2601e4924400210081c82c01c03504661901c0222048d400c03030b11035505000d02d03a2000030f0000058005001454000000e00d5402640c08480940e458550040d035a503044c0645a611001d00b51780c0c40c5540e01d080e0340104d103071074103014040b1655440e03c0c040c0410042035800440c00f5000907620b41140441c120044240d55290f07111440c051b0b8001c0107501c0d54003041d608100b10f410540368005042403180c40c880241d4083d1030a03858030481c0700000700b02d407071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 283236025 1250 283234775 283234781
    0x1207260a021b01050d0513020a1e06090308161a01081501060509130b0f03010e070f061e18050d0b040b130206040302060915043b0a09080912060109 65
    0x1030b80409022024809840010f0700c1440303418078a42042d9101e0000400c004036107200c8851041d8064580c01105544225000c11012003405e40fa0703444403810000110940321b9141c07402500d170070242c5c0521f0501140b55881c12420000b034112030714841c03c1d07494030003020981d098a000700008000b815203001e41008008003010141c000400f0b0020500000046440c2c0848070486601b16000000300e0403031180000e80d0705040450311a81c55820250003034940f0001040f40422110803170b54040b0380342d4480105848103c0240018102d94002078640f00d402c61084030320150850340040412201030300d0780c000c154010610507040e02c10407045806e00c03007003000d6164031590010300c0082448541d034490740016854425440064030408000c940300300c0c6503450720f0440035103001840b80c0d03659642d50384824600402089211100d500943d2081c10f0a904500c03030340403c1d051800411810030b1303403281d900030300800045034240e40c900360070300920f00e107a10f0321141042e0101c400d00081010303614043c009026 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 283237275 1250 283236025 283236043
    0x50703020c060402011d0a090212010501050702012703120201021803010501210215130807090b09011509150e09090307030509010f0327020f0a0303021207260a02 71
    0x8051040007026440080880e6040d00310b40d09190540000c80465020310b046070094000355844001c000d0001500c60140d4003c1000704983c0e00d800d400c82c1e0340d030360056800303000301d00c4082d010424141601c00210184001c1c0c0000c1030800d00729404803600ea131078900301d1ba415030070040050303036002070002000344c140c2c00303100301c840c3c0120300910456041154000310460000c1c80311011610380d207007043c11552150091910801c0903200c4a864410312030f0302151034038803446050b0441c05060408218950540a001544400a450012180d103041070003041003119594220030005d680702c010a607141c194000c1c00d40c42c001c65813142d030b00c003a00104106040c00c000d0145c40705a4410003109000a0304041910007091003401d00390440e100f003a0b41a00608040900b4000c003c0d000d480c03481c0101820420913100b58000e50384000742d825081d09000b04005903000240141c0d200070800d04d0f00d548500006c0c80024031414039030f41255200002d80359140c60400c0b5241c50200c02241c1e01080301ea0400c0007041e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 283238525 1250 283237275 283237277
    0xd180b070201260403050d0b1f11030405060d0b01260c0a0c051501080d080907031704080102070b040611090a03060f0b040509060f100b09010804080c03160b0615030f090a0c06020708010507 83
    0x31509c259070418800d007030f40d420000820700151041d03204030020280251401044050605640d410702558140c00a0261540c2d540c00315251007206109070213505010050140c01c01440500d07500c2d03907545450305802c100c2e40481003089025003000040c00c04d00030400321515143c00300440d9410a580f46013007500400c055404c000b1320100300b001e81000050000704030b81e084040107000384407003805180240b181d608030711200e40c000076821082103280c00070f40b0f10583c0641e1080002d0b284003500c52209200341c99046070700008540c014008101554815000c0031000c1c01c00140809007540803070290f9034201e0300450160465006c2100b8591041030301940300d4291215403280c14244159140140100c10b2802d0402107200d0004082002c0d00007111014000102204e03120f9180642c031202888030050101e4220b11124081540303420084c40316a991144904d4640c01d55a40b19128003909070000d000500314465488601c0c049203829118101a0000e540501000e43c108aa000c0c01e4600c0501444 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 283239775 1250 283238525 283238539
    0x31e021207020d0f140703060606050a0512070203091504180506090f040503040b03011404060501020712020f060409020309060403030e0613032105090d180b070201260403050d0b 78
    0x3400400d0400440c0c1c03881e60304039407403480d00b045402c0290307080c031404400a100703100f00d856600d9040800034403201103034402e41081c45941c2e11641c0449680c02070412240103d00107000b104402e10600e038181e43e211006204503070900e607050000a1402000c3c2c3e4107140c00f20f40028088c40301101e800004248410003030000e2000342400300114a8181c0014000d4005040d0540860100201031040314020f04440f003400340c0302e50319000c000c0741508050099138402e5151000c00142035002151000c100c9050409003502419103400307014200c1104030030194400760401c000700d25400c19102450143c05d441c402440300d442d140c0740150868a90f40a01441988070004006502144100754152a9030514084a40480c0c206e001218030120340500c0c1e0142d4240010080284000510084001c8540d42e0714800c0301c004241c43c8241c1e1182e4051b0b484094010050000554029460302d1105002c002d4440403d50800c031102007002c40030b80b4102c002940c00103801100e1511030250380000e13441282c0070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 283241025 1250 283239775 283239793
    0x24020417030a17041406040602031512030d0b06041a070c14060901050904090c15180f050603070c1a0604051e01090c0c05070e061005030106050304020607110d031e02 73
    0x1074620a0603c4040040c03200c40701c0010100000018803401c020051000c540c01ba007081e240040c0070350801ca8025400d801c0500c050007107890440c41c440b100c10003000c0a540340c020308500c0c51005d4243c0b246081c0e0004810000015002d141030702142008040700c0210b0303116000c503c0e041d0000c0c2c243c0d81c02480358000403d900c407290340d03518044550ba203000342800d6a58a00c00e4021038040c02d45400003420b112004480019144110007000d00e5695903540c418001a198109140500e5514010030740500d139504002d20030703400c14400031034010420341404020710717042d0380c2e90600c41c0d0710203641d6481141e2200d041c4880d0703003080d01816400c42c03c0c43c500000070b40c118070b000c2ca0704a08144030302c6c0d4011391100014a1058021110001c20301c2d0040d0a9540c0c1e039440c0c0c0c1c032225011400360703075460240450840f038468444c814410b8905a03242c0d13a07505403950f2529000c000d40ca40142d08241c0320003040042070401c56644032070b00c194180c82600c40d061188038107803045001c00c024030010313410342d0400688 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 283242275 1250 283241025 283241027
    0xa050f151009051003022701081504060b150a020c03011b0509010804020109082406010903170304082b1104050a051c0c180e0d080705030424020417030a 67
    0x10081a03480b2000300280940d41c1c0d00301d240100c1450b90001e9000405038102c0108080c3daa60b080f40816100381c1c0e83c5900d070740d071051402d0381d4000001e80e113442a0f01d1600030400060190300400404a4000d08000705030301400b4070301d035550b405110040d01513400b805e512415410300703018000242440b0340e480c0c03015000b0780030090914403c2c0c2c0703c524100291403000804580c01500b000026041d0441100e030200d550704800b039110b05074280e0400d0020754a00000d003066108446e100d058a0380310010400754581000781000c0c1d500042c01c01c9580350014042801c2d1006c280350b150724040b1240452111141d4055246000c4400081015400120420060005480d9a5010000c03500305550300c5840d42c0746404100a09140341c80b004020300440c0000244001d007840b150041d030040e18000700240c819681030a580d800d00b400c80307000480c1d00c2400103024580510055070b070140c0a900351140c600310841207500e110000188860243d94082002d101d004031904403480c903546604000c501d0480c1c0158 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 283243525 1250 283242275 283242301
    0x20901060e042d05060904051903031b1d04050c031605070c1d13031706030a0b0c04092426030f180d02010e0906120a050f15 55
    0x4410620101000c44035850321560700082c00c00000d014991040400f283c60b00900c840990141c3c84040e0405011664510308229000c0c01640c0c060002c00060001000b00050004055019020f02d0f41d204100042c0710340402d07600c80595003640c0d9044500c04291102e940c02c15440c180c40d800303680340c04104500300402d071040700e4102c820b94668028441401004460394442c0060040c07004200d46000070380f80207019001038204800c580010000e0340c4240c00c00c040190500400b0313001842006070f41c480e46242842440e00b100003e410358017244000d450355507180e40c0c2640c206014407400501007256103907611030145415005603c83e000045d8410100080302c200e80601c4a0040700210009840150200410808a4103c00b520b0303c0f6450748100c5401908028507642408640c603c2ca020207140000b604200d0aa05860b050758200c24070003400070480e0020101d07170b00007030000507401661000f0060440880d11501c002c042c049645407210703040101d5402458000183c800611822040b001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 283244775 1250 283243525 283243529
    0x90905040309140f03030403050115050607080301060c0206121614040602061815090105010609050103020a120f060911130608040b0c070503040e04031e0503060d020f06091908060c07020901 83
    0x20f010701c403800392440000380c0320000840725194948000100001041019001454103c402c0024000441d0f69103080c440c0f00e100d40100103114040c104018000035009015440700b550001c1c00d12810923400c800e102400300c0040d0f600600641c5183e1015100c1c5601c00c81082906646034501ea0810303260800195840303a000e4114403003400141e2003560700000c204a59807207003080301039213071681c18400c07a49402040c0a0003a4400035030030754408200c0354000d000b1104046100da81e01c0310741d03100784100f0100074810f048105440d50b407038200008404c8a81c2c002d03d484142c41c008100e6640f0b0106860041480c055400603042c00b48007010000494440210180d00460704103099640d1481c92401c2400c0d48582c1d00301c208074400e0f81d4180010705900142c50a003004114000c16030440e03068a050380c042c0800c4400c03036800300f0812945001030074981030300c07920158050211400d141004c0c0c0080da0301208180d01622444081c041009010010815503800400701d004007841c00c201c075000b0401c404014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 283246025 1250 283244775 283244789
    0x20f07060b0636060a08160521151e01030605090106020a030c050a0b040f02010314061f02120d0506031005010503100507020c0a0f170f10091502031501090905040309 73
    0xc06000240d04140d014050b83c81c03007004202035174a0360440000b80c400d040c103440504a072901d6081c00800c00d40654115a00c19a030340c5c4001100c0d203161411100708441c0102618900d00d251a0080341c01e4848040c2454000c403401506542d03c0034000004007105c0003544024170498510300100003103034020508114041d0145040409900036003051454445814030042c494120700d0f0400003807000310142001814401d0b43c0034482132003006052120700e9070544000e60f004001d1101c40c42107100f00340c2d1606510040d40181d8a420300c50b103405c3c6050b0b801880b040300d80795803140100001c51409010108504094042c00c002e29410000402c0c1e65002094240fa001a500c00c04101c1b000d00070060b401c039901000b084050940d840e0002c2e06040a0b051141580c000f002160022a1106c0172504003101c104017002419401c00c401d2251001e010310b8102a200180281c030110f000c00d980740029032041407144010940620401c000400c1ca5209a000104007413920701404002980a00144116259 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 283247275 1250 283246025 283246087
    0x906150103021809180d091a0c0607050a0212040b03090c01090308070f0c09050a0903180b270a0f050f1c02100210090f0b0702060405060127020f07060b06 68
    0x28141c25031305070310315105042c00d480c8100a8500c0c1c4550380001b0244c02c1d41d071141064216149a101075010310f02440702700004541003c40050025072050028103081c5d51544120b860381154001c03070302d4550f4004e0708a0120750ba000003c111140c8410024040d50102c01e18060f00c03860700e10303150701c403890141e4180181804041c401d1007051001c4140c1c20380141c0f103100c0041129080084901f07000f0700c25104201c020981482e20420043c15480220040b1480045010329020111404140421046a00c815041e80300d800010594480c020b080006d000020701d42142581010200608030009800040c03060070032200e0001411213298051030035542c10b03100b5030280c8070103860903401c2011164400c0038051a1081110034000d4480030400d1081c01142c000b2038031345401b01c003245c5808003100e000d4001d0b485840100300c0c40d8004401222000320b01c84181d80d2540c6040c944100b82d0340118841065100040b840c9401e0142c94424102004006c4070142e182c4072002018000c40a0128a58106680 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 283248525 1250 283247275 283247281
    0x10e04091a0f10180207020a1d010801021309020903010917030103170f160c0302100509040509010225061e050f0601180b0903010225050f010e0a0f03020a0204050906150103021809 79
    0x191380d0192007010f680180207800c01034845000000c14141c2064003100c82070743c0b800004142c0b0701031003114118203584040c840c0807801e041c1c0e4030000e03501a0701a19003540d42c900f900400300b200c1d80c14141c602c0e4040c000080c2e503549582401c100402301c100784603046007800c10406c3d28001c000401c0360f00240c5103030890390030310300300d410b11624407100d541c4065009440840c181c4070080c0d020004101c9088100c07800c0105032503000009080740184004c044809581c00c400a800b030030b600a520020a00c91040441d050710708821002c403900049040103078084d01d503028002c076a80c01110740c9138042d400303181c60201c0c402d8482c40311025040501c59400c641c000002d0008242d2801c0d01150000c1842100568441d00a500301c44144002d00b00161441c3c0a50201004100f8042c0140d50380c040610005000d00c03150740e1210400150294811429845581e42c01001602c9034001d0910642ca40c60292060340303803110f03010903040d540015040c1014410080d07240010500701024811220585004143d69 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 283249775 1250 283248525 283248569
    0x2271501210219030b181b1603030e0a050606040507020c03160608060a062c09040b0105010e061608180d0f15050112060b010e04091a0f10 61
    0x4074a006981040095000700e001e910a94005064a590400040b511842505812800c484040c4489a40b112090001c0948262070a01c0035400100040f1091080400c0c8142c100303465012a012159010601c080102815054461000e460080c2005003080c0341300c6956168451200070074461240d95202c01248d4198820031043c0d06c0c58102030112800081d07000105a0301221074070411002a140400040c040c0c140f841d41181203481d148c44020032074400166400b003220703907001800168216200784607031566841490304c3c0210b02569501a02c0d5051030001405101d440711818012001041002c10311a41c24810100c51038020362019100c881050511441482002882c0d40c41070800b81c1e043c060041741d240500c7c2003442a600c4601100c2e041846105507802403044070000c1d13003a0724050001c90300c180c12596103010149000b610f046003000008048070040789041d14400d107414008510310080401c030a8109002901036210307860b15403000200c1d103d4a014800320b000800150300c000c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 283251025 1250 283249775 283249787
    0x1003150e010e0d020303010302091006020607030b1503010915080d02030a12060f06180e0103030e06090a090e0109060b06070206031f09021b06061008150a080f060402271501 76
    0x2c07814481920440088148003d59a4000780400e91282c030140d07010420040c00903104404603407054002d010103695400c0198003c24001e1602a00002c0303149503000100a110007c6021384400c14000400c01c12600e111419180c1c00e40008030158401c0700c00003201038001094907090100da241c801d100001c00b45001e40074111a50008500103060317403010a0517600300c0840101080c4c411000440c417680d80c425005058428400607004c14110f4100e1611400c1110062040640c00b512446001b569091987e04030f8403044032000301a507503000304a080100c9402202c2d80a0802c450b641d08101460b000104103210150030a040700450034078100840c0d0b8a020000005c28007080c1c1152902652600c0f080c21012078801075005004800008409241c1341c3d0000140e102103603100250b40c0c1e107400c40c3c10007120201040356804500c0c40d0740012990410040c070b0315080611406401c07541030920620003600c0030160703409021554100f0030f0343c4001e01394810b00d0b4003080d03405910311554401d000585036 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 283252275 1250 283251025 283251041
    0x15020f0f040312020d170a02030414340506191202070302030a080c120f15030109060e012306092203020a150e0303010510031107030801030b1003150e01 67
    0x8a00045400000d1004980344001c90f440c0c10f800341c4502c00e000c080d0803140c8170a140c020103070b001380d00344c04640c9403078455010b50380c854400c0328007400c032145d100c00d540e14040740310340780c3c0c03c1031160224403103091614116050042c400e00d02101000b28117001c0040c80602039188003100c0c1542e5000c100c1003207841107004a16400341e420003150b4507034441c10f0081d201d9208048a07400b040f000000329480143d024101c3e006032104041004131621180d41ca080c030980080c1101000401805020388107907001e200b0b800c0400d100e800c00207030003c442d803103460035038a00403640a50050100f0381c1002c0d440400b280964890011540103c1c140d8920109200a058051441c0780e41a2006210300416400280800c00c00b030040c0074a40d00107080b5808141502c94582581d0441c1d08103000400c20b5084c9040c0230f10700c1ca41182000b080d07800302c10301e003840e040d00052400c1d400206035000420501c05040802900001551540a507190840c5c0343c032a050b501074980301d001a41d45024480c4440001c0d80100c074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 283253525 1250 283252275 283252297
    0x60906050408030f0901230301090b150304150b1801141903060b03010204090f050618100909050c100f110c2d10030b01031b020a0305031e18100915020f 67
    0x95a600c04003d58480e042401a08982b41c5400700d44e0740313241781440010903000381c81080549596103aa5030480100310702c18125615a4582003416260380c3d6800204001c4000035120307a04c61b6150000716101a003a61105501801c0362120100110300c10103c00030590f504090042440004c0c5008240244181d61007400e88600c0c00c800c0c01e40c1c01220b030700718134012042280d044500d01034800701504e000d14196642841c400410404104803442c82e089110700c240101c094490b04403203100451010020003c0d0b1100103401140021107040d081071550f0703450000c41005040c1211240c0c04140c118408807074188c4112944550203034151494500e40b4620382e006820044000e18001c80070b0003600c04004010301103802d011a4164820310122840c58400d080c1d8010000c540a036142600c0540c8090034481c114507200c40c0706107055510060702d07400340201340104120200c440701e07207a05040364130140c080c105041c280728501059098801255a400da00001680d17414903860340411803003026800c2d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 283254775 1250 283253525 283253567
    0xe031905130f0302030d03060e190603020d05070503060112020a090f0f0e010b01170f0103080c0a08070506041101052113150b01030608070605030f180115060906050408030f0901 78
    0x4104440c40b0040c00d02101d00c20780841e82941a40c1c40c003603060701c5103800360514003403081300000c5080038401110706d244142100700241c5981c40c0d80101d2403c2102036003e440d40d0340405d00401013410100505c074018034103038240c0388448150343d0020b42040c05510401d01810707103800300034900412643c81b4100c00114046c0400948103007884076406030000304151400b003403e000300009040c8280c000f55214080400f02c0034801c0e8255514001036802c12250386001c3e00c14403102c8030010784108c2c000c04119002d00300400a80c42c05282098080f6040c140f400d04005091082d03a1820307c0c0500c0000d80c2d040d1640c1d905021383e403a0420003203814006e034800340002c0d1160102c03150540d40c3d60b024144880c4207030380920215448080301a91001688183c00004008200090308200643c2d250b9401c42c182c40010440074181c7d009090139507a6010001e07400c81d030220810000e80790440c3c2c01ca4024002400c015080c1031a150329181c9074040d540745419102070008032202c01da803060180030b4400044008072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 283256025 1250 283254775 283254779
    0x100c09050904240c12110f0403080c060c0c0a030e060c03040303030b0406080109030c032d020616020d09170307120801140301090c0302010509180118050a0e03190513 73
    0x119849400010f401c98210300da2030002c44040880c01407565039440e544520300901012140b40000300210080880d040c1000d100c1384000d0040c000003000150701400307015843d81e8000309030380d042c00005803040b40000c4081050280314500880d040444581600f845005403003441d021510314892850020b02134040001c02104140c0c0640c442c0c00300791000d8900300009600c1e0184076003210124400500420450355450300040d105039503104e400310328801480c0440c40c144111803603044502452801680011081100c44049101840300d41c070b0441c030040811540d8118058072007034442c00780400c1036110711039196500c00c0800c2294150342d80701d44503c10804000701c0091000d0000c0c010120302c52056095000b0130b14050081c081c1c42504280800c0000d0301e0340e401500c0d81e9205181c0a60040290b404072490500420070300c0d4001d2654071031141e4070303c4031110440200c3d07400130010007080380b8010010a41020000950b40c041c0049080d41d07000011038002a100d500403803ca00703801c551034541c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 283257275 1250 283256025 283256033
    0x1810060f120c1a0c0c0a081f09080d050f130b01060c0f020603160801080a05030a0c11030d0f12140705072a090c020303060d060b06070f0f0507060c0302100c09050904 73
    0x2001e02070b030a50140c4805c1c400c5c0c08100300d10000244101a4158005039500840303a80600501e5079441d81000001402d83e195a214034082e0050004240306580e80e10801c07664405400000f03034030956000b4000319585040d82c030341c90ba101040c003a1408110701300704208200491989038025990b001006d06440c1d15114040d460724501d200e06680010706418000190100c000544c8500c07603502101031070825103014801c42d5004035881e8252440f0380c1c0e040b09101d19440c18800c6560600f00340e41d07030308042c11009502030440500141c070b42d5481841c0046420809a018150b581c0100c102c0c504643ea401c000e0505400d888521804019504580d030b4103001c500b001c034510340c0e04503402c0c0d034001d002d13861124205a071a80400c0751026048031703204046600048569000d4580400001e200600300040c80d15085000500d241d0119800501e030180241404010421840200010700c2c05190100ca5560000d481b000704000725517000341c81740b1003030151034011802c25024000c0030700401034910b040e0038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 283258525 1250 283257275 283257277
    0x18050405010803030a0c0516020913082701180b0904060503030a2c010e010c170f0310080303010b070305130909060b0108060a0501020c060f0d02031810060f120c1a 72
    0x81e4202101b440d0103048a1b1090084054495001110300110214041c903000e0013909840100040403488240b0042c0d40043e91070b001514144010319014101c0c211481741845000c84514010f90521509800c10b0b05400d800302002d4040e5a0500c801a49a20340c04000c10042c0c6601e4114a40c1804041180054250b2201c5404451080f550010040000c000400b000b007603d1184510700040080c3c0b07540d801d9501428030b034044288035805020451107000079074030f20354006d118010820b600000038081400c070180305074406082c02e000910b245516185d0070180034810450000c051010101c2c400225a0072140010300814040c20280558811850854028400788080c8c902003a940c42c003041c150b0414004031403c0d903c06800400740e14903030404001551300312988610003c0420003528407030075020700203180900228040004c3c0007a0346411541003440000c01402520328081b4104200d80d0751481c0801107880e12114a20a030705030303040204110b400383e0001c1881c2a80c1500c507800b4452044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 283259775 1250 283258525 283258531
    0x3030f02070501050f090103090f020a120201090b04290d0f0207020108090c03070603180203160f0b03060603010b07021f081905010b0d0b01020a140601060e0118061805040501080303 80
    0x150940c1e0000b9210001541c990240d190358510340c100611420300c1e0743d4041e50144102900845404504031520f074000b038200384190b0084c002410000760290110350300002c446002e048000010782c02c0c075041042e4851015043d40d8403803148901d00c1000c081041b41034003126000c0101003418007243d054008403201035071000f1000ca00151009000803141580416001c1c41440000c7c084c0c40004d00d44030084025050079103140c00700300c480350b0000005036800c02c914003480c0c03244030351051460314080d00756007024102c0e40f045182801c00c004020003542da40040741e040d40c07242942c56448038000d0011844d031240c00800c0c2d0000c1d07000160900f04107078100001501c14401e4400c0b01c548004846001c105031042807144510701c61051020b6602c4102c5c50304a583c01d00d0040c8102c46d6680c0c4039850745202181c4a020008050b00080e006000c41d03584500100034070f000a003070400500220001c0d403840ca071024801c050030019a12a0200200c406520703a5005150041084c8143d503100c41555803203030f00503 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 283261025 1250 283259775 283259777
    0x40b0c0c2b0509131d06100e1602060c07030522031e05060105041a0303190810030503030402090406060b0f04090b0316090f0906050702030d0e1614031603030f 70
    0x40495030030410310071000c44440c1a0043c04070251112074804c14405002d090b0800038440d14848054084680204002c510510b11207010005461420041d20300d40500035280740710f0301000d0404440003c0d000100e01f41c10900091030241d8801c900e080c1101c1e0340c011000441e18401c500702c0051388810981c4022029207020349400348148500584040c2d2a0502d050014281d4014200403c1540b6242e4030209010301e2980070f4800703c0e45484002411944042e1a10b0004090403070044125680010741552044511502040641c1181c684a07660301005000074030480c0604000390400205070084002000c0340415903403150f5104542903171581140c090700390124a0400d805404d8074000454000d901041c00030010000d00f0140070002401813817030b510440f5515015681c0001d250740c41024810768a075400740d03840d1403500b4548016100400c403410741c25403100900c01c4800c2100500c0c0d074210f8142c1c0103401440c26007440464100400750000c4542c20000b5400002810380290b10141c201c242 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 283262275 1250 283261025 283261093
    0x30427140402030607110706080901020d0c09031e0f080a030e1903110d0801051002150717100501080a0b0414010305060907060c03090e04061806230f040b0c0c 70
    0x51114111000e5000001b0303c141984422030810070140a0000c3c035230050005070000d440c2c02402c51199050b40c0a0480711000035107000d8081080c8038503d1004d40e240042030985110450300368507810010512280c028018607030010303161004601990200c0a50344001d41600c014034038014021550507a011400d40200b90240350003140342101107480004440d10340c841030034990814003808030040c179131421903095110304140c887c099004c41c0c1c9682c3c8608090b640e81c41501c03812031440c504284026044080183c4000d50074005030780c010603500c2e03018200c0d541c005031303040048000a010f0240350908171409083d2100200904c6800301d0920b00c80e9501204031404255201006c41d010094001e0180008007003032000d1121080510000f03806c58010351002c01c140c1d100d401d00300c2c010018428115045595812104d411070390390105120344604c41d400d80d211030326200081003160140100010440c0c901c80d80002c0c0003504041c181d5005101c504115280500b02481c03c040350b034201248400354481c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 283263525 1250 283262275 283262281
    0x201020c010f0605090f060d0c080714040e0c01030e0115090f0b031f090309081902010f0c021305090a14030414060304030f080a06051804060f0e0304271404020306 72
    0x50b990103684200d42000e00442015030340c0881020b401c40d80a4001d541c0159005030348c0005c5607800c030030078001c1d05000000e881e80918190441d0340c0c10090410751405030b820b02070070185030200410550020b0000f070030b02081d500c070307d425054010404d05d403d419168140150105201e40189d10511080c1c21180d400c00c0b40d950100704240d84d45510340b40781404251101035200c400c000340d0308070b41c9640d44a400c08400550b1190202030405280c1c2c646008011024013040c1c1c159039025000b21048131850408000403a0a6000b1071540e8049014a1301c455031150080f0b003440d00c040012024464000d0f0102c0d42d810342c624400c41d120b500502c1080d01c450400c14148440389881c50031680901d0740740c1c0320781111003103043c0195000c580040001c101d041c2ea4841c00034158983c014800300941d104d042c0c5d1b0500e0300e4079140030404c8840e08103520b0030580c0703400143c2aa00c00000210380698100c03554801d881c3c01440180c1403500c000c4d20080d0501c034201a0725940e4005e000d60418003580c8210140c55043ea = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 283264775 1250 283263525 283263551
    0x522080a03200708060c0a0905120f10020906040501051c06061106011a0307080901060503030c030a030f06050604060c05280b0a090804051005040506280302040b0702060f07050d0201020c01 83
    0x1241d01e0240c103400380c010708089040a078046c8014500010ba40c10f114861035901c80000b001c624a0385030200c0320381c0019450310115a0700740034844802e14146011030a0030300000c04182c0a00070343c011030341070003000124070708a03901c0d460450700f10303036040702e0f00740461622100010143c0941c0442c41b109446002c2c0042020b0100e64100c80140c0d5800d01c0060459070383c90320031540d10b600034005000c65543c43e2004105610240000c0160b928014010359070b40148040003012109403c0d15885941d1520b9428003141e41d4032401c45044030704034942260400314500f0003d00b02001103017420400e20058520b28181c1c90010f51150a69004080d82c5d45542c3d61070f420320b0240c9806010082051001b0032080c8802d1400c4107040c1d000e44042c0c980507040a4848001c0341c5598424800c0ca007030480c0e8070301807403c3c845040d0001e0701510702901d000c0d41854500780b00d0711a64040c0d40402486030b000464060710045c40c1a0a948040c2d800c541240c1c1c1c000841c81d4081d00075400215400c6c10740d401d00c2d08040030a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 283266025 1250 283264775 283264783
    0x1203091209080606011b060509010b03101a0103020c1e01060e0703180615030506090a020f0307061e0e030d030605131404110301020c060403180608070522080a0320 72
    0x452820002c1c01c0d05030b132608011150304113244195280f1461203c02c4501040c010b20841b44a60b425100000d0450340035010503107068030414000740c0d03040c182511848a01ea0030316400c01460300070b081c0562902030307200c0c002c0d0810320b180c0d940c0540e0201381090f0311511a8150015400c581c0366011041d0180c840c40c100b1010b9030702138240f182540d5241c04044c4000381a40d440f01c207004160348186420103489944050a1000903607129501d40c0c000d806080a600d403c8010380300780d0604800604001e49090b0000c0c0080d0300700d050104d981c6585a03010b803821401420450f580311801010340f040c82040e40000390080c000c0d400b484e4006c0205c0c001c18100604903100e0340c001129080110750300785e503850b030300c00040040018802c0c0d00b5540030300016005450402c210b502803440794441e40400100d05005550359171281e8002e008005104040c081015004800c54041507081c0b07140c0c0704050320b400d070700103400d00c070740d42c0000f41d1071041c40c082000303241e40206a650381019001003041007201941c10a691 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 283267275 1250 283266025 283266029
    0x6180f1a060f010f020102090d0f0b010605030f0703020306010201140703150602010e1e030d090804030302010507020d05161106030702100e0a021815060301031103251406071203091209 81
    0xc0403000425003030a44c003d0740307090082000e92002516000c03503d03010076500c030b0000b0002ca4130014050481e40400040e50b0381207001d89154035100d815482c2440e0342030030800c4050444c205050740000442d429034801e40210b0200c0d80a0351000f406403d12000c014000d110600180d015401400d1001c2203452060240400d00102c00d001030030440d60001c46000c0c980100154246e280c8010410700c42001c1c03403805081115401390440e942ca4500d94100a82034500040000d4215080b20040c031540c0754104c402d031075004850b0414051a910170785000042e40f2000d5004c0d50307200102004111080390700043e0038010f0380b10040140302550f640104507685400201c4000d601c130403503052450140800b0a6865440201d030b40300444010600800300d25150301c00c0c0c20540d489035882044101030304042108034180440700d500c1084085400c6529000c0580320300580d02000840403400c401c554412007a2000303103070005003058125000e403101030010190743e1021155460480209070b1000c0c015080c47e01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 283268525 1250 283267275 283267279
    0x80601170708070525030f0807020106030308130816080901090b0c060a0e100e0a1208190203072105010e07050a1209061b021b04020405010e090406180f1a06 69
    0x80d82c2c1d01c0d842c100390b80980010000411095040c605c4107442c2086280030729840b07000f501c903040c10812034100107100440c020310f081c007035a04000b010400603034804600c951004d0044018030844200d46028462841003040c8849030b00c0b5441ca9480030301c00850001c1c50002e40c2601c0d03044801d03039503100e810440c2c0102021039556401c10000101480080e8221103401c0f080303101600c1d6070f448542d05400c112010002c42c210207070b22401d400790400c42104114400c0300014100340009240040c0c0b100484c0f50b00c444644140343d004030102d10a1805000b054000784081040c1c55520315501c4201c0d8000c2409100300c2007442c070180080b0309070034010030403121207010f1540c40c8464081000568409000081800c4814681c1c0380200c6000805640544080142c55400b038181e0300300000c2041e03407500001c0e00b0b030b503c61441008101708507a00311555005186040e513204011ba0b82c1c6e803c2c030b03800400e2002602c1132801d803010f00c40000c05c25680d142c21465407150360710314280920005a071406510840c1c41c99 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 283269775 1250 283268525 283268537
    0xd05061504230a0b01110d030207030305060603190e1603140c01030b0a0e040f060c051201050f010c060b040221070810150e0a08030c1605100203090111030903010204060806011707 79
    0x4000300220341001020441c1070410800c20b48021b000e16250081c40070008000039800f00725030082503418003d294000004843e503900754100b60740e24100c10441a5003000b480da50381d881c54080c070042840917180c51402d00b280324021650709c0c1009114448808040b00440c094865040304540c0248280c00a420010340005007183c24040820038a040140007a2404c882c844151000100e142c01294501c070080c4e0b580c0c3d1784418070b40f982100002c00c1a08410710800144201a400d46d03400107090340c1450700100d002ca1709000e08000b04009224813800c04502d82200c010791760141204060321405a459592001210355910103d6036a26020307000d61780d942c03541d440071091b05a00c503a41c40c07103107104002c280413420340d03481d030038185140d0001c0040340304c035081101c07800241020001c000000744016110a40d0305200404029203e01c910141e441c18449101000c50448004005407400c3c50000b40007195a10740341c90000c0c01440c2c0480380c00703001500c2c0d000c0b200c6480c0051040c150040549403164 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 283271025 1250 283269775 283269781
    0x30408040317090405070309030f021c05090109090e010c0906031401060c06180c14060c1c1b060b1309031409190b071a01060806010e0d0506150423 65
    0x12411400b02d000e8044441006001c0d01207555203a114460007010b1584000400015605d000340c402c081d0001004250b420084989800e400c0d03001140d0f01c08509490702e141d607405040016950909683c1254a05a15001b0400c0040b08150b0001501c00c4071a01c41245030b82d650a400c0701500c08102c2082c40e000c9241c03004000650040701e1000170140b00d603c010032043c4461140048079200c03140c0603100b02541c160200030912103200c004686d002d054400620b002c1200c0c103515039036540030000d10440c81007070400b00c1142e403240400d08122002d0b07a410352003145090a0010207041650b170014031541089000e00c900c40310501c544201c4c079505440f0349e0001c69100c0b40d20044e80c0c2103a007525400072440300403807820311a5a41643c01a04001c05c0094540340076082490b05103c21200840c2204070303d50041c4282c5802100840d80710780c0928200d40303003a0060300460701c0b143c00c0d8a001040c2c1c2c801d25046c000c1c421000b41a00c0040c1e0429030b0100b000c101c4900891100341c61402400003440009404 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 283272275 1250 283271025 283271033
    0x150c040509070c02041b0311070803181501090c020d0e010c0b0402190b04080f061b1e03150102010e031c0504080702030f160f050a06050a020705091306060504020304080403 76
    0x1c1c0c507802405800c051803240c00715004503060304d0615207001d41070041c42081d540740541500c03640c4410f6491002c400d09140079907070354000c075202c0507180c460701c0001000c920203059000c00030500c0d05030740c80b4800861565201a10405890304e1105007005d03000b1140306100d02441582c1d0001c154105035182000b00c0b03030b140c8504803800800390059070030600e5100021841c40807070075880b0044c0515140b0a070f66030b150615040c20400c040c0802402a000796040c032000d40c028178003030141e50380340e1110300d82d6840e8420b100001e5901c0800c00b0001010000c1708000034562515a00f1000d00d00c02e80084c010740e030301c10300c1d0300d601c0f0303c1080d03185003d0010f4900e070400d00e01c0c2c00da4072607603100c1c2c40340e10740602e40b550030380003e0302c2d1080b10040620583d0085030582c1d110046008010300410034030024100030750800c2c0008484003142d002c0c0b0400c0010200e0141c211170b00c01c110580c02401c01070b144803030500b450026840c0c40c2550280036518981003040018190800f40308991207150401e280d1800c29041d641c1e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 283273381 1106 283272275 283272289
    0x102060a1103010e0705072306070c0309140310090b1909052a0a0e010503011a030309010e0109090c05130806040f0822030b0405150c0405 61
    0x4901e680340c48441075074152603034000381042640e680c4034215583c0c00784001c040c0c61240c1441c42d4914080a11b000000041e50f0101500e00c6941c401800b610410361139180240040c41e840020000c40c0c0c4039410a082001c4014191410800d001e1440c81c20356203400000d0b2640d85800d4280040000b0b1840d0317660300203813109401d01c51041d0580303549440d0230f40504044407042207010f091125548136590070b800e0000041030101d540d0344400c040014001c0074028640a5840c1440100c2503285511080449010040066182880140044540240100300181030008900000c10310803280c4c0901110031780951341c2c42d5200c40700340c1c80101d4180a503a00203902500541c0c20700011803003200b4101c0c0c145070004c110b82d60390b6242c2422642c0706655003007043d244969840c00401000001c60381c00f4001c43c0200100c0d0b00840608401c1e0000304000c1d9154a00520100070070072650400368 = true := by decide +kernel

theorem cover : BRFrame.Cov 283093525 283273381 := by
  have h0 := BRFrame.cov_init 283093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 283093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 283093525 ≤ n) (h2 : n < 283273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
