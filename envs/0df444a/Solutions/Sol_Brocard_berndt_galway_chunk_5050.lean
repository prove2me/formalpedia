-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5050
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:34:41.902308+00:00
-- url     : https://prove2.me/submissions/ec7227dd-7dbd-41c4-830a-6c5e0bbb9d5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 908093525 ≤ n < 908273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 908094775 1250 908093525 908093531
    0xc030c0a02010e060412080903070b0f03040203071d2403010f0605090f071403060609090901090b01083c0f06072a02010c0510020d0b0a090903020c0d0c08120405090a 73
    0x407015101c440500305069030064007441d1261408d00100c0c0c60510075820041d00b40f203011492807140c01000e0020b40c0309134400e90a850029581e914100c5242e010b23f4102c0104a545034001031480b40c44150021410b860000c00440c3c1080d500013080c04c441d034400e4108807241e2684020300140c1000b5590942008940c0024441031800c0200100604207603008000c1d40301d030000c040b69559480b60140d482d0403d0041840d6a9030a00000c090700030010b0f82c01c121106540c00000207141003004c40c0c0300c4000030203821211003004d194140381c2c6000301070f240e4009240381d103c0100d0801c80420092000c0c00c3c0905070051241c0c1c184000050020315040c0c0c660380503d103001450743c18090714582a802c1ca1039080c00d04841404591400311b080000c000e40300305c1c0d10b0344046060003802820350001d080119094501c0c20f99182c44203d00004d64a5024028015901c000360b85c01c4503003092026107051900800040e85401e440b80d11090808010300d1021180c2d55003c6020b00551428850700c58200141403010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 908096025 1250 908094775 908094779
    0x150303021b0a05010f030912030204170f030a030b0a0803030403180f1206050a1410090e030c031b0a0c0e0f070513090209010504080102070b01090e300c030c0a02010e0604 75
    0x50b9540e82a01440341002800760303084104034066004020341c5d07a80a24114101d103458513000300290401e100318070080803a0100c0e1030280d00003264452060100c0d10295242c160302c0300d000d1340034041111f00360380c1100400d440014090414005107005034803c1d614440010204904000f026615802c10040703490407071400c200441090011190345940300da13010400b03544481c000e100400e0024212002800d45600f0001600c1c0c140a1038020b4a410100030170213001e4181000795070780074002d4854142d03441006102d0307480704c110320b20310110304690040311450038490783d600815000f1903000c40786181c3c10500b444102000111856440b00103843c0507800d10b03a07025a0390601c08541d01c44c6120503940020560440d910600c1100d0181800c00c1c000d5580d002c4510307022450000074407506440d5803910305040080040890504071039031030740145440080070100c1204141c22611884c012824041040d00900e000501c042e2000300000c501030400502e290001411000c0b00c1400f02d071082c61b0801013 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 908097275 1250 908096025 908096029
    0x5091e030d1514100504080318010801090b060304020607020307051f03320a021e030a0b0105040806010b0307021903020606090a022d0f030f041406060a05130b04150303021b 76
    0x5444543c032011118601c4080322043d09540c03600c01d641200700d40e8080040e200e001c0385407083c810010100284e8030300034680ea07901400002c4801b00403400340c3c031400400100d17026152107400b03080628001415210030340c2c2c0da5000501e8800702e014042c1810280421458181c03509440b591040c034a07074600b115250540c01c09001c51101280c05e00d0944100000003180442020754103690003200c0314014440c0c54007801410003000d41044810418250a2a200e83c580394480c4055408460a041c01004c20342d0078015450125000241000d0462040146090511001c81048071910780203802030011414050280a081d010041412401d14010420400400d441c0e40c0b1441400c44ca0034010300482d030b0b81c659085410301c01c0302060358180b0804010702c6204051282e44034020751003002503400e01902d10144540700d070f80455619501c1418847e0400c0b0798100750816900103003455400040340c14900c00080e0888020a000c0a0b0340300e03200d48103208040e010412900c9140030401c1c10412602c0c0400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 908098525 1250 908097275 908097299
    0x17070b090d030c060e0f070315020a0c080c0307020d06020c010e011505040b06070b01030305030f09010606090b091306031115121b040f2c1905091e030d15 68
    0x50040403c0041e041c68000e01c011a0b000c840c0488504080d10010360585c2c4046036101094001515075441d540d00e0078050912600c00c55102002c01d071245c009003c1c040c3c0b43d460f001c5e000450762500d540002c1100c180107a440d20504225984998001a255041c1c40c0d0407500311240c0a00b40d0905a1402d05d400d02c0c00d5003044803440031654101da0204000380b125001c64020700800d2001480f20030035000200405802c44003070341c40f404803404850f00b0b079988c1e00c0d841401c2e9100e85c494940494481007050110020450041c000b602c4050450704010055001c81412180150701c00c0d658040200c20000c01458580107410280310110401401d0404507801c0295454000d800200c004405140558000200e41c06031801000e2045081410a56840781c02c10002c1c1c1030134003c41141b90300e0b60040c070b0444c0c03d45c902501480c1c003200c0180046202d442103400a001c05040220f04e841852802c0700d0200141032856030380e0308940007440d02c4e1600d0240c0703541520034541c8822160142c0900070b11015214030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 908099775 1250 908098525 908098549
    0x6140709030809030c0423060a0b070312180f0c05300a020a0306060501142802281109041709010e0904030e01081023030111030117070b09 61
    0x10301490340d0394403c00029140c01c8400c82903d40040c00c0042d405030074011080748808000c151458114165609003c00c0302d040d07583d000e11400b4000a0151001013031003526103034000d03103010000040141c194820004079068080741182c0c005440a100020003000c016001d0080405a841e01041e4000000e0b807030039449807030490501c115401000c0c0718690001c104c9030a8150300030703040540f580d4490420002030b1105000300c0c2d0200303500d1080c42883d081400100c40c03600031100c03415681011500c42404481c608812940c1c2184249484c05001c0075580501d5682030380c107900c40d4001019140307030a8020b1204400400e20403a60042007201051422080a080864440006070b58004035001600d120001c241080c0e00a401c6104010405130001210305401c03d00b6205c0000315aa41100304920800a028084900840c480783d540c20340342c840c03500220818010000308402110007426a041d4209a201c2804000d280c198099000303018000d4401500c0c980c904030340340819440c08a01c2d280051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 908101025 1250 908099775 908099783
    0x2301050616060b06120f01051005090f2d0a12050304210f0605040203150105150d020c0609010b1906021e012003070f11060a0e0f0f0304030614070903 66
    0x448010801c001642e0700c000c03d2840c0080106403a840075000ca50101c0300c04807401d002e06003490001294501d890300d90030300d0250f50760780c1c1d0314070b841c05060900c81c46540000040d07411006c0440d00314120311801061400501c1d110130f200d000310404c1d0381000000016070f4091451010054500e03004203102104450035191040b2034170281442c8040311038048520b02c18040c0514110905441c1084150340250703000d18000c5084581c181c0380c0f00750b0020b03a030200b03200d000d42c0300030169482d45514180402805088403044401070500c1c12140405003044411114003000b43d54800c1050403074a132840b540481603c401c650410401d0400c00044c2d0313208166101c400144144e120340300300991094000b1113011a40c04070810824400c89041c41a9400c2961a40040781019000019491091580d80d07170001500d0010245515014082c100900000d03030301503035502941c20701e400020400c009400300c103500b1030f00035a6110724505090048400180303104200c2810402480038060348170a080082d2600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 908102275 1250 908101025 908101057
    0x80105100f05160b060f18160e03102712030510090e150903162d0809030115080a021e18060a060507081b0a080d23010506 54
    0x14080305540500481c0300f0b0245084800c824101001000710136107020343d5040c1d48010324030800c001042040550142420505611140000c0420020861169001c61107040a07840340c036201c03002c00d04004a90300c04501c0191562840c2585c010690842c00c144e00c0060711b000070703d0000b40d0b0703800080d05000c10010308158907034002c506002403a980c404024000c1440420006d2011500203448031080078400c0c3c0000740240025210503404001c8031043c2001c5068082c2c0100e440e640c004460605c0240b600d11000c060000d08040741c00c02c00c11980190003615030303e4039180c0704001c060941c1c1054644580f014202102002441000503142ca41164100c640b081c0c0c0c507045500b110a600c1880c08641c0c0c0c450000c41c25419001055400c0724000c18054407100e0300c65440b0001915680306860004101c00e04c104000c01c910324800300401a1054000192000c3c50001d80351005182c10071103282c0800ca90303811031034000c00d03030100760340d541c4103212490091a0340c90500000d04a01401210108040c0c1d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 908103525 1250 908102275 908102297
    0x30e01090b04030b0f060a05010207031b03060c02151005010915030e06070c060b040e190507270f050105101103120117190c030807080910110d08010510 67
    0x8090040c200281076041600c5441c1c0c1d81e20708140e10180402d59200404112000c00700300c5500b0045c4506003a0b52060f002441307500c0c5560344d8801c8101d00f0582c5004040d03944071020000500324050030342806030320703802041c100300c10703540f0001c803244041d062180e10781070300400f0012641c00c40c44043c1140d44500c104185c9881e1340406030081c1850070707103656850082a0030412100d82008280782072500070841004600444018041102c1c0031711840700e4990b02c4041c018101010a43d600c0000501c500b05547d482a80d412040307404e03000c089000c0380c070031405a040340e982140b0303845540281140c0e00c1082c0300c0f40d490480800d041d1000c0c0b4903860100715141e00748420a040803c12541403103501081494150303550f04001242c090503100000d40d1b8004c03203c841d5240f84404000040c01d580181f0700380740d2245150746a00d007550049408a400d0310342071200003403e80c2c1e414002801041903484032040c60300700641150500c031448010005020390f00c1e0052280da1610303001070035100860f09099400708 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 908104775 1250 908103525 908103527
    0x201050c01140901150801060803041a0706020403050a0614070c08030a140108150c0a020d0507060e030d0914070e061c0c1712030727170c2b030e01 65
    0x150b4070392400c2c107100103800d0003011901540710800c0801040d44000031140c45171812401c0e1042c5100f000d40031350041c03200f8803c40c001e0a00890500d00c940e01250b00d800d502d607440600f81e800c03680c800d41e143e8010503411418410740c0c1c011540d66800105160003249003c0034087c00c00000168090045000800091070007586580040f4101850700d41885156942d400c406a0b41c1e141c1c03000300404d050300d05000c203221011030400c1d0703810b10503250090300c848074504c3c2003118950402c2d00152003040d2079045051a43d401417000b00558040c85802040c0704101d803c2c040c4482c0c02d03440f4a482a54080e400400690550f1850540c004500f2034000806240d034a44020110144a10141c0003055104000412039080c10701e04085010060945443c01c07030154102a0030f01003180c1c01b01c042150f01100403000300d14007085400c8032032a0400d40e0852900c0f05075090b8005030044c510742c290362112407090344900c1c0030406100b119006034801c20b20421100b40d0020041c0c103521000f02440203800c00f81c030b911303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 908106025 1250 908104775 908104781
    0x120303070807050d11090f01050702100e0604170102090312040612200406050d0b040b0904030309060f0c12060504060f030b0408070b04081908090d110a06020a0c05100e0a0201050c01 80
    0x20b00d44c00f44040c401580c0500780004541d100c052064400c51303680709541e016500540a80706d400d0340080c44040c5170301503441d0544000003054a820b500480030040420304d8550110140c00411420000680300d02400081c949001c00324000d80104040500041112551014507040e403075003240720118840041c820080c43c0503100d141e03a01012140494003144107540400600b540a203180800d002c02a60181884100c1c1d112005040c0c10088250000740803a00030f80140b407145200d00300c00682240da589000007140d00d00300000c030000b8108503040407960102d0280c42c1c0680011202001101d00d00b808900408115100017070000a032400050144950764040e200100c0d040349044003103103414502a4030984c404c141d0030f002c0c0c0c3c0d0119603e13501e20f4410141c007481500c4c1a4010800808106002d54510056101c20120b40c8100c0e10301000082c181d00181661401c1911400c0e5006514900315007001407500400d40d40d146010207000c40c80c000081e0b00580c8a40a00300350795a4080b0340300b82805 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 908107275 1250 908106025 908106037
    0x4050d05010204241d1003022512030c09052b1514010b03040201020a1104270b09030c03040608060604031b0315230c12010f06080612030307080705 65
    0x101501c0c2c013890f98220708406122900c40d00e010744e201e801c50310304800b1600103204c9140b20107030041282d62444d000f240c040d5006002032150203a0320000041c440340000d0454a074090120b500003041c1d0300440b84641c050013030141d0440c0508100e5212800d100101b4064002010610600c1810f01480150344142050041c1c0c1950050f0070010b88a03412075003075002e0080000d01c49103080c110710000034480c020310180e0340541d5059015201080c2c7c5500c500d08001d00c01c400e460740c001d03070301e010300048160303896460141e8200380c1141f4200b0740c0850a001074942002021807080e60001c01c4030340750b011008000c5406039143c604210003151100c401250017400750760001851a01060265682158104400c0c01240d00c614082d6201032203500e41c0a00351103040000c40390030400748502180300d0110003485607014800c01400c50070800d44440d03404104400382d04c009085140c080c42482425070080b0364644c40356040d41c60340000004c1e00107050b81c92100a01074002c100b80400481e500e81d1080007207850f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 908108525 1250 908107275 908107289
    0xa021512070503010f060f120b040e0304060c1203180f08040b0703110105070f050409021b010516090e010501200c03100b0a090e0601030f0f08030f06180c04050d05010204 75
    0x4064034222401900b19403080c011340b004c1c503518070000606140714000d800d1119525943e50190302d49a00c442d0805032280a1805034403544451400885120030009880100010317910b442c03070410341d8100003c94001c1d42c1010350805080c000d02c2400010301c44000700fa42ca501610120b588141818645501c2c0501e80014030310110001301481455881400d506507680d4420003048030f610740c0402503810f4140107081c1804a001030008103ca81c1c2c10394090300441901007050f06000a1043c055800c64504a0310301c044400200b10410700e01303a21000c040003400d00b04413408a079504140001e461046120441d400b03507050348000c104d2070340e801d0100aa480c0340140131203a010180f0075200c00034001c0243c020b40142c0544034009070304203c5014480d065400304002c0c040590039929400402403c42e4029600008100007400006410000851046010440343d4030b45080c0350042200c075a0300c800103105203070b91000620060681c1ca00464086841c02c40b0014008061494240d01901640d070000ca = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 908109775 1250 908108525 908108557
    0x204060807121e1a0609090d090b0903070302042307140d0e0f070306020a110604020a030204090f0b13021521060a0305010623030a05030a08070c150b10020d020a0215 73
    0x180c3e5030012074040c517010380c100303d4120000381c1e9000c9400c0d5598409000c80000202696010070504a80c40000d1800703a60240c00d0f20300c003d4036900803a003a24020b007140100d41220342448100a0341d4401c81d96002030640c03810489903551800c1c1500c0d24000c00c049181d020340c0d140000803003414100300e000402d15003a82034482c00d6542e420440021f41000141002103252800020003101000c5030451040794000c05e04600c01d800c580038800202070303140b0101c403500e5110240e8030101e500520b119103e050810b103100740015440c410301c0740007848004a00f124201c14001200e0080300e400c100000e0158802c0c043e0b88668440b00002c50765403080d840a01954a0040041403081c0091606c4110f00c80700303c5902d04400014041c180c0d104400300c2c01618981052101901c80c81c03040d46040d4100c84140341140728030803d500c8440800c1e441e0040c41e5440c6070340d00418980c80c00e1100ca861449481800901010720700d004003c0d4454011a100905c900798003151000c04000358400c0c1d985006034807581d5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 908111025 1250 908109775 908109803
    0x140702150403020a08031e150447120a05010f110d0905030d090c0e13050d0e0604030c080d0f030e031209030d021b0613080406030209010e15070204060807121e 70
    0x21005443c071448d4a18000e1f03040c01d0702c40c181e0880420240030150344c4030704202520186110054000807150b04140456038250800e0402503031008115649041c51001601694105191490854030900e141c800303042d003045070403c1101030910548540307049480b804103840d45146061401e61160b492150000d515103000c02003448180c04004007a1042303010801b01c0f0352102400e002e1940a084d00c018015803201090710344162042008562400000d0866410a51a0b60b19012000704540181c5044c0d4000d0780050011030380031a4030304000509041c20010380ca00c240c0f00d107032a4071454007178006c0701900d640802c00e070903810001c4032604505003204644030400e00400072007500005201000920a039004101c4000104d1160042c407075029201a1610340b409200f40d0203500700062090620030349400c482c2c2e03541c40f0441401c1c003000b5440c0b0010340c0c0e80e1b498410482228419006034100303502c000e0040c06040030480040c8101604008200d8060840304c0c21088448038210780141141c1a070146 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 908112275 1250 908111025 908111041
    0x160906030e2503060522030c061104061215060509060a050d0624030b01090302040b0d14030d110c0a06050c070501020c0304230a05090901090501140702150403020a08031e 75
    0x3541c1c00e0f00d10031401440b007a1100d40040c242d10362034400318141000f82e07007801c2000a00400309040300a1013584041841c00e2003c1c4011a15081a0300881c0800c1202040705411881e81c400c246038410b885100e165088d0920702d004041d03000e0000414003440300094980c0d0b005002c0d0055990115100d60244403d40d01c07600301600e004050741c8070003056001e000300d21070502d010380203249810f1010781d12100720502d1130b020003015205071840903800a43d44181203001c50740348004032803c101000011a91044d0303151500080f9030000314201407002050011041c10074004c580b19100f80e4200c10003007555111040010700e01d1040c000700074510340c40054030150250000c03000e03000700c1d921015020b40a400c0c4030404c04410415561890b0b100491007400e02040c03034001030310b54014140d0000001d5458099076007a08560300003c2054024021104100a195040040281c016038511000c0003c1c14180c1d4060343c0e0342c0070b4a600411102010000070190039244100901210601ca0800c2c16410231240e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 908113525 1250 908112275 908112343
    0x504060807050312121918050d080c090a0b030709050307030b04020307051e120c060c3a081b03040602030403080f070e010c020a05030703051005160906030e 69
    0xc211070203800740c542d0f0804c03c40e4504c01a0307000d1082050a0404940d00e40c65161042648031030f10800d6103031340b85a580c0303502004219154a942c80356008080768451040040c0c00300ca0f004242c62020a0100013074605501c80d14100021542d940d0085a20ba071110030091b208101c580c0c12542e054403400b04000203011880c030300d00740154000d40503505403035201c0c0c081c0039810030f2030314100d00496019a603101550500b054079007203000101058481030032007a400200c0382e07407000c0302c0748015511a1800454051441d0007944074184902c400e0400c0b16000c0e09003202c1110b0b07041d040700920407420001540009207050344002c840c1e08d5500140e40345400d2500c0002500f00313807030039000110541d0019860302c00f12103565000e015681c403540121130346940110307211902210201e0f0072002e042c10010305a02c0070003048018520620150803850b5242c00804102d580050400c850582040030881c485074004005d0703402c0e68907030f00c0d0200c0d2800200e250185821601d00400c40055403890b070300c41041d0b51400d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 908114775 1250 908113525 908113529
    0x30405031201080105240a180e0c0d11010810030507030c2c280203040606031712061c0b07020d1202030c1209070308070b06121b0405100504060807 65
    0x340038a200b039803500c40e054201c81040350248141c4000000d0328a0329000601c122403070384030040200100c183c41c1c00300180225140030b040a20581c43d103440512103201806420040b50701904c281500c0143c648800c400181510002410301c5203c1d00030541c54034030300f102c00c1d01842d0404100e40c1078a03603a02d050301d208451403180000c5008200401c18001d241404200c482092201c2c1400140c1c5451403020440a00440d441424060b00030040c01505420700203540f1950161034001032503880c50608424481c0c10394804051418200941480c4200c11001107030802c40070b0300c82c1ca81c0c50004001028401d007000030040c08101010301041041a0300041c068840c4c1401ea48074603a81400b00c5c4400268001078460460000090090004d0142800e090580c001014401ca401d2203550342c851500c5940070b000c050350342940d62410000d01d400c2c00d40381501e8004200004180101c00c400603114412050280d0922980d182c5011a1101d15034130581e50150100400c02c00c00283d81d1803540d13076540103074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 908116025 1250 908114775 908114797
    0x9060f011e17010501082401120e060a0c1119061811010e0a0609170102070b1e0112050309040905010219021507111f1401061206080d051210080303040503 68
    0xa4001061652088541c540980a002215101c484510340307048801f440c2d03621511704100c148020141400000e020f014990302d0b1040c0580400c3c00d2000050041d103860061400034004440440c41c3e01c3e0700001450010500d03414100962280f00d85441300180c4821400740d4101010701c254602804880c403610032200e2400d07200c0821880319407044c080e00c10703d10b10030440403403024030007040690000742480c0304a802810006191003266501c0c801146016504107582c00841d4882c1c6d600c17102d0003d9514050a01031800414070240340c0d488a40d02d10508140d0b81c0960384400c46c2000308807007501038481030b4040c0c1c013404402c4891084020340c1d455040c210f0b00091369608011903011405000340c000c0c1002c61202521207001240700c0303a081c112155504000059071440110611100d85c0d612034040c2c2119510030b0040b60044140f1002c0d500c080e001581140c00226203002c10b0f40d00802107496a0715150700c3e0011541da04120340c4800c00403540210194000001003000300f1501100801487c80e032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 908117275 1250 908116025 908116067
    0x310020316030b1c031d030a1505060102030f0703051e0301080d02280f0f0c090b040e2a0301020906040603091e02010c03030f02091e01030e030909060f011e 69
    0x2480c1040b003200c3d00f1041c0808003d000c8090303e0003091243d40c40c0c44950000c2e000500385002182d01080ca00f00c210401034810b0201c100ca6000b1500341400b2b45a00300d0780034401142811400340c1da40b119442400001428401c1c001460200c100c4540c0300d0800c10000e1540c010745075071751007400c2916240405d407208014060f03600d0001c5000100a1094001d0340d4080144070f40c0b0103156074035801c510b1221801c0d55115005012200006c000c523180501508400c0000300e01100201c01348029520720f0250240c46422810702030090b00c900340a503509224000140c820840c8a84020038028802c480c0341c103402c42400140072452030b415030015401e180c468001c003002d0070501515261070508046009002400350702d60310380440c0c440d800100302043c40300001441e02d0b4548000442d141d1001c0b451a040003440390201044d1b607014481c0702070401c00b000c0950307c0c141000000504141d001400d0340c1c0f040e10706004903400d503407240da404600031035010850780541e5220b01c00949840140b4540c0c1510840b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 908118525 1250 908117275 908117291
    0x4080718150902030a06061425062d0c020c0f180103080405120708151806040b07090902090d060f0b0303040f0e011205030d0b031c05040e01090c0f0e031002031603 72
    0x2202d0007003401240d0f03810052320700701070554082803481d4040e80d5481c500c0340e010390010004103030395100b2440403080e050402a00c14407141e110b03c0d10300c4c1c0c080440d0351405160041d5409506d40103c0c00a0014104560f001c00c242e00c800c0c006134050094410501098400c80004402c110a002c020301c2503038000c49081d004500c602198030741d60b000a00a084c07258008000760300d07101d0201c2401030703006460040b100c140702400d5400300785082d1003101c1c10354104c4405800e1010003900480d030700d00a800c10050a51500d480840840c00991041100405542d95291000c000c05c0302c0743e0000760fa624005040d40c2e9242e5440e0446030403142d080c010004841c0955000050a0f56148e240d9001554818041c41c2400600d2003418000d0001c144556054010885402d50700f23052451204076000e0281c4406480718203262500b891a0b1050b004070102078500207400300080d401c00f68030340054101c1e15295400c0d40c0d8440c08642024500d0160399113160001c0288907000f890300c805000207103c1c1d6542046005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 908119775 1250 908118525 908118527
    0x52b020120010b36060a09090609020907050301060e0603090a2102010c05040515070606050604080313120b06060c070801020d020418090308010b07030c050d030506090c04080718150902030a0606 85
    0x1400280c06226805051341e550304005002040a5005d10020311101d002030351081200280d030030240045501d01d95034900700c0b00314541425205d03001f2842c0d10b086c40c00c640c101400078202d0503a60604c0c0c1d22545020000034515141009188e4040c4e610607140c81070040c4641c1c0300b0388407601d25031003540554203046035a080d4612850a1b0740860741c00070040c1c0c092501d011820162980000c0341629625240d40000c6443c1d00c50900502c000c140840c011076989100c00000800780d1650703000354580c401103550210200c0c13544031010b5004034040702c4040c1e582e141603101a2410b10941d002c0e100d076500101d10f000600c00302c2d6002d001100c0d01d840740d991b0b42c5c040d1625078a0071111074060040100d400c010041c4000301070407020381040340c440c2c241403412141e0354440601e8a1a2400d600307000a827134108200141c10000745081e004001d49828904141c01c103800c3e903848468900852904038901148403e0208254001c040901a4608075401c056100d1006c80042d60044800b1054030341060380c005042 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 908121025 1250 908119775 908119819
    0xf0913091208150904210e12153d0504060605160311030c1504050c0616060f140f01031110020c041518060807052b020120010b 56
    0xb54150401611043d2401d100700080100b02800035500581008208111508035041c0c551240242ea180c9224545021040007800c81c0d403541c0300c2c0000e421401e034040141361900d901c1c540218409050240500094240c00d1181540c00c0c25800004140c0704442c907610003040b42c602c00d864040d1814080951103c80c140c480c1d00c1450f10701c0da9825074035102e02001c01d105540c4440155040c4054a21309501e400c19107140554030045220401d1100d818401003020400c140d4604030b8064455034208070610403a01c800e00c00c0004040c01c0d194440d050901c5107007842e030003145100c0f50900c40d4003450600754400100d03a10240801c442c014410a054410fa10b00703910480c003440b0b65540103299110907401400090040d4103144014500d0540000c1110f85800c1203100401030380e40b2002816a14203003202c1d1031f02a03aa44102e000e1540c1010310194030350200d00c00c0a0b0060134032030b800540c464510040b40c0c83ca699500c43c14410003141044036500d20107401140341320720100d450300e4512050355514404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 908122275 1250 908121025 908121031
    0x5010c08040f0f05071a251713030b0c030601121a061c020f190f1407140d020307030201050108150f090102130b030703230c0f0913091208 61
    0x500c42c00303880714000155030003442c141039511a106441145a0b50a2508581c2c4003840318440d07200c0002c10742e10661403100640b901030300395802a0340d01003851a11802200d815100b201c4846900c0040c0410029002e68130241c01580d0040c5088000d10346401040e1780f90700259001c0d400a440300482d9031003214503000c1e8000c607220300050b01303500d01c03d02d00070000b49520924100032802a00c000c0141c10110314806040080c404135041c80e42d0303014035825081c005120000c2a41407142c441c10030b00000d03901a503c6043c04004441b9540d40340c0103400c145041030b0750600b412100d4811076900b40400ca40c0400a80a128800e800a00240c0d0f04d5400c3e240d101c01d1188010404101440002484400c0e05850b5680043c500d178001858080202c1d9200e5000502e500004c46120001090144055140c460b40090809241c5240c0b0000f007503901900c03500c100906002c1e101c41d4081140b03e08bc42e0040100d51009100402d001a13034440c0e80c2001c009840898415251260f044a00c11045c42c00f502c0e03502c7c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 908123525 1250 908122275 908122283
    0x90b0f030604150e06060d1d06010512060705070609031b0606050315011409070c0c06030606081807030311150a0902030c061c0c09090507020f060612060f0705090d06020705010c0804 80
    0x40240c0c0da501c14846c50307801882900c0242e41e12615110746000c1990b0482501c102c1c4540a0072007507040806001c1002500301e50903a1a40c41203007044401d5070321000b601d1100b58046008909118241000c841180890301d04500d40c200c041444006c204540c2e00c100100da400781c003500c0e02c41c900c0c00748040c140c0e6802d200c2d814080c840c5881200c03880c5001c036800e03540030145040c0501c7c2602d403912140d070342903115042040426502c400510030070b500700c29420b501c4111a9011040f14108544958403103c0034440101840113000c03401440400902c000d45c08141101d200312818602001800050001660143d01030f00401c0c0304881c150400900b240c2c0d145086901c0940d254401c00000f400a00b00103408100300070075034030b000c1203004060040718003418883d2300903c0281c01e0104642c1c207040740170306003900c1000c4216102485160208001c0d5205819206225107139807003036001c2d1243c5c41031040295012981d40700e0802001a03e5024104083c0118001c024190021201307440840c0c040d10054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 908124775 1250 908123525 908123549
    0xe0a02010f141803010912020303040614040f12030f0e0715020327010e040216060e0304060c06051f2903060a03060f0f06091e2307090b0f03060415 65
    0x4000d8041090a502a0102074000985140306888480d4107e40f141d801100680000051000b802a6401005c0d20040320b514002c0050070316a87c2d0200c000c52030b4000500d111b21424003c8030707550003039010486ea4151200e09001e100e00e42c900701c944810042c002c0101704401000d84640d150310020680380c24144480201c1e000c18007480c03440001e864112200d50400c80c00704c0e401c0c001d60b252400945007110300401d0f080364030891490000c0a60f0565901c02c6e00380d038014002000850f42c004c0301c0c407402581006001445840e11030144050b0415032081419100100c24009040140741e03c0d41c400fa0055418421080c07030f90f0120744d10451000781c0d0001d52203e0520307814004034016070302001d0200080040024042071024070501030f1001c40c2d00450741165170340c8400c846201e00207049084181118800c00a140c00c96821002d4583d240c410803c0c00018000040c0c00c41d40940c031a4400b4100d41034009071200c4402022000650080710103e01407030510b0006a1220402c0c5039440c00c1d141c28402c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 908126025 1250 908124775 908124787
    0x90a1a0105071b0e15010807081501020c03060c030106020f030a1403060d02130f0606030e031e13030602040f09020702090109180f080304020f0a030f020105070f060e0a02010f14 78
    0x445158010580503980b40780340144601ca006064414a002030515001c00c1640e1714019050400365810040014103014000c0c0070090400d5200c100c460b4401244542a448019000300403803402511804003a003502ca110181300030007601c1c00c05103040340c0c0168211540307503100000f207645038051112007130082a501002140c3d01901c1c0340142d80c1c45440030349030300c0401800341c0004240200c0b80c000980e01035aa09000156204075000303105c054542801c0074821203d031300401c565a4460303a81d408101d0806a2a105090080c280c04c0b40d805c03d4000c4c42c0310500726180d05011000390f005114030a1222070311400080c1c125242e0003524003a50b0000c0c0a8400e9070321b44507a50340588801c0e03310a9140301040302820001d444920820b2a250144820903100d20303091042c45822500500d81e01c0c840d0886103410000551040700c1d00444560a290040e00c80071145080015941482401069641840090004170500241941065000b60b03190941079410354000d4815002d0414003501000b010480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 908127275 1250 908126025 908126027
    0x31f050a06050720060711010806240a0507080d0606030b150a2a060e070f030f112b1a07050f090d02040c02031c020a0e011101240302090a1a01 63
    0xb06442c807000c40c134041c190b0203030f000060b40c40e51164008544549030200103100d99640160080c0d400b44003a82c9a00c810001c030a40d801c1c04550050f50700b01c83d100009540c031410340c4207100f070f2105642c0c00380d02640c440041002000c040c280780c1c050745001904d00a02d0403d18907008100b410840e20070140c15141612640c8111924a1400b901d40e8880e459005240d0851400080840c103081c000c0d000090b00160010407103003044041c1d44454100088014140301050184010900141c3d004450607051105200807448070300400141e15040810a440782041c2000e4551156125100e070005858141c0202e410f0883d070385080d1040000a001805680240d100f0700000f40300104005000c1001d02c0305950000307060702c0c0e0400c44100180c201107030380010641c10314156041000c0b849415401c00c070321b02100a0a0001180c150307030410280501c4601400401e40c4580d144a155042c0507140740711807400b140e030700300c000c0c40101c0c090f45004000400652451207800300e60040794240305d1091a0641c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 908128525 1250 908127275 908127293
    0xb0109060f120905160918080a0f140d051509040b0a0b0109080f07170c13020a0302070b0406061d060a0b130b030f06180402010207030b1803031f050a060507 69
    0x600619003d0743c0da410880410001c101c0c18a0904d42910300f49081d0f07040041501c180d03500348a4407002013581c004010009422801581c80c1404903140894640e0000c01e000c65140140108034070342080c00145400381040c0c160440e0f407160034840021482d20300004280100740e1001c0760040c020000d20310220310705800c1c940100203840414501079125a40b28818142041c014903040c010036404800204060009080481d1440900e00f01400c20340340410041342e21a0f44c103120101c96950b0004500341034600980c15501082e400a12001f02445d080ca41080101540d009170203c06905000071141d4840c0ea00307006115400240212040d00d01d0130502e01c0707954000c9011082400c810f032902081d480c0801000e5481660b580b030711811a8289401484000340340001142e99054440c1d0070800980d0300042d41908990b441070361410740c2d5540101d42c51a02c11440ba0f090440d0100006002c0c0c000761108480381c001a1125030071015990743c4081200c1c550b06803082a0218074213001c080302182d1001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 908129775 1250 908128525 908128547
    0xc0306120209181005160e1c0b0c07051006140a08070e130f0b1f060f0c170a0305040c05090f0a020f210709140f040207050c1507060b0109060f 63
    0xc3c04460380e030805041441d09490b0102e07502c584070f02004068100c01940301d101a00140340940c0c48180b828100500c40c03d0b10040f10001605d41502040881c0d0106244012a0f600f02d0300903056444078440c46110801425040c8140d00c0f20041001a9102c0c901e0005140303000c41d0f4403a0000c14500f4940b944500c000c0030010048003111961411001c0415000d8030308021451090700c0b03a60305483c0041d410301c000103114038104000d00e829034042c044640c004044000c00303031450401200030034181c5000035100d4087c1c82403500d8000007040442c50381c4e400d038000f40e004034442c054000780f45840b80c05010060320304440500301400d84001040e030106140d0f004142c0303918408000d600d00040000702e074030110614001c19030219690800c102c0001c2d88580d00d60050403c1040b8140f804c1e81c40c00000300345048843c1072071b2140381e001403540d081000810001ca103036003005d0014900e00d801c8442046d41600654416900507081c443c4d40407480d03100f80801c006945050b00e906c5580c0302001d03402c07544c083d003070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 908131025 1250 908129775 908129821
    0x1b0c07050d0f0c0f03031106041a1005120c03071e03020d110405191416140d0c0306030512040b0a030203040f060608010c110c09070311040e01090c0306120209 70
    0x1103602408540c445804101900403169001d04c0c00e840c5280081040034030006c0181c064001c1000d120006440000310310340720440d00d61440682e243c1c00d054001070341031548480d0b070018041d02e00c0d036000d40002c200c240017424102c0c181e4668640c1c1e400380710b018554921550310526010f010a00045c5010f0b018460036a016001007031500000e1b1012804595055800c84000106844981c040c14841d0149404409206010017503d04154000d161a1a6005900e4041c080c0d040f8200c1d04051400c410344915211000c018440a1800307400503000b002640001d80e2540910501d0448103107403003080f00e0031503016a14452070465596002c80080d00702800440b25852070b80e81c4000403030307154041c1401030b00c150400007440c000c000d40c02030003d01c0c2034400300b500364104400305011641c60f40c001d940d00040604011800307545603c0c10100910540d000840b000076070718000300d4111113a40c80141d00d0b0550743c5042240075142d0212017482c1e20341c040029800300c90b80c03000613000f180ca504808101e0401c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 908132275 1250 908131025 908131043
    0xe06030d050c12120402040c030e0606150c0616080c03190c03140907061d0f0f0a080a11030106060e0d030e011101020403152003040f02150a02061b0c07050d 69
    0x201442c038410f65001c110314090107410070003800207615080c400c001e0b106409041c104100e00000164503240c8034020310491240d1101c10307451450000e2078044441006104058410901e42140c14015199082c0f11020000e20a040019510500f95080341d01500e41e58a20300d00325007200c043e4034060b00c452420b0300300300340d19080380d546010000510342d40901900d0016244541c2801c034000c2078607101015800550410700c001c40303da0b441d1020303603041001c0140c40c0c0700240c0b048080805c1c200800c95103c641e591045055402c203101d910040d00300586000c5000740200b9580c2c9404680c250403c0001c641c1c003c04802d041d000082c0180d650030071902060400c071031405484071106003240c00a41c025a060146011a031040c10890700c00d41e50341304401c214500d281a0103d01c664080d0000800090014280b4101c80c020766803003048141c00d4a8108458580d21910020025161724040c2c9070300d9080090410804040c48520080c3c0f103440fa207030b030010000c81e40b90504004503c0002d03107059071032032a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 908133525 1250 908132275 908132293
    0xf031a090613050c091611011109040b190f240f05031003050601060c020f04051017150c09011725030b0a1215060f121a0703150e06030d050c 62
    0x44006440e0300c160380306c0d010a44000485540035110715504041e05019900d000520002d141d560000d4079101401a9800512031410030041860410500324081240c012210009444840c41e00c6510940700c8a0b100c5800114a0041c0d8401c0a50400005004a4020f11191700d02511510141d41d00c03ca1a034040010b16580b43c0310310b81004000e800842c005900c9808410550418924ae40500c0034141e904000f1384c60050455403005026008446903d46205055401d402c801c00150081d0582d44803803881d2402e02d00c0848841e07a11a0600c240840c281e58903220808018000f168030800c13034401c201000f4042c0c01c20454203506409480c900341503840d2002016030303c841908070301410f002c01c1d000403e01480d082c0b1640010030745008480184c2003813030074018004d0b40d103141411108401680c141c1c403803140c68150820b0409001c07001854401c0403c002ca026855007180c4c1c4c6c1d080341d00d890148450380321680b0141503d0304071520b940645c0a031002200e140c1c0302d10700525461040c0310980700d10300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 908134775 1250 908133525 908133529
    0x7140a0c03060c111506040c0203040902030a09020a120f0303050705131503140106140a05071a01140406050918011509021e25020a0f0f031a090613050c 67
    0x440c19400079505a9920003060104941084400e94001038201c010044000010700c802c400020003048940640c0e101c0d0082d403149402001030b14082c29a0071429501ca02d0580210401041071900c01c0e817262003811000148000790001e041c2030310790030170891507800c0d03a6500c05601420000e4144800c000c410080e0105000c2c41311014000f400d000b040000f40c0d2413500b80c000302034070742e0740c640420344048010040061a030030242c1003440504660440d41c031402c00d1102a40d103805145d0000d00442d0055075400c1032a00ca03609081d040e10900f01c18246203134242420b00c41103a04600400390029407200205011002d21919480484482400801c844a820000302c0c2540d031154491440c15401003841e00040c1a1108030300300d50b40980031843c0c102048021100780c800c52100c8115240c15101d5524011354034bc1e01e002d040540318071000c1d940329981e100c961820131426403105039040e0100a42042c40301d8034802d600380c000c1c60b103600107143e10b89400c10309109200c00c05d041180e040c0b07d0048800c5440e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 908136025 1250 908134775 908134793
    0x126100b0d0501080f0c101107170d0f050901020a08130b070818010e09010b1b010501060f030f0204050d20041401060e030f06010b1c0603060b0112020c0307140a 71
    0x1da80e4550010846500d8208414a00701c01a5141c6403290840c241450558503031541410030841c2c6072a0501141720400300c40d900342941600524441c12440d0300900306220006880c801d02403150ba582c5200f4203200c0c1c0d08580600818039140c0c0160800602e6a020038100005031031440384011b0303c0c51016941d8428102036621207041194036800110303410014104041c1121451002800d10091000090303000400d8040140645071704090007203800006080b8099448191034074000003013040d540c550f0006494400240071800000f0304220050484c0c070a10b000740c90440740060414404044165102601401030822050120700d0700c0110369004d80c0c45000b40704252900c1c1d00c1249095040000090900c8221050107000b0760001d00b210014003400180a13045983d2550305984418101502c80c00c0f03001c22030661808642130a0f00441804200d501c41c14003004c1c240c03282482c4062140d600360503405001c1801034541c03c00d006603030100b100021100e0740080e2000650710310024550300c103024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 908137275 1250 908136025 908136037
    0x3050705012703030f080a05010303050319150807230a03060b03030705070603051006020d02060a050901060b0d06091803020d050a0e0603090f0d11071e0503060915060126100b 77
    0xd0745d1010f0a00250b4128440c1070700050280e409021540c19038401901611000d8481c0a80408041d10b001202d06580c0c8010406ca1642c00d081030104e40d5141d500b030340d5441e14003498942c08001440011b5000c1801c580190342230307010709030041a500d940ca4410003005080540380e01400b08111a0000400511804015100341e84002421303003480301c003d041280703440c0c00140a55010400e4040c2094000404990000d64400c0108855880036a41070140c40c880e8072081440201140d84039a0320380355040348043e035174030f07807010403d949500b0700b820305041015070b0160150300032081d030700111031050303000b400000315a050034250b648404012071030640c0122000b1032030f81c1000e0040c1008100500c8010741000040c90704409600c5d801110540b43d60052080c1245404600712416004845290400c018000101038414034a4126105500c0c0c4429001c2c50080c050040d0008985600668058100c0c102645070807080580c0c1004074007002c21301074805542d83c0600280080c4000c5c550008041c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 908138525 1250 908137275 908137277
    0x10306180c021b010c0b0c0c1014090c0d1b0b030c0d0b040b131a040504120f08100303030b2803050601540e0c04060305070501270303 59
    0x68440c1e910400905000800001240300c00403014042d00c0d6030791000c01d940c00e503900042201c016440e18442c501d80c5210301305030308615004030320240c114428a9880207030b0001040d091034040d60390b40001141c585400d4240244d00208070320001c4003260440e60b500e1200c0000d11070706040161550111003994100700c803220701e0300c88000781080c88018280620b8420032800c0c0c0d4240b1014002e0000200d50003800080d03140d820340c0e154815800021203c401c2d504410014008121320304090602d060b46040301c2c50011f01040e041c010301c044070761181c0300c3c85205900030300d020b0860a04664048015160f40380982d584070034030948c144c40803200400120a0b0500100000820038a1485d01070704011050b0300094500f00c40080000c003148252410b80d032400c071100c4c1300010302d082c40c40d03036610700001ca001400e0400100b16446840d02d0300540c410741c2201c441c1401c89135100e005030304001c2900c0d0a80401000380d08021410402540500140801e640d050504a804442d51001c01400d0360450341c401e070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 908139775 1250 908138525 908138531
    0x30e150c0d030501180b010e0603070806190602060705070f2a05090402180601020717100b060c1b03070305120d050601090303020a111c0b060102060a06030b0408070201030618 77
    0x1010185040141801c18101414140000d624118440c0002c0310a4045400d143d6200d506000580e031141108510041009140c19164117010308004c0c42000f084400a019003100740c01074007a410f881e141101100c086500420145d0398551044400780c00020b8221644040c07041e00c44005692450602c1c6100306400350b403151585180c0c01410091801c0d40715500524043d0140000b60b2a040c1c2e2040c04242009100001500c031080106e150040540c4084035150020000c50240f01000c03036104403040780203505202d030400c2ea1040040074807640401c20398540c81100741c2d42c01079180e00c10000082800405849131a40d59803516030509039104216501281f001030b04d100b00c0001342c0304158005900b80307012485030342160ba0103591041ca540c8017404d8050341c002c81c0a4540e550081c41e11403400800d888040c02002454118121070003621140d02501510000400000e010f2080380200d03600400c2485654482c0d440300c0d00c642c0c0c0407400a80c100341d1524008101894484000c040900d1490000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 908141025 1250 908139775 908139787
    0x3180212010e060601030612140304080f0c0103231302060d0207060b0a0f1a280c051e031209010e0604031706060301060f0807030b090108100509030a0516030e15 71
    0x80c3c00c01100600050516143c0304050000304844080d1703400f6103a121681851000e641485e107851809035910505182c030510402201a95020900d880403041c2a2403d2025051400001c404030303590840c0040c0400700c48000889078020620042c0132039001030b180c03034a841c40380b0b21604140e902105003901d0454413407d0601d0f10741001840780b00101030056a054110f800e0205d010b03812a00300104550441c400300e4080141324a15030540c6401c4098080c201c1c4503015076801070079100c8140b4066400740290390300c440254045070260030031134941c071016500e45522100800b01d5000c1c09020030580390741e966070868068500f04001e50003207000c1e454403030348031608084d500c981060040400303010712410701c01044841c1d000301e0001048100d40c1000000ca9071119401c50043c1245004954040c80c510300001e00104003007082140b4083d0b0707880c02d11544e035a42005c150b90380314030815440010020440003660450340c3e610440356034401c2c03074269681d01c5a6000116000c40013441e0140d10f16001403a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 908142275 1250 908141025 908141051
    0x2190302030f03040e0412091e1e0812070f1529090703090809040c27030f0204021315030b0111060f0402090c0706140a0e150105010318021201 63
    0x18650b4100201c8000c502d05414005549078204000d00b000340b0540745c41d503010b403c3c83d0080050304007801c0c001c101100c04595078074419944401601c211407501c00c052545514000c0b0b40e07224a070550741c0d214001c02d07203480c2042c1d030100076907c0694191042d20300766500070009115100480c4200341000c201140010148002e028250081d40c0048959410791445d0403054071082d0911341d11050606002440c200c02c0e08010800d4841d40000e01c2e40706250030354114200307400022030343c102d42c01002d80401305201c0a03140c03c000410703404003900300c0c041c1c048803400614003500281a4200010b01c440541540c1d140d401d0f003800007408010700400d850300828003031940c0c460302484c8020346420040841d41040284e0700c025031030180001e03004407021400600f080c0c0c20f83c021aaa6260f200d00d0801000d052307107030303210004102034904014003410094400c01100300010b0484036401c4401d2004c09a07482c010040d402040d01d000c0079460145071103100c1e005651074000d8100d10b01c0220f4000309041c00c2c2140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 908143525 1250 908142275 908142283
    0xb0c0c0d060c17100519120f030905060708030f100807150e012109031421010603110d051504050108060a0b1002030403020607080910051b0d1d0d0219030203 69
    0x207500c100c3c042d401c80c10040450050082c200440d44103071510003207004001c030111040c440ba0b8001003440c0342c001c8946d0003080b448400350403026000b951003442094903039003085201d20a01c1c2000e05001c1050000c80d401c3d003d0001c0242d04031510300a000350556071a05010309101c4540c3c003c1c620545142a58040031b508280340d07008000c000d10b040e4000e071002e00a980035501801c001420349a64411004003054000c034840c0c41405400c00b40303152281c0e00d582c181c503c400e00000500903204021030001954901a005102202e694008014100f5030103e420b5001084010403800c0d43c1054003c2c58403450310385120f110301910007180541001d01e00744c1386583c01d8665045040d8000c0303d0220460b8069603000c020fa070182ea0341143e1321556100a802c198400c0d00421040c25840b0300744101c5003803400e4010001349400032104240303c074251041c0e074000b1b45402041840801040300e800c0c1030306000b200540054501003009003500c400c00e1054011802c11410303085600c00040c0c042c64240150b2400b00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 908144775 1250 908143525 908143547
    0x506180106090f050d0f0803040203011e020418050c031b12250c02012c090a050414010b030d0e21030301061704020d020105030c0c0a060f061e0b0c0c0d060c 69
    0x601d0050281790140d540750440c00c2a607101414050011010400f1135400390410f0080c031542c10300390707080b0100912003180207600a115443d15007000c031440c03030010616406a075103d0b1759940c000c1c0341107945002c01c5451030303c5010310700280d0280130886442d8699408041a000745403031300d00c01e464a541900324000c489d031042400e1050110500003000103070f0740300c0380c03007490307010820340750b02c00c40e01102e40c3c48420448041203076034007800f45410030050502e00da00246c495405040b0031040c40310300501c55800ca0382200072071a0141c001240c1182a10300407d401b1990880182100c151140440405102c502c0d0810b018041608004010003107158400003441c91400c0040c2d80e00070a0515500140e040540c03003000a0510001000258405001d1400c1da501c4a0701e50003502ca0711485d901d040710007044202e6a046403545021404104a548452928910501d44021381c04a5041c1000c1c1c4025030030202203004c852080e0080b140c0c0684030082c85113502d17803140801044082c0c0d00c44010740000811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 908146025 1250 908144775 908144779
    0xa11032a0f0d030b01090302130f0c08010b03040803060f12070303090b12220f030c0303060e160c0602221514070f031403070507051b130506180106090f05 68
    0x12032800c0030480855030084110302c0707042c005008000c80d80142c500e0521548060350018250000051503a040d81000906070040c074810080105010f1064501000038010304001c02c40500008000601d032600641e00018020000c00744000e404000441c82052100c3e5034103260007041c010000c040c3c0140d1058042c004801c07009090017000d40c501082c00d00002d140402541403c11546800c1143c044011070b0160010001001d61040703040152115110140c114000f0345422070005d40742e04000c00c07160148403c5003001c030b006000580d00300d408803449601590800d0382009440c03540117007030b192078290b00341c18080c1030905031605130100780780750301e80700100305010140d450b038010356054408503007285074041074400d0b45103c641403c45c1c0144c02a0f80f80344020500205011613280c01902410040380700b04100e589903c0c6c4c0c00d902c0190026400c0d04c41c1e412541101001103040519004107900000151204103c40360740f14036200101c3d000c0e4020008503e034450144802c0e8130320302140d0041c00301 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 908147275 1250 908146025 908146033
    0x11040b0d0605150a0608160e1005090f0418110a050d080703090b0d06051f08010923040f03020708010c02060a020a1b0c050118050f04020a11032a 64
    0x285501048480d00c0c654401014240c0d1a00065a4004103c400c954045006801070408988506014102c2c450540f422a8090b508903038002d8107510443e144208114003410300003c00c12125000d81d1a0380252506c0e5910a103200000c45803500c5500c43c2c8564080c01000307101641d000f80c00c00344030340303d0080c0c421400b070801c004050060380c46080301d100c41142c0c043d11641c2e6402690400312001850752700014115580014001221012a00083d0a81e041140c0c41c8903043c00c1098101810703404840010003017104034004001210700e56002400440042004083c540a007000c1401c2d048003c40d004c82c0c075030402c001d01806156040040c0d80150000b90005c2005000842001e0345d81c0304d005045140141d000250600600e100b112808444002980285840301052030f02c2d026802d02800754078000b400050306011612503030721480c011202d01071310001040554106000c007070340c4006640018072a03403506801b0383d51000c0000304228107030a407a02c10b0604141c1d03425000f140f00e160f50000290b01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 908148525 1250 908147275 908147291
    0x110d11041e0e0106050f070b0f010f0506071a13021c03030b10050f0f04090905070821030406020c1513060c030b0306070e0a080d020a0c120302030708130b070f1104 72
    0x707a03422883c1034855034105503440711014949604c43d4403070910020031465000d800d12000c0c041c0070394000e040c1c4015103104d00c2003944802c02e01c400360081e03003405450b100c62003c00c4801c1240c1c0f2f54403c3c0c1c01803150905906000d0039500462032010b401d40d10803d11601d00c11071082816458407074500003080844110301e03507200400000386140202c1403490701c28080054102d986000728001c03a001020b0400d0140004011814440c1d15030610f4420303045680604000d60a0450488a00c1c030b902501c91519141181c0308c0b070703c805000390802c1d004054184078110500440e585100c0c0007510807420000340300c000301d0b240d10b8902c1c00d60303940c883c0315814503040c440301c0340b400c0d5008142581c6c03013031141ca4454050061080028809101d03a44001070a00801c40f400c060258007080800703110b0300804001d0720080d900c22201202c41c0344da800c0900140c01c144111000985d401303004102148840000011381900c0c0d0550151a9201c11400c496500f03149813080100140281e012460340d204590400c682a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 908149775 1250 908148525 908148539
    0x180f0106021f0222060c1403040501090e0907082e0516230409020a17091903180f15320d1d0712030f03110d11041e 51
    0x98201c0340b41c0d03410250049410055816801c849035241152442c403e41d009a444001034001c0080d09025681d141e50402d4040350180d00108a9044500c180e4039a048640340002d20380c0040409800c800540c000c0100006002404010038002044040c0c107507000062100202c184401110266040e0241484c00308034070340106c2000b000a01da541e0174040071000807820740e1004102031408440051070003103400700f40c44040da030207071020300d6541e00c1d4580c01448880e46034250303038401c4441e11540e52007110b01c525201e024401c1030883c50f201703043c4210812482e0f070744c0f4110400b02d504802103280e0b04940401c00442c29490784141b00d074050401100e000c803030071030541d08070488030000300080d10212090f840002440040751446810342d1410025424000848501120700d8036070350b00325108428005c07859104050341000000c0c2e05131a0700d00300601200068016040086030700606010a10031004460140c0c062000c1211140c803081d5030f0395040c005001d101e40740c4107180742c1a40f041403400380100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 908151025 1250 908149775 908149813
    0x20a0207050a0f03050c0126010b04140901051c05070e0403020607080a15300b0405060705030906150109080d0201050a150303090e09072102010e0402090f0f0a05180f010602 76
    0x500001c1c80e1040016030301d00900421031048d1011170031000403510000a4040302003004d0300c00c0c2c600ba1140d00108501b000300b0001c52500a0155650201c41300c151804806d1800075081e8410f407140302610351040e6515030000300d005003110190f000d80c010100300041264401d074043e5020b0400042040070391324848101c4000c49090140310500b4107441c0c56000036480e02e00e0003d0340d120480320450351044135450b00c4061040e003581c0468181c41b50710081201180900c0650b031082001c0001032072550b9031011006225030446035964180410380d0030100d4009020302c2001484440b40c1c00120309414151410001c849a0320003200220790340c09000d00000f03601c9090202140c08940c03041c21681c4a0904950030123810381d1084003004086112109006148140841154005d895003400c802e0120b0074002a40b19007005150300050300e50204155183ca03034070040f840040038080700c106584680102d007000e9210807176003040d8014001084840301d040e524403409000c103880030300098105980f01883c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 908152275 1250 908151025 908151043
    0x218010807030f02040602010b1801060f05030c0f030106050c0606310b03070312030b100c06020318010e030d112b200304051b030705100c0501020a0207050a0f0305 72
    0x40065500100e04402d10036001049511007401e411545c80c0d40d1200c01a000f0030708503480f18001d00c0300080d02124449a003040d40c0c100d403450344136400907032a1110100c8150380018600041c9a030b06000c1d0002c41d1403800007a5000c1c00c1140c0303d06980c0e07001080e0691821000070710440c4500c094070001410854100d0100442a40740381082190040100d150005406441580c40d01441011400024071401c1080c03a1172402858401300001310040c018401d0011440003100d0114060603030f801c00040720f0341d00075648800d11440002890801c0b00c5100d0035125400c040e07000319407001c41e041105030114441c02c100c0b60302900c080c83c507042c100910180183c0d1030f000c1824034059003840785003208013140c000b402e013018003550550b05aa24105040d4184d00142c6040d00c45100c1c488082480c000b00c0440404021801001070508600d42002c0001101e00d1060b410104600c00203c0c4000803800d0001c0c2400c0e0070143c000e000094207113007e000c0310716001c3e800240448102c1c40104082103000c580002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 908153525 1250 908152275 908152277
    0x403030c020112200708073002060c0a201203100503030301081905120a20011a091b030907080c1017040201091d070201180c120609050d0e040f021801 66
    0x1e100c4095050241e49030048030000b5040d8941c3c614a07030603251403248256031000c00809401c0440540c92012132b070300d485c1100d4840c1d061004020001466014103140182044c1101400301c020f4a0002c02078140b9000d1400b44403100408030501002c000380028203400f600c801e40c0110304661620b5081c1d41c2d98040c0c1180709181048031b11501042c41003e10103141c6900e403502413143c0c0c81d103510b10014414201c900c002401c500107031218140d50203060080000405501500721502080b40d4104154610041d010003d02d210395101d1405028145003d5032081c0405000780a805150000440c2803030300000d0002c1c49a06000b41d001401d42d0844030900c141e0b5050648c880450340c903880162820100340d00000c0100c030b141d21201c403003c5a01203000303201e18040da000340001d880c0d442c1454040080c00c100107000044141061191075410010034181c2030280101145090343d6444050505c06040104c0340003403601c141031002c42c00d060090104803900c1c00c0c030440c600b60402401d603e41c0c1040e802403034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 908154775 1250 908153525 908153527
    0x90c0602030f0d0b12060403050c150c03042a030f06050a090c09050709030f080c01150f060e240d0c050913050402012a0c081c050a05040b0403030c02011220 69
    0x81c1070b501d458985c180c00b07003c0324040f662a41003074103015107150002001781c043d0b84940690f41405480440680780200711405201e415900e503039540c7c0c4140c1c0d4920445121742d00d205090314102c1900e04806000550203400c9c0f101c100e60309400c1400c02d4030300c020507144405040654000001d50f041030201e0440c0c40e51000050961039205003183c400711160b00162217084030034551014800064000d0682c0d1865500800006515a01c1d03845008242d1041003a00c450780501000030a010308500e6144e10001000c02a00907880c03c06410916203444d0b00701448038004c01c440c0c410b0803003480b6000b412901402c0850900c001d000c0000c04100b5040802d852035a116000b01e001c42e4040c440031980c66191103d02c00881e4100301c0a49088907050405a0318014200070004803104080b501444029207125404000d00500c0c500380ca103a0702c50b0700ca01041000810000070302000d00f00107800554441d564580400c9000c1c00010030482c0d880003494030700c5251005602103030801c03059807584a0b80100040e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 908156025 1250 908154775 908154791
    0x140f03070c0f02060d02030f10080d0c06060807260c0a172e060e040209040b1b0c0c040c110c090c040305300406090e040c0b0d090c0602030f0d 63
    0x420b44003001908002c0d088040407921414180b0b298001c0d6210700c2d034107030342d00941c1d6440307200084071035807140324610f41c58021605070240d4274800c0c210b50108900440c00455556511904540b0b09100d54ac014903240e01c116641c032031004204c002c1001c200d03513140001c180c0f0300081c00000742d520700c0610403181e001040507080081c28030203220803101c40c0c10344615001401d56605a11000600742c030103400502c2d01d1321401080b0f00c481d121030280125009803000d0345035034031659a8402000007030b01003400e05004290f540c0382c100c2c013031004100701040c00c009449588160010302c410740c0c0f0345004600034401c1002000070320040001d511408160100c1e00f069064a660310740180d81d110b19000544140140400c82c0c502820303007030400144260b50401c6080c180000c00180074140602c0c056100020103030b44040129500c4040a550454020381022030001d6554440301940e6110603000340120b51141458000d000c1e000d04c1100003040f660000e18a0070302c0b01307404c0e6a2240318440038082c45541d40c03511 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 908157275 1250 908156025 908156033
    0x30e100e03010203090d12091104050901090f050307030f09230f0301060e040c17030d1a060a08270d05030a0e0708100e03040b12060f0a060f140f03070c 67
    0x400d000401a00844d13480c2000141541c40e81760740c0ea4480c020441d80029440343c44042d101e0700c44299004900c05042c6c012141c00c21002c0c000250020916640344c0d040e0034040781003074104041051094004513510807461601030f100c1c0a04100201c280214840104915400446900320071415141004640c803807000001d52111003c103a00c50b015840c0c10f201140c1400445a40d41c050b50045004071042d9682d00e11801d03280c0000b242c0792656800600c00800c01b003145800c0407181c1018005408608842807000c02c40700c0c0c10100c0030a0000d20b4502c00d000103080c0c5284440d00030b0f211004215450911004810b0ba14944034188c0070400c000000020000d050590203c200010000181c54806589003c01f564405c90900300340b0759149456000301d08080e0000441d021a610303442818105030126044125222008003207507001080b50390074104558405030f042020302202d4680d50841c40c00d070329005001017440240032014203801c2204c4070101412500350f0b0b45c00501403a0070342c0c1001c01890 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 908158525 1250 908157275 908157287
    0x7060b15040b0a0905190524030a0516020a02030d110c0307080c130e120a0e120d031404020f0d020a03060612021302120c0306060909090c030118030e10 67
    0x100d0000800c5000c607000c01c030b0022900003002500031079940d1202507070f05c500800040526004106004030282c080401c21810004010420a078130369458020400aa450004456008541d0200410354620070028154195a2a02a150035030310080a40034420350219689040c026014428000c4048001c450780303070104041803e80c0405400e40f000250f41c0c180c0190b8403001102014421001d0f0f001c001100d520600c03902c0110500b12004103040b109251035100c2aa000c10005001c011031000d4010b00c03611610000404180410020661a52490f00040844441282400c07029190300c1c00c0c040075941d508404101c5000c11100c90720000c055200040b02070341e259200420207404e02c4030000f203460100e40350300c0149000343d44049006454a101100300c0c400c3c072002e20549a03200c0c0103ea66030704007801440d031021000d0071281c94000c03c003000a10031402150304140d603500041c01c50096007420b000e18651000140203080619a0395034014258441da8080e49006915400d400300035a40700e64 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 908159775 1250 908158525 908158549
    0xe150a05151e150a050703050901030908130602011107020a03080309011d150106050703021e1e1b0616140109021c02040e06070c03030218090c1b07060507060b 70
    0x70002282c07101141020141c030640410150302c00c8a06100b002400c45296080320307071011141e6105407400c0141c3e80c051354580c004880c40780c10903942e48580b60001704d1100040240301c0c41a144070080318900b08000782520880d88203424412805d01c1090300603228181c0c1001600d600144481e2030360380e10040103005100304030240540f01100c111a50001401240c181c1403c09544039010b026030320b4010684e4140702c0c400d0003c005a02c05010326807640402000b00f040b86000c00261240c10f040c041910b9010301d00076072046901e40002100c101c181015005a00444206840745030802c40100078200040c036800d90003078404c024400700038041100030750100d10590f5008200040e10520440000b400342c441c0ba80880c000d40ca0148044030038180090214459502507032082c42c00b40c00c941d02180690083e500328011051140c40e0310949030b4035100340901c100d00c88a0a00d4403607400c50445c49200f806000e1159040d0011101030010950001c00c48011542200c0007141805a03080440d407005021 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 908161025 1250 908159775 908159779
    0x706020a17091518040b06030105041805010e0c01020105010f03120f0c0c0f150809060114010302131710020412030e0f03010905010509160e0610091a07060e150a0515 73
    0x502c0c030504219110409025071084c4000840e040406010030b00003102e1818a44aa2080c0700b80010080c17403034142c1204a0300e014a5982c0a00022103984490950b0b004007080092034001c100030b880705590900c03030b80340100309103090018000d24544444c1126941402d03003404008083e9803480301140036940030118980c0c428594900240e64806100c1085114020320614980000000385007510440c00280540c60759005865039920b84040b8411134500891a54149602842140380e000d05000d40d81000303002001025202d0180f4488081c08c0005081c40d1003032607403041c070060000132203900c0d0303007144c40d0b42c1424051041d8a0800018030004028080c5641c15800e04002270100441900114060400d04084803140a40c1404000040e0854014032411341da000000426a2a1038500d0346024941803c00e05512034686966a06003081c4651442e01c40c03000081c400c04110851003450002080d0002a0440f5650102c0d1b030a0021000b81401001d0f585410108044450071120880030440c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 908162275 1250 908161025 908161039
    0xd020c162d03350703080a1505010503090c0901030609022e050d021b010b0f18060d020105093d02100902040b060a170726130206031905090706020a1709 67
    0x607036201e10b410f642c040001200050080c1d4041070f0b4602d442d01030b8180c8403404451004030303079043c20011510750300014103000c403500c10740810820507103030086240d010b10300460000c80c0c0765200e401402034500608100d81103001051906d925951124595004540e0709803405550350300c0c014640c04040e0080e820070080700b400a010007980c00740154022070381c4c404199003d51a03a1001e90401100c12070000880d40410708580028400f8034081d00120703410381c8141802400d1503010f02c0442c41d081d03581150701c050f10440a403031825207070b03d204400080360303680d404030403489101005c025112488201105101a11180213030219640c9401c049245100038029944a018a0b500102607070000b0141244020041c03000c42c40151003842d01c8210000c20310b41c50781101c614110500711841c0010000e040004e8a442008010b9842000542c016503548041000c04d0001d0141e002c00c84002805402c11503010b90010040700d9004103a070514103400c081807035040440d0040c00c800700d21400791000d6001c12 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 908163525 1250 908162275 908162363
    0x3020c040509010c0f05130315091202070314030304111009240318020d02060f0c0106560c0d030e060c0313080d020c162d03 55
    0xe015845502080211741d80e40c51465103504050300d4900c00d00d40340710040c81540300140b01140b01092400d40c2d03264003a07800607984105841e00704041140804100c0141c111003020010f0207039004454001c5207102020b10700e1824541d9501d220709000d1203410f07000e40c0b984c1d002020040c0c0200c441c000140030503405400120b54100e14540c008140c680683c010a140031001c0b01503203001c4a14404c02036024048905200e41d540800c8900c1d000031301041c0cae41c0d80303007042041c0c0948403e0003002d00901c5400c001500c0c2c11215038100403c0440041c01c00070b84c080c00800922808000d1240c060f0000505000d40c2d402444030760403034614850b841c41041c0d940b00d40014407600a505920040701d1400d600c0c26203115485144000c0a90301c030580b0202c0707519800e440c1c00c2000c26000001008048030806d001840d1400112826003400945c1100c09448240007100b0001002c10810a01790b064900011a0224103400161030480540c1c0c00003901050070b01c0c3c00b03a803083c2d01500c08030000130130051380409200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 908164775 1250 908163525 908163541
    0x903030f0403023427022212031115010b030a15030809040e0708030702100521041203060303080a021605070807031709010507020d05031c0f061710050403020c0405 72
    0x1604052030030004c64001c020001e20345401c0020000014002c2860ba000c00c034803206000040c4d0440300e481c1c50750071100440d10f000703d041d1600f140001c2c00c01e0342428203400d00500b0003070003001e105030008540d40c0000b0b14003641d450100095605441c000340c5583e4581d00c0300c400035401811750541507110082d0862010081c0403010740601103517582100d06002405a042d0074030f03100c1c07145100d1600180c4c0284181070043c54504601e024020081c60103600300003580c44d400c03400e03c00b41d503055141c281e001030a10041c0b00c4644080c244030408c40c1401d00810b80340d0b5070004d0000c100203120741485540880c074242060b50750307446008a5a040340403660411b45510069884a034940301c11a600b501c001a0011101050790948040080586885041044980a00c441c0c458016021201da010402520321410804042e08081c190f86039400264009441140812140c0390782192000e0440e4030241d00652100040c20304c0807110011012440752030317a00d4140d20f4405040c00c926801410142001000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 908166025 1250 908164775 908164843
    0x3030c120911040b0a150804050313060f0e03030313080903070b030f16090308030c131503060810051003020d03020c03030304030e041d250f03030509090a050903030f040302 76
    0xb4480c1240c1c20400c0400800800074200f80c3c03440307810604080c000403e910030740650700c007a600c01c1c001c034185ca10b0000070780c041902900890f000300005c5030001141031138083c2c0c01041540d5180099004500c1c40c10455008006008401e000a2040d1070006901d100f0386c0b4184241c1d401840140a52501c034148541d04040000086410082c0840001c40081a561080c1c0d141c40c201d80d00100140d15645803240c00c104158001000300704202441c0c04006414407500d051486205850350300003400300d0905004034103101020f0b4450645c981488248011860000740c81d00843e40e0456805110010354036040c1e0400104118183d818007020040005054001c1d400302c0c00040100d5080104140074049401283c0c501c900010940d44604509581c0c142180d00c15500e0010010702900c100341c1c0c903400c1007082c0b0032540044000403030124420740581005510300c1d4200801315001c1c4003074500b5a00066990000800d40c0c0c5184883c0000b041c1494000d1180046404264042504540e1603402d0384030750b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 908167275 1250 908166025 908166053
    0x20c06040b0417120103020d0501020c120406090806010f14190f03110402120703023a0e0a1502090f04020c060105010207150233010305010b0306101203030c1209 71
    0x1040d0203c1044030100d0b10040c1190340320b80c1100c502008a900790340a02104041c400d00c01ca070b1641d070070080000c035003d040041050000c02c03001c001d070307443e42010703002171140c6420350041c0e2301d99001000503c14142035030101c20a84a41d82c49040c3d42d62680c0c4005140344400300100d642c0340d500703400701040242c0840031220603a0f024100001d0000ca180007408120710a015003450303071070202c0c0042103883e032294000708035544108800c0c096000e010395a512170003035400640346820703141110400c180c0b4041d01407540b4904c018800740c5082d20003620b521000191001e00d46001d50741c002011000c40c0e440100f02c0504403806402107486924039800c2c5030352441c00b8018a805407181030400581ea0b02c00255801461906501900d07081101c1035402018001034130600b51031038200c0c440c24003600f0100803014020360080700082100c131640c000f41030800d14080c10001a441e4507000c140901c0c0881e191a40f981a814070b000101e500004070201c2e442e08503880031500c29808c1c40701010038001c1111811003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 908168525 1250 908167275 908167283
    0x6080703110a0206070e03010e10090506011208220b03040f020102250b03040503091012060b120c03070909060902041e0503070303050a030b04050f0103031b0507090b04020c06040b04 80
    0x140040200c98040740c00760680c0d03000140d10503070010b50000e1080720416100540a0300128010b04c1b040b007010708014030740c804495450341d90003c0d0300600c0801c002c2e003801400141040c65410b40b994503800a188921002e8080d52607207141803240d00c0d079400700301d84014050840b0b0305841341042d1034204442c0084500a900610071181c2c1550028a5405110154402ea10900c41101d103028a8080141c00040060350381d4002803068081d00e4641101650306c01ca800e5a49807011710070400c100d01214080c0d0032851052509101003039000481490060300305088100f0300340c403540c2d07540c0304a5800070290002c0004600b0240002200e01264000d0300030740356100e800c12400040002040300036409440340c41d80c1075210303210400c0400d000d0002040c0c0031000d894089410400f50001c94281c4405030395008040e21000010014140e100c003c009560100c2c9107414520442625402c0e521041c42c0034011446580745d0f00c01203981d0301c0c6d40c101c2d0101080e000c1518580e261034145100300090072142a9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 908169775 1250 908168525 908168531
    0x507051215010e130f0204030804031e080a0c0f051c030b01020102070507031140090b0610020f060a0501060f1b061a03030d05010503010c0309020f0f0102070e0106080703 75
    0x741d01d1911040c00c1060002040e5150300200900740c2c01c22810303200c0501e010320b4540c0e4559081e0a0164940001c2000d9406020019a200d1035454510746a403462500c08410881a00c6a400001c114404880c000102e61900000c6d45029003024007103210807440050140c491070111800b00c225540668035900085c0d14204a880c654000581c01e038800c0c42c2000f00903401402e420300c00528480041c0c8508840946a45504401e035805240e8040c0203251503c0741c80d8407594150481811030300d600070000ca61050a2108a810344e545602d17800700600380507c90f00b1510300803d1101e01c01c0003402d00741408001201d106007041204040180000e0080c0000a002004028000e07400384042c09280c005507a044c1300c0d11921510b07030344001c01c074802d0345200481c0160000503081d0340403c05401082804600001c1652402e03040508541c01d00f000b8809141c00d0011402c0965201c8140e0681c9032400ea988000c5482c20a00417400c198668104030000343c600000866a141d0103a0054030440c0f07103882c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 908171025 1250 908169775 908169781
    0x60a180503011404021908030d0605041505090a201b070506090a0b2505061e060f010e0f0414040c06091401030207141b01090f060f051c05070512 64
    0x10500780c407180300f4142e440c91000000b103001070a04040c0080170b58000c206504000c0d4441d60f8150a5610001a50300755076254107050200d80707014828145400c122003180950a450800850191940200700d6040d1a6445000c041c01005c0303e4046101e40410303a041580d00c140206c60b0355100c5e40009002c0d440d40c8105107010886003009021103011741001029806010319148000a0030742c8008a10b01c06440b0605c1c28001e401d07803500300500307150300c81c80c06801030f40341c54072040360061041800d401c002e150080034040c4580380c0b002c520ba4007030701c02e1030b2507090201d41c0c101040022460102c0580c201d45004403424886603082406400b492185138403e035013a54450080700d20301250300450040c0540310031003507600e40c000e80c000c0800c00d02c50007030401c0d20a0612026401c3c50403220030003c10f80c180e210300440030360b802003d07000540041500100e4907418407200401c01c00000800d40c050280c0082d20402161031081100d80c805c070703146001d000328a48820000e000340c10800041e81d030203440c6404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 908172275 1250 908171025 908171029
    0xc08131a0301062007030b0a0c17011a0c0a0807060c391109090f0705222a0e0405060405090c01080a1d0313060f0206150f060a1805 58
    0x4490480b2101ea4032800501301942c0a0020455206440542440b4140000000a60103d1050720500c001c650010f8a080c07a01c0e00541591a00e018824110902100500407841c8806218240c56038003d019622144003050b40f901d008110340f00a070801c04080ad4440803c40c098210343d8403807207640d447c0421400d02c0c400d0145a211107489280c0c0340c101400c041007030307849801c88015905000d280030401c0e888032140403d42c02e001c203030b0712000680c20402c19a216007030704000700070080070305503596040d4000d4051400400352001103c02c900503152040b00c1c0481c00c002d05c10390b41d25441c0c00000d51b03040180340c2016203903401000c6103600031030a0000007642e40c50f0500c9401d01c1900c14801504081c90403200440b00c1130390062660403d680d4507001c5195a65245840f0b04200031a04001c5588030a94645960880e001d641b140e0200000081400411940400c0c06608050110040600c94409a00040c00c4002403985560004400b25000b02502c0c3c2c030070410f400d038650200150700c02e42e441d001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 908173525 1250 908172275 908172277
    0xc070f09060f0b122a07030207171501090e0c0604080703030905010311030a0507110f012f18031011071506060f260c0403051501240c08131a 62
    0x40b0382c10903048140f000811a44260480d090038210410001d035050745c1001032901c8a0f0007844050380140c0c8604000d106d048031000a100300e1080c0c140050000165191015610700c005011310310f40140c594a044480303201c100b207000301f4007200415650b02c1340d440d920020303502d103240d00c01980010300c0081c0014480d4001c2c4228000e0f405180301041c07a581c0e0340d14209001d81406072401042111000303241400390300034004407000d10745900003c910024510b40304c1c51801f0100301f0017001481901c4665158800e40c03011120f002010780d150450038221100060b042200d00524904441e01708039000109840540043c840e00e833151008440402041043d00c0031941c2c5402060081a014101c06110781d0085078200c0c9002030710220842208009216011603440568804000010100d010b20410501780300071080740ca202c0000c0f00d03466160041d48440031107440759400300c011410f005000d10300c1c444d01141400540041c0c02e03594610480c0034042500189108005800c400841c0c608450032441f0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 908174775 1250 908173525 908173537
    0x1d10180b0426070807030315050909030a0206390c0a0317150f060d0f020f040501140c1b0103022101170313270c0509090601020606010f050c070f09060f0b 68
    0x511040c0c02c1024a5070301f50020050030a102d107940c181100000303402e40c1d03160282071243c40900045c50704c0307400740c9002034a014005003208054200d40d6090580c01c0d0008046c20203c038080900c21540c0f03084e0142400a6845a400b0a094900409260301d05050f082080c24011550017182c002c40d659803100e031a440d01e185860751640c40381ca012203400d05860030070040c2071009020704001a000303140d04081d5049a000e2444900c945a000c64208230668100003102c070501401d8005c10716280e83c4074509070300c1e1012651144213002c018a101100303648241d0684146602c2109030302c0c3e070404c541e01d911000c49000d10075100a295030017240308907000044240c0f04a02d40e801406040c8905210045008183c001400e100320240c240303134682c100312107002e203800310046601e13119928201e44040c02003240c40248400c0c10b540c40402400103590303015030541c01100c001e2a140e40c0340e1035003500740d904010b1079031701c82c40c00c3ca00620707404210001c080e801541150b1034801032401641c1c3c0c0e01e5800c1c802c0d00034a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 908176025 1250 908174775 908174783
    0xf0c031e03021b0a050307080f0c0d080405060d2c101401210215030f0a0e060f0a020d110c1501050105030a020706060f0b0c011d10180b042607 63
    0x1c15000307141c003e04142c0f001290040c03081204680310310110345081001d5202c405907034800c103402117144805200c0711075112801d40b103000c50440f0381d8564a80e6446907204540c0101400510005024151b1344213414415034220050f400b607004c000c1d44450540140509021401007030741600004080744510303046010300d00c1c5001040d07860f009000c1d5001c0120700c0e040c02a490043c1c90000140e844400ca8203a01ca104510f00f0340b40d00b01211000ba000e80002c00d80c01c09140381544034801c2c000000b81095011400d0042c0c50f0255032400b56a00190044c0c1c0403140d50681810021007602405102401c041c0d4808003c691020301940490042044207206540c0454400c202113042c8000a40080c4071071800390f00045078507a03554040d406034895951103104040380203d0300191152083c040c00b1520150403020b511710569402c03100740c035181d0820364040e40300d50380d500c1c41c1403500c03401d044140e2454002c0b070a07c501d40f40038148020710380e0b9680d0340050019607007144407100d005141c068426507500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 908177275 1250 908176025 908176033
    0x10c0f020706140f031906270203132405130c0515040b12041407150c0f020d08030402032b05031f03080405130b06120709030f0c031e0302 61
    0x644101601d450075200140d0026000810240008071404c1c0c00540c0151110300d1181c10601c422454102154515040350070a05401a201c40d009200401900d003006244407005a8030b8a6000b20b400240700741c010001c00701901f5801c0c260750003039410708280043d402d54009020641d0b52174100440c0382e80c040c100078605103103510705001606000241c1c0828040e400f10320b038501600c1d84030410b0303d81c2043c6642030000c034415042004012500b4991141c00c03070b440380207262207030600508203098002c54101c0010000e8111001f42840809080b5810075034014068420360000d07410320700c1e1240d00032203041c1e0281c8034100030114032443c1813091040d05000301d100e084002080790011247d0380e1003e0541400c0c96844407a00d5a80100c580100d001948914a0300780d071903143c03009000580b401880b601040f985014018070007070700c802c4112031620340c51149202499585142c203884451564002420510a62041d40d0401c0a4003145c2402e8901800c0000031240008400004400c400c00c0300a0050300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 908178525 1250 908177275 908177279
    0x5010c09091515030b013605010c030f05090f0909010203040317010e040201030b0406030219031205090906061312030e1e060d0c020c03101a0102030a1407061503080903010c0f0207 79
    0x40b00c2c0e0b21200105c00c051410707612140b105100c000e00085a142d00d43c1404412074107902801c051400041d00400c000c0c2003225403130300661805070858081c80c1d40703102408030020309000c507640d0f9a14000540980200400103c1c200545414000d400c115011070210340159202c110400b44280600d04844090708071810743c1d5203590044000d070544880440c0c209480b003501000596031401c0b2200c01c1070030041c583c2c0c00517142d410a9146034503414041d900f0b1040801940710240c5541c05118ad1042d0b0075501c0594890f1404644451110160310041d20001c441400f0010503920244140805500303e5946141503044205103280c902c44031b00e9503500200c2008040d16803082034020f5440d01038580140c070844441e1601090400388440a40350b0a00d545850324450310141500b0700e05030032000e00c021810403509483c0a0190101c10f607400058420104100d02044441d03008404480120004523602d190340b440d01109503041040214403a500b404404031149210b8445070904110075402061414 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 908179775 1250 908178525 908178527
    0x10608150103061503140f15090a020d020d12020303090c0618010804050f060114090a05060a170c10030e190308131e0c050a0e0702030307081305010c09091515 70
    0x114070050a400a5241c840300000420000030340d0003800e20f41100900b1f020030810044900b410100f0304903900c2c202d054014000d0401001449413901c0394141c940f107103000494000a0b40704401c2010080032852000f0f4100c140c0ba60110165014035080411641200d24003c200601401000f10940c245a4403040c04a500e62203003401607089406070b000c1c1c840c88062890450704004090b042240005228016002a81401e5456543c4808140b008019600700324000807000205440751041c5031081d00308240402005001031103840c04004e001e020032005118014010b00b030700700c0801806000d43e402000300a0301c1c4d40c9240c400b030755056a0f020080d03601d0b021107008041c1e51440a40c0c1c0740c503000d101442d91244450341c0c14101401020502034461400040184841e02c47d0811020b01201d0014000204d03000000d80e0340010ba1420094866a1021504c40c0c1407001d042e4050407960a02076007202141c0c10111080940d00900420f010402070140003543d810017074410080310542d0500001412 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 908181025 1250 908179775 908179781
    0x1905070303231207110d0923060702010807270501030621060e150c070b0c0406080c030411060d0e07080d05040e092409060f04020d0f020f040903050c01060815010306 73
    0x80901e007003a24030214524150fa11b0840c0b048080c001280c032950040c040040520419151440d00e0480030401074480c3c0046602402a80e100034140118400811040c50150701c01e610010034a100070701c5410700c3c4943c0946041560311400d4040b03841c0c40408103410317901c08000040b9010740e8143e0120b0021380d650b07103000ae10f020508401c8900620100b141e441400084650050306464a140e4841189090101540001804d91038a90342c042100301700c219001100903501521000d0788076243e5807503003040040c0b106001001c0e9841200062135035401405a80408100d910b00001c95903010303182d40c481960b0b08503440c4a180841c0d030a0104110b11a1809451035001d402d5905480854050001c03540c1080040034109400d020300300c0c104031950504002d0b160f482400c2c480251500c2c101031700800d56004c112000a0102d003443c2c030b4074009544550000b22406a4040d00c20402031060741401403a6400c40581d4154035400c22100043e145000280104102210316294900780d01e036036200c13001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 908182275 1250 908181025 908181031
    0x29010e0d0308060d290115020303040b130203070f031a0105030c03120c151312020a0f11010228030810050a0e0a0f02071a0a14070c0519050703032312 66
    0x81280c1444034040c1d84099115207203020318000301c10302c41c06d5046c80040d904000b030352081a001c550051003000007180040c14140d402c014030115441d406a483e0000ca8201000b54000e244179041c040706c000104090610503010ba43d004c0c0886031071a9803148105521100060300c2aa8580d00c03640c944682512090000c001c0c00c001c403422610100707820402e00c25141d80894070040414100020b10041c04000d4030010b40b50211480074181201e81d5a13128a94032184040152078003240d0800030219134000c100e0b42e400c0c2c82c00c82c20700c81064290000306560005451380b0480009010703a003c5642050000104070507104010301d00d4000d2418004a03076003e000090a130881c051300d9602e60b120f101f01d144001c06078140a5456400000e0781100c68518100f405080c41d146549031044081c02440101c074820380201c440c1c582070111404605109207454002060300644640c02c1d0715031002c0001c0040d40701c0442c4d1103921180d07008030004805107010700316907070f4001100d001000070200400c820749880340c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 908183525 1250 908182275 908182283
    0x9360b0d0f0807020306100605030403141e0c100902130c0212121b0c1e03040f0b03060a0b0a0c0b1003050a060b040f06050a150329010e0d0308060d 65
    0x1844a025480c1e4410194110000340e503040d50000c3c00d034080d8103040c40201d40c0103031580b04a000c500c0c40d040b401841444000c10150400c5011848006000807a40031185943c881c0c4031081041d1001d042007210581c000c0c82001c20520800802004a030128051601e0385500100303801030031480c400880d00039004070310424003103001d4039a12000ca14488000b03410004001000d02540d8035100010494880c1c1c000307030100101e0401e00040320004c00004410705410380d604070020741c210044901c1840c44c000c58009441c003081000b030205042003100080d510490089070780e40e40650b55101603000e40c2c820b03001d409000407403802441d40440c150038511342c0c001e45240c07040024190749071141030030901c55003821140c4588a00f003c0419151070b024441010140480401070f2030303d4140000d0111841c1d00c1100c00d5040014260b642a0740264040078600900c620034640780c0315203007500c81811100d00405408100883c8011181d81003181424620591545411403e0f4032040c040000701021103104079 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 908184775 1250 908183525 908183539
    0x10140a09061e0e010506090f0a09051c1d060a0504140f1507050c031c0e060f040609180504020d260c0f150405030f0f070605010609360b 60
    0x10b4201c400c20000c10803040048003000915a160568072425588003610030b070b2248820360184035400c81920003250300b04084440000d065400e500e403444c00c264100c911403900921108101403078540010203004204d00c00300c200d450750b500c00002c01259001d5a00c988001175000c0c8024019a220504501201c050050240d0000c141100c005140c4420020808242e0307080070030188100a0f0070021084600c0044000e8690a141c1e00e80b450422802c3c403060398104181d0900c0703640c01d80c44207803c55484a0f1000c020642d07036601c40d40064146a00d61182d40030207901607003a2402e8240b01d1280074002e9a0007000d0104d81c40603616196002b01100c0e81307050303c000d4032000100342500000001c24400c400070003e004507200c030409040c203040c0b40d02441860140240c0c1084009078020084880c02000200102d4031107201024821207030094442c018606841d040012444640281d2002d04a80c903006603007411070300525170b039403a5a0100041081d1020409019400c03100c0d07503040240401c01c003030400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 908186025 1250 908184775 908184791
    0xa02060f010821071e02040b040b1518030d050c070b0a0c03030f0f050405012c030d150e0106020304140d0b012907060218010801152d030e10140a0906 66
    0x701954000341501401170044001e20b442103003001c0c0291080b900c4100c0c0d00700300d10300740304003ca50306002c8411000514213000628081c0b4003415a910f10000d00040c0031514282c41c00c3c400544990300c80c000c03952480c8900340c2d00040404c0324000f12210101d5aa0300e0852401e030503a02600070303042820390510055159449c2c800f44810510505100d01c1c0114000303d52001d400300b014001031143d0f52024441a044031040012100000484110748510400010850142440c0c0490302d4900e400245140c0b0244000148035a0b0000241c81581d1810002d0086902c1c01d10402003100c441c5600148035103103482c010003809200181d00503240d1000d80209d5071213802c5415112860784000d404460456020401c240b031030b1030548200041280030708203400d0b05c1d41003844950a002660071481c04201240700c802c40d1080846244003601c070158016030380360010003500500901144003e500c1203100b0a02c2c46291540140507200c110030b12510320100540722405490054032142005481083c1c0b50001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 908187275 1250 908186025 908186033
    0x90403090e190e07030b0415090f050d0207060507050d08070504090906020c150f0114030c121f0204150e041d060703140c0405061c050106050a02060f01082107 70
    0x12507100d900703035880c24580120555a0b88044480c4000300340c0c1164030030f480034800100041c031440d81103500021586000c003510300120000d8112464014100c1d440e0b0513412041110000d070300c2000c2002d0382c080e6504d081c0c45400860f0384e4042d40741c0181242e40001d02150003240a01c5006400900d40d1038214542500c5000e079605445c08004221101d40c1d000640076000c490134044c0394102500e0705484006401e2104039000462018043d560740da4080e24514815030760200410025018003a050381e04904411121948072501103220141c018144051060700c000c90b0b100721002d8408901c2040c81610f82d10404541c000b100005450300a9a10b10105002a00f03404e502c072a40448400100324510b4145001010b42d80c49003012841c9103920400d00c8034503100d000941d0103859003651210340720114003180389150b514801141c2c0c1d10500c0c200004c200240c0c014020320303040b0000d4080340d01c030b83c035502080303000c2d1203003481004880c1c0c01503030707020318085840d40d5916005005c058495040c41e00e1522 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 908188525 1250 908187275 908187299
    0x91e070903080a1d040516050c0106050a0e180a051b0a03080d05070f021f05190c02030a02010c020a021e1503010e0a061d0105040b030a050a050a1112030909040309 72
    0xf94150118002c0c1d4150003004500d840c004012542c02d076018480360070f00081035841880080c0c01242800360100d1031510081003584840300502c2d0007001000c960b03903101000c072414102510101c26400401c558225200e400080c103440b40daa0102c0148501820242040034030b101d40c8000e180c3c060150b003400408500c0400c05401061001503001405081100011380505030b021024020b5420030081e0170004c9510f003810080c065200e10020070180c1e42c6080700c0c19403810000c90700000a10b007030078541d1020343c004050541016580c008000c07420780e14400b070b40c2d2100700e45c000030751084142039000301c2d041c00901c010107030943c05000d00203040403006082c0c1c0c550700260010402d40b5503c00400000c071560380190401400d101007156030101354150004818001402001d000c3c544030030f5800d94544081040650064018064800b0b03204a464016252071a8281c15180d813800701d0b6a110f0320b0324107103074103c42d6a070f80b0800852400260500340190b520b0010b000707a0500c10172990024120311180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 908189775 1250 908188525 908188537
    0x1407111002070509040b06010e0a031a0a022115121216020d140d050408060612100f06030209090c091303021c020d08010f260102040b0a0c060b091e07090308 69
    0x408980318a203804000101845c0c0100c1c2790a100c3c043d0307010108046601200b107403007800c004101d040e007a0f568480d2444041d105031a00704461140018098408800040683d40505248000042d44503a6042000b2590150b0031240c00c1c5900450074890040e20700500418104029210800020241e500010507900c0d40050580c0c0c0e80c10b15400703030801000180455840030081c0d05201e4101414459400e584201c0144064051082d03503030034440c3c403c4200407042c015070940b041484484092054000034040740d1000700e0085421201080041c0b401007003070045034801804002e941d56400482002c14242c0d41d400f030701503010b05000c942c0154041a001610100f6640007080c12401c2c6400040003480140d20119403a00390031818004681c0c01d4a4661100c004507483c1035400d800000745600a10540c0d021881c020000030b100155141c004446802140c05588100040e18103d0140603402400703c4014801154112070304442c1407006c80b050717030408400d20380b0100d0b240d00d0360340f101d4413070f4061 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 908191025 1250 908189775 908189783
    0x9020702131104090b04050f01050919050c0408120c0d05030c07020a03030f020606030c0907200105090d0f020c01050a141b010e1b0307060f1205041101140711100207050904 76
    0xf0240a50a000d001e21961000c0c10f07503040042e4944460454500e040600629101d01e07180808109500903100035548500c958490420150400d4111032180c0d070310511400764680141c1c20304507004000034043c2e442a480c0000070300680442c1c004111001c2d4001403141d11121002d00900c0b000d6101d540f00d003c0518425110104000340c0194042c2c6400030042c0f40320f00ca98080103811041d610307511003903a0884401e003061499944082110030310403880a003054010362070304080000c1c0300c2c4000380340c440011440c1c0340c03a518480d000604a8903241000c5403035003c20b8003006000c0301c01e40b0034015070b031440c6800c01185040c0000f1200b5510403d1500c0b82e000b006039165850091200410300c007510321003524400900884040e90301003038450300540301c0c1009010081141c2909140079640000c0d907203208000400143c50b10b4600803100072a49071099000510040300011645044c07030445074034580100e2000d40506002007081603840c4020269400c40c05024000607694a515408034021445 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 908192275 1250 908191025 908191027
    0x806060d0f021822020307030f0e07030308060303030115050a0309021c140c03060f040606210c0f0b070204092105030a0c1b080c01110705030c25090207021311 70
    0x3550303101a0707081400c012007510504d01c1009240721082c01d9642e42e07803040c1c80e0440c00350704c0c0d0b0750308441a0010050ba080038032040341017401114055002180090949100c1c0d11a4122511800d041c1b641d01d000c02d00036040000c80d21004030860b180030710090a07590015140124070600c099000ca48418281a152002c03c440302802e007040007540302c000c07005141510001c00100380050001fa0f900c06000d40380c41403010707500020a0030300c000c60300540042d00000300c004022103d134000940d9400c0000070b0540d440c2105040100d4204a901440412502c0d060b1060781400641c1e000c1100030840343c0340480e038460400f10511000312080c0e019149441498070f403280c8030701c0d11040040503503195400d041e040203040c1787e0300c0c008d0340e040b04102c0c58220b80051a16444986031882e480c014600e24118900d080f60115154040000010082020041a5083d1101c1c81c55803c0780390511500994040400c2c0159074040c132a14400f80e01a240c600e0005207080d104a8041000804841c04c040c2d4441040030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 908193525 1250 908192275 908192287
    0x60303210e070b0310080307051506040c0c02090601031506091e08120c070803030c0304050c22091b09090c060e151c05090313060206010b07030806060d0f02 69
    0x4010010240600d05525080c00781c21015103030503842d070714a809a20300f031103804804036010140d100c107220003420f4007804403550303950b680c1003465032201160355035481034006400090300750500d40200741000741581c440e0074040300c2540c00c0004050740148200e04269a80e64410150120306041e04002e20070354135240c0703c06050070341150010400e0103d02c15481c9108004005600f00040c140d00740c40c4011501c20f0300c5040e140b000c40e0030802c880e030044c10544004030501542d0680480110701036481242140d104034005024416a00300401c14981c0c59407a55406800e4440e00b60440084680300c2c01c17061955024000034a402c5001c00c0e000202c3c01c42d0f031000305004100800c0c041501074410307410034480700301607407002802c45200e512035441000800b0400410070100001c2100c058980804148105c3c5400820950b49810030a207407030451103282c0c0c0020b44240089201c6040e5000d01c1711103881e01805860540354940080e241d9a00020100200b6044000354031491103c91034188016079509 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 908194775 1250 908193525 908193557
    0x120b04060e07260a1703090a1b050103050901050907150207170a02010809030f07030c0f0618050105070c03021b18011203081b16080d09060506031b010c0f080d060303 73
    0x1410010035100302d503100844c03883c0402c2413100340e050802c0c00c6900640c0d50355140b00210b0708021300440024441111020b8580074010500014006d4550a90301000199503000f4014242c400039070390900c003500134041c00d005134240c1c082800011100d60045404055441c41d039000c5544520b041c210702e60308452840002c42d030340301c00980e401c950000c0c000c0d4100280d5111300900f600c14070f0130003000e104400708400c082103440c0c040c0c0711100707401000030841c0416140300c258052503200c4003258554a4400000c6069000e41410a45a601079008200280c80c0c0d40c5843e5000a04c0548070b80d2018014004d500545480c0c42e007207002c0d001020308a1250390003071030b014102000203095500e09040321240203251030410350070380380388002c02c0100d000f02c8107a07030500d07108a125503701c0c0d40c4030506040450040c0a8950803644c000c11013a42141c202d9202075622800e051103110354031703000904181003000403802000301d1512103030181802a140c402803a03066801c444680d40101c1c0410360002c6209502 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 908196025 1250 908194775 908194829
    0x60114311206051e0f130605070507050124030215090405042a0501050a03020703030e03030a09021c0308011a0f1305030c010c020307270903180f120b04060e07 70
    0x10403182c840000c2d80c240300c88001307410b10400070140e04800000c6030005020000146650740c000c0e4100380c0411541c140441e0050082d401814241ca140d07091181d0400c040c19144165401071b108403503e80c10300e070304550801116200c60340300d00980311002c0c0290001640e81c0c0c403c0c1070050340301e180e08107039841042120a280491100c0741d081e02a040c00340410140c1d03040710444030008aa4940143e0340e25030303890168001c064907144000c4522010040024510301e85d0300010106001701c0d05040c41002d00c6d0f000494022882c58010002465038004010503076103100e80a440c4a1040300706d5041242007601001240c0011580045901c01c0290800480c10140542c00120340c080c07070b02c500e0342c06c8203402082c1c0d00c40e802d02c21000301c1c0144803548601000010410148001400e409110945c00e034200144018401c03100340c02c007401c410364001050f940e4007404c081115240001040c1c1c44903107441d101c803078581c003c0050b2441a01c4590443c0504818400c080240c1002e410751407190020804091903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 908197275 1250 908196025 908196031
    0x20304030b010f03050307031b171b030c07060c030918050a14040b04150608030309070f061d13090f050703060c1b110105090603040b0a0506011431120605 68
    0x90b43c6000c003420300c0821400700c1114840d9405090204002e4650354030350041000202002d03002141294245041c50034150085c0000031100380501010a0300d81e039166140d204009154449510800b400c0103c2801120036103c1030340030b0304040c01150307a16510707000c0101c00c06032141000c80c0e5920030000400c100b4030a0b82d6207000961880c280e103140030359809503568400350000c0d11101268071190071012185e0010300140440700705603904c90602c6100e0f556a4440c600915221445011010030254400d44003440c042000801703a8007614604410301c010020303503142680301385840d80300c0780c004240f05104100c44184614002d000c0c00f840c50601c0400c813109c154040d81041300034200040a00c030402c80031011207401005050540380018016034241c49124490b903003100010080005202c20310b1007181c400e0150400030b01403581c07007000450381101c04191102141c01b05000403075484160b24000e80d021b01421f0349c4107400b020070200d892a1010550f2288124121003211403082240341c1c020b5a070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 908198525 1250 908197275 908197289
    0x417010c0914010807030b031906021b01090c060305100b1602030706030c20150c04030b0702070509010e0a0b040f090203190f02010503190f0e06070f080c0d020705010606020304030b01 81
    0xd00302c2c4800000a00480c00600114101901d42614104541c1e0621203c103050516080c104180e0340185088006034120907001c0c1c1c142c517035105c0855032040042c0100004c003a841031458206500740101500204000390503140d020758503003000300e000700c581070051411414100264844488071b204142c5018283e4000c0e808060400b9000c800321030f042450304110b91900390000c1d1800c250183c0082c45c0c80450040e001141d6011000c2c4429040000000d100f5032380543c1d40742c09250398075642660383e8200d910959411000700d00041001c11034814405400c40f0312000003080c10b03540300c40001e05940301c0d64403008050795120007900441c03804201e008081704400c3c1150b010b0f8000d035100d100030700b150a44080e06025002000035540c20014100036002100e00c802001100050148203005240d41e02e29a80284a10004520001c2c081c000b8410307000c0c2517641d080300a580c1c1202d00d070b509410221101101c1902030124500040d820701074000070300a558021034407185182040903c881040e44510 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 908199775 1250 908198525 908198549
    0x60507020c010e01050c01020d021b070b0307080f04061d030a02010b0a050a060807180b040306050105030c0321070f11030d0c0f060c110d030b101b1103030417010c09 73
    0x5901660000c290f4a4180c409092003602c52443d8203a0f140a48554466403901c0ca200082180c9800400714400d0000c0c0080b0b011102c0060311040c415006100c00d442400101d2903650025406660f01200c0c103902502c070f4040499890100d9010150001d81c080b07042c10705420104055046a60920401840c2d8008442087e60f0303e00d00404181d4220b140d0007200c0401c15200d0028401e2405117104440c0040b071228801e90b01940d80c4240e11464101d0b0204540c90f0f810003000041c01e00c0c0004d029001030100a0280283c40d5043c0a815581540b10302c045204c418240071010116150080c24440c09005107040041c1c1c503600c20815040c420040320400030700012260640109100d14158401c00394010000100314464a0065429144910340b0130301c284202002c260320154950498900c0840030341b030a100144e42c620081e186520350354040813000316181245030224100c11070a0140d1039014041e2840c00c1e0700c070400d00c0d64500c1c1c0c83c0c002207810780d1035481010540364041d9812380102440c0c02c0070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 908201025 1250 908199775 908199793
    0x150112060e0f0709050a0b1905091804060b030d2f030307081012440904090602040609031101053108070617060d050316050a05070e0406050702 63
    0x1803100000054052001e03880c20301d0005400c00d0050822130042d14000700300d044000c0d80d4901e00c1c940e0b640554000d1f10300c070300e40705886d10070140a401607400b0381d8001003100404204110203684410801030056480f640c40e4840004652001d12003011004501d0703541420702c0d00c01c903001c100181c0c3d00410000c1c3c0044604014046003001000b52908120f06144c0301c000c6842c3d015030304c542105117401100d00c00c20602d00e83c10401103110100c03104140710340102840901c110001c81c04900c03091824047d0446030b8162820010011001000c00e103900800005510781c031038446508030b070029040000032560f00c42c0c05109105520401c0348500c9030904c0c00d20315000c21000c03804902101c80610300c0300e080045101c20598070140c0c444e01301401001045071141d503950031005251007588484082102c0d006d07008242c03141030194024150740d8112004500c0e0141c060701203c051240000d080e203245c000d40bc06400090803e000e030800030f003548010f100017418503007080d0782240c0e030140c0258250b40c404000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 908202275 1250 908201025 908201039
    0x5040e0307031403070e061908072a0326010503060a090c120311010c0203091504030b0105220504051e03030601020a02090903041a07050d0c0528080315011206 70
    0xda81c03c84155520b406071651100141960580c51002c10598003043c007040c2d9142c1c02c04400c1404d600092195210040360715540b4040d00c00400070307144020410b201004e0b01c0f0300fa07503110840010580c440c1c076083c80e1500c003074036807680d002940702030305002d8004c1c1100420140c902080050381146000d40704214060f074598035800045500d01c1102c800c0a20088800141801041c0710500380191000910008103c400c009490b9800240414802c2990780d0303008041c1c15105040d24107482d800603001216908000410010a148058440d03d030041c048410840384003d0003468010b03880b48005004101c0c08441c802465142c061505019074400d0041102c181e1340010303807a002c0354041d5032401c0c450f100c03680e6a41c1036104071b402001d94001101012140c8070b1845000300f4a4134090010355084d401c200c44101ea07101103601018003da4018154003a00802030520148038142c07000d24044650740325a105070075504103e680d119511611152280c031542c004020564407503090a080000740e007480a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 908203525 1250 908202275 908202287
    0x30307050d09110409110406061112090d05070602030c15092d031b12121815040318350a0209041202010608190201050a0905040501060905040e030703 66
    0x41c1010020386640101003030100c08164007000d490060300038080e0308568100110503800c134181e140d028620b03021000031100c1c4200c00020b80b46c09020042c0014000c408901c40054000c0a61664003803c0c1c46c0340c10300020410040b031070041501e038020b107490f4222400141d0500c62400c0e80903080701036840411040d55004140f020550114810b4011544141c0c1240d465060f402c4102c031030300344030000d4110304644009201810040156084401000c41041d0383c80040c0110012154840ca40c503001c07442040108200002d6440230004442005041c103032080460201614117801058084202c0100002c0018665001c0c1c951104080c290040c1c03800c240864000000906070301880e10360b1034100107070040c00032181e1607800501014050501e8140a41c5001c0ca5141795400b541c138240e40000e4800011a18096034452030103040102400c5070015121036101521100410011150100e055550345c03183c68003034181944c41d07800040c180350070300c01103643d901c0022083e0790080c4154800139600030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 908204775 1250 908203525 908203537
    0xf09070f050910030636110d05150c0c1903050307180f03051c020105101815061d0d02240c0109050102180108090c010503190501121403030705 63
    0x910b14140c5a55411a40000e510980c3c000034852820039001140c481d00c818016000440d002c070030304140001020050594100181d002482d0017074114920802e450a00405524180501c066584200b800d100ba583d00e00c070101c4800103098004955138450300d8081041c20041e98110454046003040303502e001d4603a000c001c201400300201409403d03046101d585034007000300f80400d0031103138040c5c8178940304e5120080c040704040c040190207580c201c5540b05003c0d40d402001a070a40180711410500400510013001c1c005c8020183ca84000c000210140307004a0000c10305603654800e811070142d001904070490242051003038500068240c0940d88aa22400b00031301d00c8175929810318030030400150302d4054181503040355440d10044c0d9047c0681900207010840a003684960040035000041d901d43d00c0595180d41d090340304030301d04c084179405240116046015081208402242040500c082c1d400980003070441d9200f18030a00b04204442c964015803486d1140554190b1600c840018100e0042e2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 908206025 1250 908204775 908204779
    0x10b0306031b040204051507030f05041a0f280905010c170a0c0b0405210a051c0e0a051c05040e28060914060301020316080405070b030f0f09070f05 65
    0x12004202c4680d12079044400902029060b40355880000002802caa0819581a80400c42c0754101046d4103208104617010303134811103103076914020000301414160300107032000443c500d41008910400d03402050456040100400d07901e0015040c008010020995030340f10506004168036044001040c9046000d000b0310641c5041d61100340d02c050860350514014009040c00e03041009000620001154034209160350f50306110420b080c444008103544070300000d810009006102811180c95000c1e50141c50414456001c2103940d003420002d030408210103002c0340c0315440042c45100c00740480554441580880c28081c0c00c3c43c2ca001d155200540c0c0041a10400300040030780140780c0c95000d004148100070040040104d07585031403c5400824070b0060741007045c1d40f80c800141452405008803881005440142c0b06003450b0b040701a5210103000d041241d65001f20100840c600c69900043c2d44205486407030381680d400d2120f043d9030148000303004404a41c001c800103100441d9201060400c40301c013 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 908207275 1250 908206025 908206063
    0x120813060f090e091c0203030f0c0421020a032103050907290d02030f0403021c12111b030702010831050f010501090b0a06034a0a0308010b030603 64
    0x15900342da030305000c40144541e030500c0d0303090307a1512011b90001c060f6204c0d01c2424072109443d114000100c50301d009500c1742100c4003500001006482d10540400fa144500c040c2090340d240b9200d64130001042c5021240700940300101e00620792150381400342c40d400c505100080d001503400c00e40c49907268040901114450b5030a03804000c40c0c154280c084500b807446002e801c42d100d04014051205029003990150018030a076802d09c503144a00200b644401c1d0607036140c03d5543c0030035082c03500240c909610a201040001c0c4a004c88402c4030005001d1011008000f40d03540d4001d620001d0b00210014048c2000c44ca2441491040f035007010300b900c000c8905544600d400c0c046d4034500640361450151081c3c519508020000410100d10740002c00c80ca0011600d50441703070b44400040301203500484041ea441ca20304010f44104082d08201c44400702c0e04030241d203d0100001d14800750300700400c806d5240c640e2003219040c040c55071012880e4094001030748407a00d582403440010313603240c000124040003510 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 908208525 1250 908207275 908207281
    0x1c0b060f031504030801060e060c071503090606090506092d151210110c0c0d110a17120a05030708180a0f1208091510120813060f090e 59
    0xa41041206560900140c890b0403615003440c0007020704400384600400301d1588041019a490920213681000201500902c0c10a18104e1590811070301c5901100600d90b4500301100420034501503a00a1b004200000c1100c0c14200240200d00100909600b030030a0041071050300103081d800740319040328180703500001d1034032403642d00348014480d182401c2d0311240d2001083c1000101180e00d030a06601d20400b0404810001f03428403032845000c60700c1010703070000002c03401a40b40c1125010252400b4045490741100740c6e001041ca40c0310250081d4151240c859981840810100003241840c1c4a11003698100344080030b002c1d0190101406690620543c0c00008003075502c0c1904405019440b402101d401980c00d060550040d600e10509a6606404240b0087c4d0113024809040c09500c03614000c0044280c10b1403001100c11001e00110100005007200050110a01c548000800c0c06050a035950f50790001ca09020040c065200105002c89540e0f823060380c90308500c84078216285030020544540d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 908209775 1250 908208525 908208529
    0x609070617040303141e0a0203070905151218070602010204060c03030b19060c030e090106020a150e100609050603070513020c01060314010c0207080f0307060b120111091c0b060f 78
    0x104000c3c49016200740340c00b0420605035040e580384030a0750700754030284125490b13601c0c0e039006034272040394098041441c0c0001005642041080e052070007048442c024203004404108021000c01902c031003006001041d01d908210703406001800060441c1d00003107160520303040f400f600714038010f00082c051640e11614540f00391110b00701c15200311065140454004e4498070050440c001d42601500003d002006105140c10a00d07415410303581c4513001002c1d0a65141e1b100d9140c0760204040c406210740b543c60030342e008a0100b08098546d0544800421b43c28200395490044640040c0124032030790042001300b2a54840d4021941e211100000c00359696010460310307400341c012984010008800c41401583e222819405291540e14903821b82e082d40d03503a11580c59980b21030002032001c5800801107000040c02c264004102080044c280740050201c1d600741908580941248160035900003a07455407910b0092100750040b150360390703a01802007043e02c07116103080b0001c00c601d001d94040e8582000c26 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 908211025 1250 908209775 908209781
    0x11120a03022e1104061d130c02071a070201030c0203120c13050a0e010905011d16140d06031104020c0307020904020a03020618030105010608090d0c14120c0609070617040303 76
    0x3038001c103000f40f00c008001014034501e9400b91159500103082d000710b070200c3c2031095440050042d0000c0c02d6114801c80700b07259000034062101c8060541c441d459000420a0742d49210b10b85003c1d102d800561111424000035050300c1c80841084210b4000704210303076910481111380c0340c00c018406009a26a074049a001e0080d00480d003141c0d038400703038903800003d00c01101103d107030580d4400362041c0110707646c0c0c400352046210f0280c1c503070303160f500b0060010307480500001d640081c4c005103151504090808040301c02c0c840e40700c1c510000c0c100f901c0344414411700695205030702d413810081d101180380506000da51a12030040c08002845a0b1518011900359a54034030907801454004003415902c0100100c03030884185074010581c001c1d400d01c000000c042e0300400c0a18031440100b0301030f00300b520001c50101d60403804460116400b0840c4501882c02640400c000d0078114400901d46075286924100710f894410010074442195100513414441c141e40940c21420440c88520450201e440d14a81078001d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 908212275 1250 908211025 908211103
    0x30703050a270c170601090f050c04090f0b04050f04032a03030f1d070e1b19020709020d09170a051b0a12270506090609031911120a0302 60
    0x100340c4e00c6615042109001c54290b0403aa41d0316010880300e240028544140c40741242e05411000f81480108456100b581160400c020000e20000d207491082c80040c08a48040da800e4503944443c00810003055040580045030222400c05402c0c102040b40e5000558000c04100400b015220031140628007510341100d520048070742c1851100210224a495440003d80f01c2e501010401101081c5c9412110940d80000c114000c2024541010191a400c0410340318180310110721407103600060041580c0b02901c4000c20003100410b2244850030720ba02201c0300c1d2106104040001c210419600c0d411078100c81c1001d000b074052002c542c1c2900c0b1050300306184040d010342407042c18500702e00400c0c0d0000d01d00d03000301d040c41c01040802003803075640c0c16891158094550030030800c0040c0310a524041024081851006044400d26841c150081007541c000c500701702ca4084120070320030601e1501a1401d544060407000030203400c50b00740c0340255070385404a012484081c2c41c01031030160741e00305880e041c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 908213525 1250 908212275 908212289
    0x12030f051b0903070801230703140103080f16060f0606110a03030506011b0c090c1b0b0c090a0e0618040f030804020d0b150f040b0d06050c04051005030703050a270c 72
    0x4491f11401000b42507544020401d01e8840d00054006070429000b44101e030300c507030422500c1808507821691008020350000c4100341c1c00c00c40c01d101c1c148070b0003001010400b61030f2088401103981e01f010000c80d015181660815424030000b0240c03481d00c02d0300050440c080075014074005c1860380b240401038034140704c000004010254008803110a015045402d0011521406c17000c10002d16040d0040305d031068805141e0f00450360148042002c00c050307082d40e035005501c00f041c6601d440308880003d556050b9542c40341484500b0213040040925154880300207041c0e4407440c03002d0501e400d0b55941d6151054100003403d2010f103901040564482c20740701d05560b940a04050b1b50350800401c0c1c112000c01019055215002030035280781e090415000c0c1c1200090003600490960a80e6a90030015101c020075843c4100d20a0000141680d19002c422201c04d030300e602c0d21079481c207241000809448000349030400b9213040405003c01c1811104a40c6801c1d0b1068101140071001480c0408a40949501c42c603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 908214775 1250 908213525 908213531
    0x6031003120c110d03170c0c0307030e0a05040c05040b0a020118200111100f020c070308120106051615380301110301050108090c040912030f051b0903070801 69
    0x1c0d04580c001800e00c071080d019500d00804814403004204944114820050005004d01620441e4039003000c0c06940010307241000c0b03420408005c2803a0b00c5c50b040418160f000512900d590071030340c180f051041c5c0240c4816102402550003005000d84180b00703611800c00341e40b0b80002c91a10f02c0d80b0039800320f541c1c081d4095114164000c1070805d140f681d0352000203088041c1e1448000340d4a503000e001001d6030801e0000281010740300e5801d0740ca0007407071001c1d81211101e408004940181206101280103140b0034111a611141c1c0821031076040c800580101051100400501c100080d0078030008003200d07800f606a100826035902d40b0009000c0d51003561001d2a6892760410320442001030702c555140405240d4040c401214082600f6101d0301d041c1008403920400040c03106520505040b030f44001c440c2c0c103c540e00d4400c040820100d0364815030540da40d071030b8143da140c8025454003841c0440f030860002441141030400041401c0d07011f80d030030041800fc000a00354407a4500340200002084c00720020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 908216025 1250 908214775 908214803
    0xc03030915110d0e190803041a270301241a16030e0a030f0503090a1401021c0903050105090a0615061d120115091d060606031003 57
    0x5445a086409103034550702003504120800c038440c101141c40e441c1c1000c01080050400c0b0700a440c400f43c0c400c0240e4000c440e00d2500d03200f6172200749494000b000c16000543d51031345852039400c452070b03003204012050b860811404e036481c8600406141c9260581342d0040714404035900007030050035451320070b010071714100365822440c0204045040071030f000c4c00e241004031040740c03400c0d039040c0c1b140d200700d02d201e0507a000910b800309109041029201001425040d030b81501d80d1202800b1050740300c002c0314035610000312030000d0305014200200500010306180140100440040e445001703001c0144440d41c0c1203091204094032a51514004580204c004c021070b0814a0030541c07100d44942c3c00b43c40403424010401d00740d0b200181c0e498100c481541c1c4085030307040e20030281c5114411003c24598411070965114041000a00c100f5549503020303599489100c0c98182401c0035500102980d0491055031208880701203000701d40c0c0c9910410448000f9669034820b4800020200550009040d11748850301c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 908217275 1250 908216025 908216027
    0x204111210060206090129040207082d030105011e021207050705030d1110020903010f05070e030d030c17040c090e0d030b0303030403090506070f14070509152404030c0303 75
    0xc1c1100390368141d802d8420036540d086580342a0f402420102c0d1811030440300321800b01040010b00c44244d080184007502d850181d0f1100c141c1a004034801502030004000d0800d043c0d025003250340d44801d01c503205181550b142c1300010b031031043d4100c2c00d014032050099100700201c0c03080c0680d13800901120321681d1141c0540c148a5034416290084a0191280c240300c0302c00c1c51b01644810403a40c40450081c03003040503100d180400b9412400f0283e070559261801545a61514016248100c000d5a0354070742c81c10280b400c0600d020424099001818036011001052680c08203c10400d00048043c00031940c035540b03400f503039181441c1d00c1910600d14180c510000128041903168000300f02c0d580a100001d04182095203070f03c4283c0d40140030501c071032410032a40c2000400352040300d000c2c1992010040c0070f070302d4035044172080b00c0702520f00b90844030051142e45049000701d0707085040c1090007011120b1010124040c8002c0780002e0101d01c0c9002c14004202210004603405540d1010a1901d8550707a40343c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 908218525 1250 908217275 908217301
    0xf051b1e0d090905160513050a030b0405010b01080c03060f1f08070908030a210b0406141c0b22061e060e070e1309020303031e06090106020a02041112 66
    0x54001e00080758142d001680040714010f250244103640c041481e400d01502081d02c203070b4040704040140140390000010580d55141d46000110b00840b5100718926003480c249084a104801103410310015a040c04920501101a42d601c610242c4010200c81070b0a000651007042c640b42e031350000090742842c00003003503000201c0360164019440701d507451900c2c0e002480c2c80f805205425000100031901c0045000c0c0700421030382e02004003080020741001a680802e080d81c910350401840c031000c6061201c0e40e4200b084100c040d640c29403919210845040e030b5031010b6803401500700140d0a203000349032848040340180005000e50301610400c204005e43d201403050f148561b1034408040e15020000840340403600e203507881000395540d1801010041000c01098031040004441d240355075250300001030b10104000c6000d080f440b1445007081d520504032142602c0000c0540740100c0c0c294004120706900020781002480d41183c0200345d088403d40c80740c01c1401340c42e1503d8140f511000c18001501b101030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 908219775 1250 908218525 908218543
    0x70216090f0e300412080a1101090c141503062716081b0306040e1c0801090e010c0903080a051e190315050402180d080409050105010f051b1e 62
    0x1e00900f0110a60ba01c0c1d01c04140198031401059825840a200010700214020003540e400c41c1008402054040c01080c2180e624420480c2d2040c2203600c14801131a0000186130314800840f071a203030012980c01d200e1402d000c0508080d0094980c1c00402032407404098522003580a64045002c035841c1004145084000580c0101e011522403004540c200c945540c0d20103107004001d101a28584826062000900c0065082001401007022040c00194000c003080740c8004c05684041c80365040407112802c03550521040d6656a2400c41d207100d00d660401400001c90341c0000100d0344131100c95605444510403001c0c2c085808101e40d0080c40000d5844000d480440d1110010300c0b10144424402d0f0101e445100075182c250210600030010707854603400070000d48034135510024080b104bc0020800354103000354201d4001402180612030071410740700e0107004010920b01030280d102d042601600364841c0500042000c000400090403503041000940c2e0100f0129200c2250f404d08583c1c071070340380c5e0088 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 908221025 1250 908219775 908219833
    0x403031214161e08040311070b0d02090411090d03050706090210110c040b011421012912070c0501090c06030e011508070501030203100824070216090f0e 67
    0x540c1c0c043c40c0040d0110740f81100b540b264407000303419251524250740d04944004212031502c200a804640d007041c04002d0000b03441071400c05601c40600c1800c000c00d880c025803080c101d0320018004030109a44070081084407d070941401c2e503544905e41040400b0f05815540690030a0400f00001c5400d03074041d00842c009800102900ca64007001d004101c113841c400c214050000d41e54502030126003000350018030305149280c1ea026040d01d160840040e05000036131041441000102110111000541c5e48070000e511030054140350610b44400d03040344410281102c410400d03401e01c0e034010070400350b01c009182e5801002040050f543c4040c0100501901410032459500301614010300aa00c07a06140594852901a02ea001d05010044009400086c07110710780010f032090000e410703641404402c1602440058003184800140a145080c100240c81001154091303240d129043c0b60110282041d10301001c0040b9070124a458540058040d001e0f01f84201c0c0a901032044404c00c0003904402030710380e0707 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 908222275 1250 908221025 908221037
    0x106030b2704061425050706060329010609270212041b030510020906120903070201030c1d040908040503160f06081b07020d0f15050603030a05040303121416 69
    0x1400d0304a000c05071081e1803d60013841d01c0d50380b50115117119100107804080c546402401d0191549861051b80c2082e0b0040c3c0304140c0d43c050780c1c0390320f40034112154001d0244012402c42c0b03514024000340714030300b50721695521824034540715124030281c1d02040d4207907804c03003019915440301c05a11107001009450860766480c95103400c00e1252031058400007129004806400300f8004480603001075070240c4403c075801b4004100801a1200052101d8001d0500b40f00039910b03a416440050708907416200c80200303000c1d042040c5120038043c440138031030f40103003610007190801c080d14044480707001b55000ba0f40d1600920035082c40d0707002090302c00c00c00c03180141c8085d0389451f070701c20055441c2c3d030060301c0b00c20324806200403005220094078010f100d001d03c098090040c00b141038541151203e503414040312104244a061503031250503000d00c2d60411003c902640c41c0004400c005003003403156101c0202401000000308485160b40d502c2802c0d8000c8101d002c10051501150403c204000e000009c0d0110b59 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 908223525 1250 908222275 908222291
    0x6010549080a182102150a05030405061003020901050d0201030e0708030c070b0a08010e0916031101081f3c0816030b04061d1b0a1d0106030b270406 65
    0x40110003c00c2101c0030700d41c0e4600c0960342d6983c0d1414158240c01e06a801c01d080843c03040d41c07504018000e01c07264540c1d540d241c1e102d08041c03a001d407d2800240244003403404008041c800b50350359066560450380203c402400e01c014910058005d02440c402160843c0030f001400220500088020102600c055060761000fa488000c0d9007154041c0c1000000001c403084010700900302a002072540260070312080740c211051000a441c1c410f0210b81048030284c084c2c40c080345195801000103504000c404c9203551030380a0401d1451034030800c0340f24080d950401404c020b00c01d050085c01d100bc0a041d900c0410300c0e1400110401c01c400d40d814401c00c5d010744a401d0030b2840b03841c0300d1110401601e601040480305610383e070300d508000c0e06103042602c21f40e0102e242040c2d10840e0800c02c180001c0e44072132400010520f03070020070161400380e5000900619203846941c51102002460905544482c100011070240c0007022a0b2804845080220a0404907001ca03610102c000c2810784603500c100c40a00201d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 908224775 1250 908223525 908223557
    0x180a060c0e040516032a0201020d0509010b09060108072705180c0a0c030e030105150f060a021e0a02030607021c110c010e0f0a030c0806010549080a 65
    0x5501151a411801000c0324040345880c442d8000c4280901c6c0c2d01c003904000c144506400c590001903d00d900b015039400a005980c1615901955611100c210000c02c221030244010400c541c00003807149041219040c00102e400c0d01a9a02a14541000e0702044040c0620134644010040781e0003160f21130480d00751200241030050610328441c0a000c1801d81c1031200d440c1c01070310054007038601103003400502d006882e6161024440c00c0e00c0340c0c0c545c40380480d403110b00e8003c1c080111184210705010b20000c008801e04207400081c8040ea15000e100c1031072424804103078550401114882c001c1d85070080740107020300c840d800244030b0b2001c401740c011810380c82c1e031221b000d5942005000c1c110b005908030320444a0f02d5030151401c1c1315444805007160714000445400100f60886540080b9a402841002440380b035208000c4107000d081c5c242c41c104010b14502111244000d40000700101c2000c140b240011100702c02c481c1048403150390107075246222031a00d0150820313080381d2000c0b4001403201c00341c0c12411b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 908226025 1250 908224775 908224781
    0xb19030624031a062407020f01180e06030a020301061806060201060501090b0307090e091b15070b150924010801240323061801140405180a060c0e04 65
    0x300d90100c00c2e018410801e0220f00c41100c0010441035102030001003102c084420811112441091040c0c800da6600c02c3d84100b14249103910b020504111030000b0703003d607180300100c00b407082c0c6140345c00401142e41d80c140040c0c80d100e0180c00007501542044000a503031681c003441820180b6003e41d06103c0551500c80490880380648526400174407100d6082100e075100c036009503042455490a00881a15041102d401c1c040030758040000d0b6000b0759071200d1541d40b46490600540c001c440455001c0d0f20050794550b0760240c902c002c8c06809104010803402404010120440c04014043d03826070b24003072010078131035284842444004031002021102941c85460340710f058580c100030000202c842010f1142e81c40000009040a05644d00c0caa07070300c0c0e0300708541180400cae0380a480400d454540f49060102c5080341480ca4001c03042800300500c00c0031080c8040c1d03094050152030004141d038400c00340341c046100740044102d0720b0042d020b0b00420300125810040c440c0c402a1118028a41a0800c0c8021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 908227275 1250 908226025 908226029
    0x60c0a050d060504112a0307030c080c070305030a14030603100e100c030510090207030c15231f4a01080613020f040e070b0301170106060f0203030402040b19030624 72
    0x1281d017081040000113802b844000390b43c04d0141a5482c105104241c1c001e18216140d0826951365001284481d150340d40008480a04184520140d04508000b00400c0d03507004030768038007000c2070340755000b50804d214200700640d001d040040b03003840001c040302005001410280d1f941650381e00d084002192460442c001c841503203515135106201509207840300484216208000d152a54a503180005500d0b40f94045030907504e00081c13004e900b403c24024545999000000807000700030b054104101100702c6004586581c0d41c104101c1801c1d00f03ca030190810000c5607400c40d1000c00c054042c003a00311141c041c1050584015034229405929039000500120001c046c009504c61105002c0c480c0d5800e05420401800c6003820440b0801907d07004581c0f8103810907004031000e02e025401c544a082401d0207850010141810f0400443d044104001c1d01e0b403100501c0079000b1600c94207100c2168a56180240d40d500e001054098183d880780b400d40050b007040101c5032030352071612000ca09954a2481c8581c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 908228525 1250 908227275 908227357
    0x903030203220b041418040503030103080d020d020c241003140703240510050904060b210d020111190f11060f0117060c0a050d06050411 60
    0xb0400c0e10190600c0c0c401d00080daa0070811000c0c40c1000910084540081d0010b0540c03040815111a8142c085c441e248041e8a008214114984140801b203403012007140d0550707400866650303031183da85134400c0280c46001c01c00d9411920004010310103060104103810329100000300d410b003c1401820b9160800c90644000031385c60b0200000300005400c6416200d601c0d4800340544010503500e8440c1619500001c00010b01c090007184c440ca0f0601c0c540c483d80d0303800300c1c07000c020741c1866040030041214104018402401140e440d6100702c01961001003580400803032410141400d058000070548070082c0078010800356080c0707502c0d1100862150152180324040745000c82c0000c3c0d034480c080f00d5109100c3e056000b4001d03800d030131300c00d40703003051002ca4801c81c0301c8003c00e14131754900501004204554200d01ca19500900300f44900150f00d0001c0301c000c06007610741903480f0304414810800070841c90384103550081c500b85844540340b5402015200d0210f818240558040c04240b0b441013280403442030507 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 908229775 1250 908228525 908228527
    0x2505101a040e191a0906040f0807050a0c03051c140a030504020a0b130518060a062718050903040602060a0c050c0f0a050d0e030715030e0714030c010903030203 70
    0x4091800d1941c482155a0400c2003110b03c20054072000d81d007108900c1034191044c0708490b0301e2441955121604641107520308008000c5458184c40d140c6950300c2540c0300801120f00011040300f0702c1001c1108507141d039002003070300c0800c0b0740d00c1c506603a81c0e141c180b409000c0c0f1404008030702142409001e52151060600140610302501a04110003d0500420813a13100d407009102060034482c00b07018110740d20340103502061080c104020031181e60400d40c1403400240d007000400c00540c650802810032200f69081034052107030900002c00c2042d102881e0109041c600c1d840005100d200c03000ca20344251070b2500100440d80704c0a4900361a8816409000c016a112030080703030002200e580043c482e03401508d04141801c80c614400750070030800c030094040d5030340103200310001e0203424070101444d4480340c02c24110f80b4091901003a103542c4c40384240b0601d0324440040c19035450003900b25151411340941981e1100d138840400e012480c10341d803a0140644114820003200754024107040342929090f400071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 908231025 1250 908229775 908229821
    0x100b0906190c0c0801140109021e0703030b0f0d1a06040e010c08012105120901020a02040f0203100509100b0f0c01021207020c030a0b060402031008010c050406031b09030f08250510 79
    0x14401960014140c4404440b0000b4ad03042486003071000790080e0b5201e6500464580307929020172071102044008148200000007020b000036045e500d00c204100c22001c1d000907140e0302c030b200080040600080c042c1c01d075402d02003d85e500950142c0118143c070381885041140d9460703c1c02109905100d010000c049900041010134500000d9001d030084c40d40501c1200c0e0142d40e194081000d5801c0110407030600b903000700038032111000a031202c10140c5402d44414003180380070742e10766103041c00318821084905000034260042c0e20f905400c6880e2448094007c0d0350360100700380c402110306001c0341c4500060117096501d805500e8042811401650404400f1019440e10400c00c4000e50014114450b40301c0c00703150001300100c0038012a102043d51307440d5180c55902e0001c0180c1078515920480040741d40ca0000521140e40083c08181500c0e001040741152211501e403017641ba12854400ba9030008a840140c03864668800c038515410340b2500c01e5130f403c44212005003065a40d25100d104030381071030281d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 908232275 1250 908231025 908231039
    0xf0902131d030f0919080712060c020f12180a081f05070804060c05071b06030b22270b1b0c06070e0a0e1003051203100b0906190c0c08011401 62
    0x240c44c003420381c24040031885513580141c07510301f542e280e22450284132808407001c1409868451011342032101d002130b11911841d40900d9403038603080703900840d010501044048901440380842c0416000c0606502441611622040d6031284c807164008208601003c3c00c0d0850b400c0c5025481c00385402c1e4072907406c07585541d134540c0701030440d1000c04400c000051001d4408190b400381041c524135402d000d6064403d050880041c15903004048a07406001815400d08030340c81c00c00c402d20950004044005000f08515000b05c60b071055203000d0900301c1080c403d0407000e0250069086005a10780552115800c2e40d02440d411035003c0e0500d07062658003c5400600050b00640c007070304600b98000c001c03150072902d0302207401500c60207403103820300c4050304034040c020404200900c41401855440250443c6030139504c0340c050018a000e840d401e00e102040115264880c81c06698025190340301096044500c00c03c0240700315000c3c4000e55080710a00d000203860ba03410b109041c5980140c02c1000c2e0399030708000d8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 908233525 1250 908232275 908232289
    0x3022a0c0f1e06031b0a0e0102070f0b071e050706170a1b0305063c01050f0f0a03020933090307050d0c051c03080106020c06030a0f0902131d030f09 65
    0xd5095a1002040260b500d26200c40100319030301c06622a04451f0014400091420b600d607049046038271912030060043d42680c20943d80e6070741d44010040c4902550b80c1114160620f00003000b4414410b860000c5282900401e4000c00c1c4804007581119543d9490207030301c26980800b8449411040180c0080c1d405840780d000541d20600180841c0c81d4604440c0d0500241320711a01c0398401004900b800124403401201400c0c0d00210920f803440c00c0075160300c0c640816101e014941a120b00002586003840c6000350141e0ba0450001820700080403009030b058622664450400e04540d5090501d031040c040c0090180c6404040140081825504120902914803c0d110303081d1131021081c0c00014590751200140e0b03000001e40c20000f821080c403494003509012040c0c100c1400e642064a5511144e03c4003c1030f6039014001c20408540141700a03288801428a1a40a50850b180a4000001c0c01994000c4c40c54a81e02c3c44000183c442d004407229105c0c051200122080603081044c841245400d039 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 908234775 1250 908233525 908233531
    0x20a1209050a020604090902043204331820012007030203150f0f0711120310090212012603071b081b0103022a0c0f1e0603 54
    0x4840b858041c580001c1d41a0b003003548029a0b01343c4400da940b085042c035009080103c035069501e2451010350031a0002d0110291100c0c0049131748480001c0c090054411959194251178411a40c0d0070484074240200c80e0f03031f0003112303041950a21501c000d482640c2400005415004042020346403039441e40c2d07040200c054260301741001219416042101115007486142011120050604900d548141070a01d60241d0350074501c83c0e5201c040180e003032015040d559008030701254030410b030707a24000d00703403071401c1b070600c0c200c645100c0c030410b030002c410200d40154010340100c0c02510360996a4003151082c0c0c844c0a114060319048840100300400e24001982c400d0711011601741c109102807611a865908118030503030b400d00f101c02e031078501e0a414950400140098070050100b80d500a0550084603500d003005504059001445c04100e03541c030f0803141151098903540c44445040503000c1d50341c0b54070b20728440340308803625420000d1030318011204c8021030612000b400342c1d010b00f100400600d50001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 908236025 1250 908234775 908234783
    0x2071a1932040f08011b091a0307050d18140304031e02010e030f070315020901050a0e2106040b07030b0d030e03033106020118140118150f020a1209 65
    0x10710002c201c400c49002c0e00006407a404c80005400b240703a138240088030007982135407401c1c045c44250900c100700c11901c0030740388800b1405110303590740c680d580100c3c0c103441219803000030344d0f142043e11021001000c240940c0c00d4000d00c800d50410804652042c1c1b00d12480c0300040032522041031050400045005c0212640d005040c0016050b01d00300c00700c0d09003480d03884003200e180c00c059418000c101400080118400e05c1c003c0c2142009007900c00604284a11403603402408034031221000746690380041c2030925101c0e0242e0000394042a241d240e41c2c5c0105407011101048040e002a031141d10130300c2042180c400082401070403030501d807010b84003103400e0700c100360b0103000030042c0411300509540a010b501a6030100311f580380c0c2800ca10302c6005040e03500030a00316410711640502201c1c41d50b900c268250340125001340340c081118910780c010301030314610f800074843d00c1d54150203000c841b2055052020b000c420a00408201525401c100d100c1e0101100200e83c0e500c80c85100c40b581944a0f5003844d01c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 908237275 1250 908236025 908236027
    0x70204090f020d03122003070318120e0f0d0203070302012303131e11041a040c0215010e070f050a030b0a030507091103040b0402090702071a1932 64
    0x6030b802250500c24440c0d800c1e004242c01490056402d5210700c1020041584004407071845406010407900ba480041e150000b01074842a6a022502c60444464034075684803141424180440001500440b000203010b849440039821071926803c00c4580e140500f68000c02401d2030390300310750054590301007200d40511740940d20300100c125000000011409480000c0301c0080d40403841c5071590b003241103074040890b03000080d599000003420300100d081104108640214018102c0410703865003010507600381d5489070030402d6400c4c2d03454005ca43c10360350b1464040b45984984c1c80d481c030300c6901582a21080001101200c003460711a12401c040d10070103280c5d1a012440c1c80ba00c00025810100e00c1e0404c2e181c03508400070810588000d0700c200c040054a0030300c0e080c250701e4103480380c0d81c58980040c030190050380c0c6000010000d602c01c0c0048000381000202152170f46105444030700c1039802c006007142210505101b00d4003214051440f02c1c480f00490703c0028484002c2c8000315045584d0b440c010450720740 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 908238525 1250 908237275 908237303
    0x30415020f06070c0c080d0f0f05460c020126040308180c01020307060e1609020d050105010908060a0b1c03020a0b0609060a090905030d110309101107020409 69
    0x300600005008800300d584001d000281400c01640c00b5241c4c1d40b105c646c2d0b6120300d04411610750080c243d0412400365041030341818100f07800075281031041e0200c2c00a00500c0c0c0d0004503040401e0009912801c0080e0080f82014070015000d80d007030340320695403134081084c1100c240300542c0300d880d20007000740d0380c96203c0200e0880407200064000c402c0d00e0840203d1044030030445010305144451071102d030f4203001414050b880e034002030340744c2c4590b01001d4152600c070150320100030b00030002c85444000e20541d502c9111350740c4544000940042001401583c00d0000000d00c5620484440341900e1102c005801c0303a84810410701c0040562140080d00000e10a2034004010403401c81040140d0082c2c001d02001c59244c5080c400c1414020849446440c15906005139a02c0d40748070501918600c8000041c18181800c2c654654041c140403446d1490030703c140d401c040251030000c0c6000341d201508460020802090280c151020108a14400074040c007842000d460b01c0e4100c0f4558501500d01d00030450 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 908239775 1250 908238525 908238553
    0xd0e0105070c0236040303050403030c2303041406010611070f05090c0304060905061f0e0903030408030405010f1e0c030501050f06070303060b0c010e0f150403080a021c0b19050303041502 82
    0x1144c02c5038180c0c00b01e40d0b00c00802c003e150f01070040290450451910000090788010301e00811a640a1b168012107004000603041241c0031560314150700c54241128020f603550b00c401411900c503940081f1050082c9e8800049080c1c0304410311040d540010b01828069032190960070580e0402041070f1042a12074000c000440c80a10903140140a03c5c40c1074010600076401e800a54000c50340f1040c82000481c0401c49480c501105503500203510051f510794a07152400c1c11340c0074000c0c1804d1400d240d49413101d8020311400300300316805000d04a09050002c0fa41c0304105030100e540900c902c0c1c0e003000034600020410f1500c10000c082d064802c1c00c00145c0b2989410400e540d64001ca10500f074070ba95683d8110500c40410480c034480c000c0500700070002d28520800c10b142940d40904001e0a101c1407502054108a03141c05603a1000d0001184d401d00c1150801c4840140c0350450a040c010034408240e008c21403049800d400c2901c80c00741c0150300e002e14200303ca0220401180c8542c007140504940a2481 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 908241025 1250 908239775 908239879
    0x4060504181d1e06010b0304021507050708100e160603180602034204022b051906030302030f07081201141f020c0f150d0e0105070c02 59
    0x30900c1100074083e10005021078112070100405008156104000400c00340d070742501101da00a50680c1c1d1418050009081000c444c056004001c109010300c2101180c85080003903c0b2503150451001403009820400342d4603181c9072032002c81e518450400d1381c1400040c0c002c1c4c1000d2480080081003c15241b000e443d0b000480e04290790a1020b0941a8641c1050907001689002c1a030201e0741c03c3e0101e2419030f0b05000007102d03c0c0181d14056038010503542e000b0100134407070081411300c0344600760100700004d1500b0000d042c00c480c03040c0b191100c0c084010035030126220b090141c951580040d0306c0d202c0300340241d0483c1c4d044490200e4090100b00501c40c21080c000059a0080c4101c08001c102d101811080000f2880800c0b600b6000185140c84013400a9002802e14110141510f80600b4000440d01090340d000c10140c100403079500010303150080c0451580280001c3d1000c2c002007046071110141110380d140007a102070f5003d5192850442107042c658031500350701812030040c0e003000c81d88040440074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 908242275 1250 908241025 908241071
    0x1b01020304170f0706030b090403080c0904050705120108120703030e0c060c100606030902010e09181f0605060703050717090307090504031d1336030908030406050418 73
    0x40c6400038100c0c40f1195804120710303400303001c041c28107115011100d004280b0131007008002408114054002c41c00070001c8404030f0b2040038014209200501e4601409031003680708000d038200d0801c0400000a802c5000710301042554403000340c02d491301e11aa10100e001e441060381d41159400b400400c0080e503a0341d08000c1c07096980c0e46002e000907070340d1407000b0000c54500354800300c1407500703090b000740c0182c0c0e20080342e03d450501192024000c0d00c48030300c6581e5190348450110490301c55140201d91220301c0040380c21780f4144541e03013880b04035200d02c103104484c0104032000b00480d400340303e101e00090044180c6404140201d907141e0401e5040d500003480c00d011070b40800b000300e0352401400141540010b14401414a0320000d102090412011403481d041a20342041000c1d59601010703140681c0c4d40800c07580c24883d08221a191400c6142e4150441d0700078001c41c0400c40d40c1a00007040c0310044103540441307419440ea50f04251900c1c590340c1c13511488070440510b807035580844d224160302c84181040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 908243525 1250 908242275 908242319
    0xb040c0f120c09050d050c0d032f12070f08041e06031a090a060306060803030a29010e0109051e011b0f060b01140a021015081b01020304 60
    0x42550055020302408003071415480c22034208000142c05942119400d02140d030295410191640903091282c10070004407541d90380b20410395505400e241d880042c1020b12407855581c1c0e401954960b43c1c41c038039080780c0c000741002504803424890701c0202100241142d14080c03d1003a40144103907407000c030070354010740040a600c9007403078140548103000003e40700581550b080402c03583c1841d0280320014824403507028400d001410020b88a000b40d40c100000440e805202480303444d0300c074101c030354890304201c481012449c600700e01100034200302d000501214214110100112140c43c1c011034201d4100e00e012814410280740004079900d032610340340f14103007561888143c183d4451000410743ca524a100c074508500705080c40c03001c10340c0007802801c0c0030350103080026907040f0a401a640d20b000f1100c007810b59080405c1e407086003a004501c602400400c91800c00c2025940c01000076240982d00441000e680025202162030b03104e0064039217003031070500403682040c0d40c84c5221032221600c1c4182c42 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 908244775 1250 908243525 908243537
    0x904030809070e19090606080f0c040e071805040816050d3e0a080408030c100218042a210606141606090b1e07120e010b040c 55
    0x3950000b80100d10242c54043c0d40c02055050404081d200e010024419600d0070380d0761504001040866400300d0014403a500580d4000ca0141080d66112682540700314040d40c10090044123003a00440c401e01900c48000043d00340351501140100100f00081080f5041c11003044021110006840c0141079507201700c004110703800e10400006c0094240f840801002c01030401029041400d00741800030a024405a4600342794134090210700e420070107a00a06044d02c0020b021440d01c0c800700042404840045c1101d04e04160524804201d2103041402c24206540306440140762600303030010300c0c0712070181c40c00306440301c4000480300010803030030202c00c0800c03c807058842001145150409110b007a030716041010328500a0058580e082c4401c1c1988440700000c0e4035601040b803010140e09480d003140041100058903d0301049480080c1c1d816a000302000c00d0300094122100d11007880b500c1c10ba03466140d46c01e0700d5500000030340321019845809540319003408403d501c0703500c50309003240070a54400f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 908246025 1250 908244775 908244781
    0xc06020d0e0d0c02030d181a041a0c0706030221150102010e031317160e07091e050f1503151807020a0f1403030a050604060605070f020d1109040308 65
    0x100303280408210424043c444590b5500c000750790040b80302c810000b2182004400841800c00030b0343c0c0703800180c125402c110003c0061880c0240390030702400c10f132061124814078a12942040403003a000d44500e48207190f100761300c06d0144a01c650040d1100b000d94118100d011008500e0b0300c08600000c076003400c2c2c8032401c00d826840943c1d09008910341070542d07201942c0f80c0500da01c551100c19205010720401c81c40d401004080314070701005a40c0342c040481041d10382d1070f901c80d403000c60200410f5034510002000901c0110722000b102c81c555031500701121140390303403610780014400c0110500f20101e44c480b404910211040314500c3c002d510641c1940014180f076584c007020400c03080d401d13054944ca492005010440055000030b11031840a41040514400ca080c130f1428900b8030030141d8290056010200a020190885800060082000301d50a0041c40d455030000c88080c09000005040110a8040c90000d400c124000849103800703000c0000f595074000700403070503000090303e013100050701e51410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 908247275 1250 908246025 908246051
    0x73618210e01051614030a0504091a030a1202010b0604090e010c03050402030703062706090c060819050414010203040b01030b060402070b270111071a0f160c06020d 72
    0x1150191003200e0520101c1142214002405405512039800c1d05926001e81e8000b8801c41c452803c1004060344100c95449416090040c40b9030030a00c1214040d50a05002030362030b51081588038a118070103402040c3d15200707031703c1b201c1100d10002414400d5559518031b41c155030301c2e00c0000f440500407548010901060002c4481d08644a0094010400d0728000034000140c1d404200c500c1102e401200118401201a01040b4902c0c008808a5404452540e41f0300810446400165034180035a8000900c1941c80d01c2c1590251400c4074454041e181828645210b03ca49900c00c0c0d4101c2c1c010380c407040c003002001c1c000341c0c2203034016a404e03510300b074442c2d004204020380074102a40c824800d48095003000944d64584000c004080e03d800b101103a940b841c490034042e01c5032000d5a0812100c028400800418015803d60788059801c0c0c0f46441100c0303640c55070f20800a00580a401440a040340982d01c07046800d01d45102100c0d07620420000903c02000305202d030010308442961070030300188003214004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 908248525 1250 908247275 908247323
    0x6020318030a050a032a0c090b090c2712030c10020406090308180306010e160203031b03060d0c090f18030f0e0612090c03073618 57
    0x84541e109620160110740091008211200002d501d030602c000811203200e81c001c110406100594030140103404180b05101c052603014007100c6019504200100d03105007400942d003021682c1e003260043c00c110307255189001c6d2640c8103030100b420280380d805490000009662448150804001e640041004070384140b080c003244580310b2060380110305c2c003883e10324041c01c00d5a82b407202415243c00440c0e20602100410318130a054000101a10625038660702440000442980c0d03600e032850112844050b00f5000000320f07070081030804500e410b0007581280024081c0d00040407580c02c02144001c039030018441c81d011a0107000d46100c00309d035006182070290100c601c01307461714210144c0c0100d03210200b5000120003c03c02c4151501c08076103452240030807018031548491300720b07143c0c956007042480c07440131513050441401107042e100001c0e62043c1b21080e0141400072009103803c0070300446024a904030840000c8191541d0205064081201c0130400c00107104082d5840c40d24640e07101d02c52000c1103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 908249775 1250 908248525 908248567
    0x603100911122a0a0504180b100308071205070209040c05030606041a150c030a0306090e011104060806210a0c0608070207180212010b07060b030613030c060b0901060203 74
    0xb500038a80552401d01e034109030541c1420203400803c803007a1203442c6468004d500801350102900a218036204201850078140004e5400c0c0e440560802c00305015040d202001000c60fa0001544c070b0410445803039460090b401040303082d0038003604125110058940d2401c0300e100301d0080651074509483c0c101814100400205031900c20361809442102c140400c2c02c8051700e140043d01c01e92600038407201c07907242610842e00043d42c82e22001c81c400300895890b8000409640200e40148240203c0240710f0f0b0a981c0045d50321074086c2070030b00044c00350303a01c41c450b1154040c1d001061114034080118080440d69503090076a00241c10032044a014465101c03103100050402d4a401c02c024a004a0025120001400307581c1107040044295142d909042d01074400c662854500c000041d43d4a00e6810a01d0b44910001c0303500790700b00259440b05140c08910144100c0065150b07081450380ca130350403181c030b85105404503480b41d5685800d001e682c4907042801d020708156002159070320500010160400550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 908251025 1250 908249775 908249809
    0x80a05070510080f060307030221010b040b0907050d0908040306020c1606020601060e030a080307021e0109050613060e0a050c01021b061e04210210030507170603100911 74
    0xb0400b0300041d42c00500d0302d6000e241c1900030783c0315844440001e030801485604c003951200c0e00c0c6514030034030900481d54540d00601d41c0001c1040100391414001600c2625009950200b00a0009007c0b98043c000400348850403900002e064913065231803000b030380c22580091b10065400b107813040001b1002c201c4c0304034609401d48000314452424200958640781409007104100d414102d0714226142001101c04095011880940302d10f89120020350b02d09000000f1940788c0b00306075029000310707010300c12079a0107504a009003125655240000f00c10a600780f004450305c580d035000700d007043c031828003220017a0b5125034081e002441c0500300083c9000f8429240c00701c000307140725101485540f008102c07064603000c405d070580c1806d409010307400f1078003860740246d4a200ba900c0484144011465840c41258400c680c002c0c1d8200c10580210112041122114041402c11400f04030902c11948045d9201d00014100c032181710a1110007000c0e500300c2ca004540b05144e000749226075142103e1030751085010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 908252275 1250 908251025 908251039
    0x2040f0e151011010504050a05070608090c0918151b04061704020103020910050408060c03070507030c020a150306090c031e0e070302150705010b12030a050c16080a050705 75
    0x100c0702103400c440101d000c286110701c40000e001c0100340d0165488840c1018a54020007440ca402d040c1240c9507011404100c855001d003100100720746008030781880c01915684010410b8580441c2403145552015004c12880031907003070700c00d000290403c401580d040c4a0081c4016500703001000e801284403101040c3c003440030a00041c018194000444170300000000c40629070b5403503d0005070001c3c803c9121054001d0003074040b41071095000001401140c07105012205541d60303008508603a030000380c0d2900001042045403902003881002e0300459103000500c03c1d004030391344c0c880c061860407000401e0004203840e00b408000c403606901c01c08000c402607080c18000e003034490301d0349011015821959407900c0e0303407100c50090844080042001445d8050000d207038001c0640b8182d46250840e8078211119820100c04807424100b03206500044081c0740d00560030000401019940c40c2c0103d011188a441741400301c0003802c8010b408140244800406000300c818181031050030028550805400713043d0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 908253525 1250 908252275 908252281
    0x50c120c0f010302030415110a0f03020a0c1103010e06091014060108010e0c09030d08041214030c070501140c0405090c040b180402091809010c02190303020a020709060902040f0e 78
    0x754094801d911040929005a0b80e40e03e51811043c0140904102250325107401d411000100030035000700b0f08002940c8500e410f80c6aa4131046040e40300e02221400010014146034000501038545140d0b4048020008505140c134088070520781042150b01506ca80d01c403480e1060058900d205100bc0100202c2c1c90021a151842c0043d260201c18818070108101c01d600040920101c5415205280c4006069440741c1b18081d200401510083c1e03001d0b10941ca6180e000902c0340d0041c2103110350030000d0000c00e4207650383d220f035525454101c08416200c654a0351000100410f40041d0700c0e220388100c1480c42c1e122401c200502050b040b004001d105060403c100500c0300d464800b05840c12850042c01c00f141c0d0700a0b40c804a0068007405640036000340c3d00c540c1138403110f804480b4291199288a0080040c44d8030510b0403a5203040c04441c1350480ba181052044c00b01f4401c1e00140f8680c1d00c0d0b401190a110745e9a00f0541c112030782a031180040d16070105041c01316940f010a0400186481100c00ba80c9003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 908254775 1250 908253525 908253529
    0x409210e0a080a230a060204060f091403100c0c050a0503030906010b0414060708040b28140f0a03060e040303240308090904020f0a0308090319030206010603090f0b0103050c120c 78
    0x700c4c504252481e4292010a0804042410008040c5965103e18199203460f070351007029029091036905000868000e840c00f00d5103180314954905c000d10010000c008680d100350864000740b600940c10341c10008040414070100300100865001a8031841c0207541e00e00e000204682031050607004840803231004c02040100607416074500754294000c54881c0c1d56041245400006407040790322038121014085003a005072048078440040e100c50030018a00c1545203114121041c41058449048460b801d1010603a4010107201408020b0340b182070002c0c20640340d010307120090000f102c1c1100000c2d00c41ca110185403030580d805854030780340c0500044a031800c5075145006030066804450003154990001400d542d80e07488101040319028221801554590030007482035400008098041d1140c1054800c1a400c10000306030384a4140c3e01a0403642d00705042100a44001079098a950345014120000700398203031800c900031440741d8020201c10700a4000d1100b40c02c00103820ba6401d4200c13000241c219 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 908256025 1250 908254775 908254793
    0xe030c24030604090605190b0603010510030203090c03030423100e0607210e01090e06060f0c0a05120403060b1807140c0106032d02030c0409210e0a080a 67
    0x20341200300d2120349030354030040450000c004c0a08040c0c0b403981010203200181c1c4000415050560f100c0c0d6041c0714180f1440c040c01801d110030300c14503070400074003050040010312039809141c10a07030490594000046a200007842c5801c40d81102d541d5210022002d0480e1301c2d85001940280c070155140c008a858500c409805001d800c1e107640c2c09640f00003400420803c4a42a0303c4203210760f400d500700e03031214242000f0504030540901502280c6403c8010910b8880d03400c12500c40c000040c0601d1034038191146c000440d400c80480d60141d84079184465001441c24060b00c2c00d08551451810785451a60400070140e40d80e603032105004204c1002c01c03e9080f4074281310303141d1100741820300700441c40c82466008421b00c10003110360040d510b00240841080711301120300e4418149022010000d15100c0700c1100e10001c11384c402549030344120154021810150801040309000c0d203400b2148516507480c1070204003d1090900c0024030003840241e642c80c0401d00000034014140050948448554030000340d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 908257275 1250 908256025 908256079
    0x18060307020d1121031504240f1202100c0605011202090f0615300103060e030301080a1707021c050709110904050c36040c0804110609100e030c 63
    0x3081340000081c882d000c80d1001d1003000707a0080d00821000d1400100320001d0b0f0a0550303a26003241c07040780002180710251500b03501399101080300801042e201d030b08101803010f0200c03806051004249400c0c01245040c400d0314020104640300c180038200a204105400800a140340f2a1501750401d10450b5210440d07903c00548508410680d03d40c521010308440d8021188500c0700405540c0d41d82e03d005401c415043d048a1213110b09001460000c80d1050300c0707010174000c201d41d80e4403d00505d404201e0242403038420440302e03030302186404969008100020300e4103258014903840c000000040003401c10185000781000c0b00d040004184100402c80144140451203208503250408603080c856000b044840c501003020011000000301125064610590303040301401d081c040d940700c003090605000d0000048a503566049840c1d881d56108900d200b1710010389034000c03100344089810340c1c0740c3c1c0d00c0460b00142d154540170782d07402d1403008243c900810b260001b80164600b646805140c401041c2c0040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 908258525 1250 908257275 908257333
    0x1409030307031e02210105040b0d03121401080309100201050613321e01030804090c0e041d0105130c0b07050c09071e03050403050f18060307020d11 65
    0x14038840070481106941070041c9014000381c4c8000760301001c1800d42c1161211280c4496081c0b515aa46c0310208011600d40c900d44070b400ca2100d104a81c0000e01c200003400d60030200000c0064200c4540d5404102c0301000d8001500c81c0c0d00004000d040d030306d040b078110341241c103144c8001d20062510101248002801c2c40f10418031036190361a00c0500426034445034810700c1583c0500d03442d1200756502e2514007500765401006040482c11034584500000c8030b0030f040c1c03600078840030315251510310030100400b03000d50182d080020b1044000c41c9640e8501a080510300c0d044103040c01c8034604000c0d0790842d21301401c0304000070190280b942c0003603640a001c20850b60610a0561078450a0801ea401e0070700c0c0c0f44056070300031403580401a0b240c0d0480000c0a0444080703034032600c48000d00c0340c140e04440d001d9401a020403070601001c4042c2d03403ca0700804100c1240c2c51515000402140801e4043e0000d484c0080560000600e210800764400131380003011000c50000c0c050f0090a10904415100c18500c40c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 908259775 1250 908258525 908258531
    0x10f0c0f0e010912030305011a0a1d0102010b03101d010b0a06030504051005040602190f1d01141b01180c0e070c0807030801060f0f090b0a020f07090b0301140903030703 74
    0x401c00d40c0c0503080407002020314428501e0302c0165882d00070000c000c240a44800030282801c000d140601420540d0520704082d183c4074840c4940800710035181a4005555045649840806001e0b460500c4540ca010707403a00b1011039602d0359400b0602c000701d62074003c104268949850341c001d070365840401104452250600058540341ca00b062820004000c602c10006803c0c64188000c0040c60f500a240000005410440d014981002103030f10400c41110300c40029583c45400c041c20807000c014101d5a5014100030621041b456010b040f680c01c410083d98002d14420700403035841c1805c1c002c00f03200d0b0b0440c0512a03d0760886560701c1009600c140154000d2000e64000982d1a034010034400d440c55070031400c090303265006c601d00201010024041c00e80025075080030b070801d41d40038202c158103601d01601c03a192101d091114080d419000300c6011421846103003000b40e926070052107618080d18007880080342e40e0a28105241c20341e13080300700d504a811346640411614482c04801d0f00e0308004c4600d004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 908261025 1250 908259775 908259797
    0xa060509010e100c0509090c070c1401081801020427050c030103021509010201150e0a1a03030717210f070215070e0307180f050903030603250f1205010f0c0f 69
    0x440701e5015440040c0c2d041f42c0200140314007080304a003d010110310806810020503181c220400a01d10312041c62404142c0450211710800c1401d00424500d820a0000600302592120032195601c500142d15171a06610410640c0054660040f240d0080d1090345507851540340d98013003601c00104070244900f42c1030106400c0b0141c4c1c400e4000e400380740d100c1041d2000c095141c4042c115840016604a5032803031815003001d1408402100740e0110305030041c042c50074820a51031320100600324882c04030001b503081000503c20b1150301c580703a00710041c00704100702601c1e25034242514500040c1624040d58046443e1031354161b400310030f2a5016000b0314011900300c0340000402e01c1c00c4001e030031078100140911209207440e07072113a10060b4810160380301849561940301d50340e9100e110039920079415400c1800392000400c4041185054000c000c480c440406030703201e007011245a203d800c56020401d10b050107a0511800740248950501c1c00101080405031300380000e80440240103400c020300c9000041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 908262275 1250 908261025 908261027
    0x10806011a130e07031e090203190c0b0403050d0f0509030c012703050f100605031908070f0302150604050708011404061a04050a0b040303020d05070212030a020a060509010e100c 78
    0x20910003420381c3c070902c0c000d0342440d14019000d0803000b0480a01c6010000c10040c100c40d25008080c82030307402401030540d058521204510100111006580204060070000741011000006000a5000c0c4001c0c01041e598941d0041c8800000c0c10f0350340c2003240c02d10140c45942d4020421018a0740c003400d20012090130a44100c2e80400e40c2c1607050380310303044000b000082c0280030078500b40300b4241905803010160340c0300340368045400c28058990580c3c004140c0740114414031284114003400343c00c5290414541d40da410340501e072042c800710010f8110540e190340d00c2c0f0030041030356013000e0100e805215603d09120020030744031052040382c154203001047c00b80d6503251540600c020700201c00000901c3d206900390515070f6840340c40707418011600000c00142001c468801e50f401d90307038107601409580341e034590212156000b6070402d03a44998410b2554030150000c00080c1261241500a0008640070381400000c680006006160507410b10034401141400880d00c00305c0390411244c00546a417a03207030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 908263525 1250 908262275 908262307
    0xf120603031c0b0f040e0703020f060406080109020307031b0306030b060d0b1306020d090f0209010b041a03190608010b0f09070f030e0c030118051b0604060c0512160209010806011a 79
    0x119145c1080c0b4104060a5030752010070074200781c90090311034541d040c6004040c010144a140b2804001500580050040045907001550451518900800c140c0d815104a2010b04016030301c640210740e0702e03081081040044d41c0100d504c000f080328441ca102c40161120031004c030300103000c400807105006400c01080344ca513060301c1070180180d0080100709603a00d41840341004007001688a0907180340000340100030360084400392050213140c0001003078082c010080607000604180545e0300c4030b15601c41c5c4801c061042800502d20704002050b440515000d020305001c860440e28058041501086840c50f01701321001c07401c00d258500010ba84000318905401d0030550300f000f560650900c024a8110410211150030301e901880503180d0060b40030742401e152080402e04150000400d100801601c1d0059600b00d0101d03009505580c4030b40c0c2606e03a40074491f4021108411551f00521981d015800c0c840d0304240500307000e00003000d880d41000e003480c541d0000c4203034010300404001511a0020410790f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 908264775 1250 908263525 908263549
    0x50702011115090a050609011512030e04020d0515010e1c1a070c141b011407061e1104080c210312150f0d060c03060b0f120603031c0b 59
    0x40350302c020b54144124219150003010702d00f0340d500d10402012441c041030600c1040d018503c02c448005120b46040408000d40c20000030035007e001880c800d01042c0e1b141c41c001000d1400c000c00e00000c051400840d14005d0003030b5000f00c60304124011407186030303548501001f080901003004202084003c1840c120486507026014440c5c40d8001c0c03010b0000241d0042541c4807501c0c425203480c010005004061580d44d24580c5c0180311041820f101410194010200c040c1285040303172259242601c5034a840c0180c0d15900511103103035803214030300d107100c041070311a50010088010b10f01e403400703181c04030710350f82c90600c8285544114804480d480e0006080030190074014071800a4035121000301a9500100c03008413409803000b0561580314009241901c132214480c10014183d881014598036020010250107142c0001e05548510104515600401070b00040040c020b0103907803032842841c03034421080b01800c041e01036403040c00a0090144442c6181c2c3c182100b1040c0020b01500040c00103000c8510a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 908266025 1250 908264775 908264803
    0xa0f050d0f11030a060b18090c070b09070614070b0105040e01150312030f0212040b0711070b0301150806010507111f0c0b0c04060c060b03150108101401060507020111 73
    0x30001c0c111000d4a4800514421032848408010180c3c0d07821380c5601b140701d40744007000d20031049040d03802c842c44c1c0f0488040d0000011580380742003920307694032050500e000351807845043d0b0200e0340400c1119441100c0350181c10340c6006260909501d82c0c2d03092444401800354038822034030340e00b10f992500d6096000b03c1d20340d08035580541410350b513803e0140c03d0030030809a0000090804000c010222418000c82d1a02445030101c000316944644070110f01880244c05e68040010020041c401c01c030040100c0d002400801c07030603a40d41d51400c1440851003040449031000c0c03180d031004001280ea00a01034070300d00c3d9009a424540c0b504803c001a045031294900036541440882010381115888000c01140701d10980070742d8096114110046481d026030700c07443c00003a442d4000070340022007a170032a078902000a070488088640c032420224881c2c000360003403a40c6912051150b011016580103100c0600000c00850b00554140311004259228200c40a414040011042a541541002118551000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 908267275 1250 908266025 908266031
    0x30f010903080f070903150903030603080c0f100507081801150e07031410090209041401151e02031902100e01061d10030210021e030a140a0f050d0f 65
    0x51854040e00451003514901c62843c40140002c042500500f42502601e8100503810301c010700c81e02103000030b46030319101102019107c500000000d24546d02915815000700c0c064400041c1c00009248ad0003c24800a1041814035041c0064660419445900301c03c040c800c484e94003044522060160a40e514808007a00b11035a000402c2240c0c2441030780107100c1d559007446000230701e124903050303024292404400d210365641c0802c05400c41d5030081c1031030b94018002041d0243c82c03807996801da090990054500c450a14280c443d43c03507110300e40b88401303000d10381c9110742c050030054025945d002d101c0600117164400c00b48900340307600810981c15881c6d80c002c1c0a000805001c102030740600036921540c450040e50080c4100140d98502001e0f11511040e00c036611114615020043e410040401d103806501030740003038135650155446060701090100c1c004650360101084014083e44612002e0100c1440a1190002659101d888041e4075182454520f4540324100c0000c0000e100c07035001013a4481c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 908268525 1250 908267275 908267291
    0x10f11071401081e0c0306010c0803010b1e040303080105060a20100c03020405220209030312091216020904030311070507031b0b2d04180f1802040b030f01 68
    0x10500000d00000c0310282d8031600503449900c1112403084541c40144c0264010400082420300804060369200304145425a05d4030b03215282d406050380300b80c0005e4050500042e41c0301803042050710602e4041404c401041c581031454800030300c052018084c0921615002618444240c0300e071040c00340200060030034001400a040b00c540d6503919010040d11800c2c101010303030114034028400e441c100c802c0948440910702c0700721511810741001c502c0070782c46c1c1c80d42406480e295440c02c202402051490062440307150804914040c600300120055116800040180440d50403135030030700e088040d90564218086803120318080c1c01a024820017941003040104458041c041c00160301800c0300d010fa1098141c40b50104440d4000b01181d015a18807444200420b0260001d02e048420742c40716040d50100310460040181541503105034016408200b501301c011580045610805500700300e207030400c00140700c000b5107050706005c5d1100e0203441141c0d50402c80daa642c40a00811807601c016800803c001c034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 908269775 1250 908268525 908268539
    0x909030225060c080904092102010b040204061407050a06110c0712080a051317010b011214070819050c0909130b011a070803040308010f0608010f1719031e0c0c0302010f1107 76
    0xb0b5503900d08c44010b600b048902c040b40c1c1424070032901070342e44903030710b420011124420301c050651041034110b41900c9082c80020118509108640940645000c5641e60b40890b1405a00d403000e01d801030040b00c20b4a515400000300081d00301c1c0c088000300d05081d511048500700c1005036420650119241c074112192401ca200b4066100b0340d1240001d07215055000319419212040b01d044590154402d141640490308840c081e000c95580041c0c0c0ca505614111001030004e010340301c06039540443e0720804241c9110516250300181e500001104580702000700d140c4030701c010314006101c0e00e001e0341c400f010540070440000c02124680782e0080c0c020b655a05003850010007400c2d017441062a07118a092001c01c60320320582070941207856200566814505100b411507031244140c0d03824a4a2151030120025041d01c9a99128070034001d80740e1162640081d0f4903600c40140907600d4504014078000c031400000d240e400e8040a507030b020f20380203007440303d584801d54008450f09600b00051203080c0c0300241d45 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 908271025 1250 908269775 908269823
    0x412020301151e0f0b0904110d09051c0315140102070801051f06050307020d0e0f030a12080a0c02070b0c010b090109021804020c0a03180909030225060c08090409 71
    0x10a103d446100b0010303074568034100441000d0050004401d0b0820045c07400c0d1500743c1000b11000c48100c407851812401c2000c180407200074840c2101c15030044103004000d81444409100901001e04051081e010148046041410903001d800c8c0302403584075402c145a4400c002c0c40780580060b0000f000141400b190060000380c01051519401d0304a82c00030400c03500c034500b40d038050079142d00248080c22881c0e0003030700c903081482000c980000303115202d1202c40e5010008400d40c40e000e400783d0300f0700d483e25000c010b00c003520050000c0800703400c04c44526001a0b000542500701d42c80400302540b601c1c40c0e8031815014240082103640d00c40207080011900c1181c690042010324801403148040204950a0106a0042810709012500b00040e40004680140200b840d062628030708445a59240c0030300c6001ca880711401075005900544d074075070001012040034604d080303041e50098105450b00100400c41150b4280052801101041c00c1c1107945481c2c106d9855039510207074044042c5911040c0c0d07494 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 908272275 1250 908271025 908271059
    0x50d02040b070204060609030b15060d05040b0907090509030403031d042903070b0412030c060509160b0c032b1406010e090603030a0c2414010605030903041202030115 73
    0x412480c01c0d80000d46d85004298100480e40c0c030036200c011aa81d020146818180000720f03080c2c1064080240268848043c42454851441103e503841c3c1400c8c54458645001640d0f00311a25051a103418056500c80c00007d8604481d81031800034640c800e41d081c02040701c41d45240047c1c111f81444d03070003489044403088803441c1c8403000b0315003002804440c0c01c1654422503803060001c41c640c100b10a000d40c54014410710181030103030414185d00700c001d56661003101c00440c1c1c80281c42e00880004420050080801e034018085078a03000d0a00c0115554540c41e03100d020940903400829403d41c940d104500c448441000842e42020811484040903510b62200100c46103070020350711404040b21480d00c500d010740036001c0640118100b40e9080002e440d407144945003541e80081d8540c891a16044020000a13203101c42c1801060354600d00006c104030407030682100302440420310400c80c0040c0d000007a5411920302401c0d01107103541c0d600100c2d0040c60321840d081c3d082c4000302c40c04100000d5912080d08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 908273381 1106 908272275 908272279
    0x509150303210121080a08130c0815090d09060f02031309060e0618040611040302060304052a09041101050c0304090c02060a06061e050d02040b0702 65
    0x20201200e150b100500701c003100062000c1d00004111200380c00614104080c00503c96440c2c074081d000c4c46c81c41034200f182c42000100c5419001080029454111024440841d220a129511501c030314a44461940c0c01c13a002c10b0f00c3d0400020403400d280010750b80c0b442142c1c18140f0844455144240c0c2d28114482400400e6040b1641c60400000300003502c00080e07528980126903480000007050a4411045515900d031b80c0300d208001c590b845035000e1400140042168a8251940070701d410194004101104110410500042035114070014501180f07501d20040c0d121510160381594440d001649007012400052044140d0005840b05050050820080b03280545c0307540c103d98413070f8540c00d8403074484100d800e40601056400854000d0b042c0803603410084040c10555a2004060301c2c1c00d443c103145400b0b1840303141900d04140324081c0541d9a41da139072800d401550001d4106078 = true := by decide +kernel

theorem cover : BRFrame.Cov 908093525 908273381 := by
  have h0 := BRFrame.cov_init 908093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 908093525 ≤ n) (h2 : n < 908273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
