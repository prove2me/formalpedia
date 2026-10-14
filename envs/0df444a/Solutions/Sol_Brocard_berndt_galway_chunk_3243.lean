-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3243
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:05:14.027043+00:00
-- url     : https://prove2.me/submissions/774537b8-2cce-45f0-96a9-a3cb3dc3f8d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 583093525 ≤ n < 583273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 583094775 1250 583093525 583093531
    0x61e0a270608130f1202010507020714060f1606050c030103020a09020a0f1107080109110108061918020c03030f011716180204080d02010b150405091902042102031005 73
    0x680da0580075610b5624000702c0c1c03e109002142c0780c00e039180622022402d508601003241c0510350000c00c82c1d082c120b400a10f40442034208088d40e10003000c040056030350b1101203a030700d408804c40d0300351105140400492000607829014010f0313030a020402c85d01840c14030080d41a2032084444410140d1100110701c200e001d620018001700d0705040c9400055801841071200d01d6540208858109403110569400c4d56000e420485a001a1040340200c541e0011500f40d030048083d640c980050910a40002c2c000d02280b056040000044000340c00004064046502842d1110200d9030b40f13090000b05044911030900c900418000c10340345085000380007240706640304580c1e040e07114142d802c1081c0035208801c0300f030202c00003641c00c210018002e2014080c0d03845851071500000383c144000000d0004134045204c0440d010f4004100a200555030219802e402404800c1e0007405055040070f100300900c070301d070040c0041055800445869807004181c100324640f0075005c1c2c070300307003100b44c01c005e0142c036030503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 583096025 1250 583094775 583094777
    0xf090207020109061d040b120a0309090b01140307110c0d0f02030601090b030a03120906050106090303080928060605060c0307110a0305030a0f0215070504050405100f05061e0a2706 79
    0x28080444514054126687c0e0076002005031602d96451498140303408240f08044010030b602c0744040107100d40d6481819818202070030003d00600e80115815031900c802082a02440200e00d03004120480c02c0200070b82113080500720b208013001c10f042904040248a2040348644108000401d1046440c081c01068040c05001021b031104c3c2907902350707071028400b400c20340807503990b051a0011581c240580ea001b040d140c3c90f9100002d00318203005000003001054944640d200c1c400f010360030900900504119490f000341140d400ad46860040007915466004c0f903480350010031040d016910100080c8038091194003000058005001403042c0c07a600740c40007a0054005100000a240c0900c2801903400142d1060f640751102c100c8802d0020001035a005000500100d0184000d0403c5d20620742c0004035510100080d82c41c001c10624403d001d402450300405010904c81940c8000140000d080000345401a407181d0110a00410900c40c5088500c440100a054003021000041c2541e040d81c0305 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 583097275 1250 583096025 583096067
    0x215070615081b191203080f090d0e010509090106021e160303030b01050c01060b0405040c0201021e0f0d050f061008040b040609023601091104030b040c0f09020702010906 75
    0x480012500e0786032003e4400e5404c40b000801030385240c03441443c1c1a02901a0514100811415081c0280818001080441d8101c11f903020700c007020310001038401c01e910b0f8a10b06002c0490945004075514029198107a07000a01c0034004911a5000f2a1040c00540d100d000a5051280100006c1d69000c121580da000c00c0000341040c40440e100e40c00c034410103041810554580071010106d113003180d0980d40400901c410108040c0401d14050080b0b03540448a44000e5003080c8074660302c2c0000760540005a5090ba000059401300b140340d0000b950500b20107010300b00b00b41d240113010342d80e40c10000c449152043c1c6c401000032480900034801310380195042441c4d014141d03190b68443e402170105982c2640c1c441700d1000103800e8001041c0c040303c025614800ba455040e010500d203888003407410b0b00200c82c8103060040941200d220f00042c1d40c101c80d00986502c03101d44660414900c0d03500c9507041109407149150b004100543e00707800810110f80b0030707038800c102c141c0d444070f0803035180310044124010145 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 583098525 1250 583097275 583097293
    0x309090219020f0d050f0c01060f12060b04021c091106180f0d1703040602070b13030815030a0b0402040e070b190203131e0503060118050c0c030712020a021507061508 73
    0x1a81b50040c15641c1d002c00000600380b51075070241145400c044e40b2112915003916040010448640030700300c1030354401e5a080d42082d018880e031400d02003100c8400074100381c4c0c40f540071003400102e80c507000445002038000d0313030340e001d070b03c00c030305601c1123211080b240550942d40303a40070181800d109801055400541036012411420b1018145520140c810343d91030781c003030040c0c1c1b000c50000300c3c0c518000d40115980400075a05450b01514060340144182203015440002d030046881c080782c840201a80880c1101540e034491002800419002500300c499100d20b19010407282043e400503c080c11628003840710813503000204076524400d030818a0f01c0710303048141c10040b00e905864004240700400040039206a02d401c0800d06e0407100340e00c5920b00301c60143c4803010062075032190b25040b0350700b0764400b454620001000c41c0d6030301c102040104024101f80c030018100c0d1081c8489032115500810890002040484021403600564010350704d02e89804035400300c10140d2000181104c5c60310380070385030001d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 583099775 1250 583098525 583098547
    0x10905030c061209120a0905040f060b030a0c0c0b070f121a0925020105070f050f0a0e0a090e06060f0405040201020c060a090906030620030403080c070309090219020f0d05 75
    0x2403005000c0700e5040c4201e0b417440078891040c1c4090032954007565a90348400e1310b00380c1040290b0b1002c1c4440411149042020b00031840051704a80d44071604c0200403d00c030111007811641d6541d50311010300102506401c2c17001840d070000c4203194402c25680d541500e4891065098200c90080501c43d14007805268030128a040c0b441d1001e91040d20407469044540e01e94a001242039807119000300140d5695040040d46030700000e58100740c103024501242492504116508c0c070741304940040c024813162419840641e50740c41051406402c08036020312000b010031075455034440e03081e00e60074801e4181c070005038502d05084c0708091259405900404030380e59a01d0a12415034010f901d014200040e9800100c0c41c9000c6004e581c000714031070100081c202490660b804c06440f070501c040b01240b5410000e03c004240d0003c06a0741040c1c1049945555001518040c0c900741326035402055090300200e840818142520b919030001d40058090383d6155481001254817805c00160000c003250040c0700b100094 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 583101025 1250 583099775 583099807
    0x80105120c1e0405070f0206010f08070504020c0a020307180506041b0815100c0209090c0607300509031605030a0b04170705160b090d0308040609060509010b010905030c06 75
    0xe50745802c00b03214645200480d00381d81c0c046452001041c003810b030500415504000c4640101941c8020040c41410046229150481441007a125680102e55100c2409003030150000281c1c1c021304890382a55603151452190b504020701421052030080018500d007840e01801e40740070300113906401203c1c0a03c1d030680701108098101000b180d40080440304544440e0f400106580643e03d038007110a001d071041005009000f8241030039504900c0382401345480f484141c56005a008030301c68010a01c0c042c1402889201e090403000030f508400d0541c11f104e8004000f046040410b8064881102c08a100700360807030000c1c0700e16034040c2d0141c00000003083c000e201c6035800c14401c000300110545103150b40c3c00315400121040e1010703003107424070810529041182c2402403d90301c03011400c12400c00c000401c11011880054188008040004c0c01c01049500403241b07103030710150402c8a4104a00c41768000d150700d1180311701040b80110082081d00d40010021280c810042030586007000e61440d031404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 583102275 1250 583101025 583101049
    0xf1e0b07020405100504110c120a0c12030f11071101090e06220e0607020709050906070309031e0e0301140609041115030f040204060519350a03080105120c 68
    0x710300c0e02003000ca45c1d662680160750403d083c50108645560b10035481c242484d0015905011008040004403100e03504411a001d00c2e0340c00c001c10103481040342000b5406040020700507200945486550092001100040c000e8180154000103803041c40100545e81030340c09006800303e0307040300b40001e00300e440c11000d00c140d55515001c1099426103504118000d4407051200e50300b16030011410016010341c1045402d00400c0394143c180141d0601d86036403521100082c020004064883d5400400d050040c8038510f90308201030413041881e010204020301080201c21726a10950900502c0e507844040400ca280c01103500034190241500c1d9551218005400f070300599400103101c5002c1041d07050080055407041102448511031451701d0301c100000c603500341d000b4521813030700c2980d0b1011100d5444e84da902903d800000043e001440c5241d00c0c86003600703040031300b103681e14920b23080d07050403c02140c00d2001d0740c482d442e0b84101b81d0b00c44041100807030104c0c2c2c2240140c0d12070203c890103440c01c59a5500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 583103525 1250 583102275 583102291
    0x1270b4e0f0c16060e031b1b04360b0106030e030415020c0307030606080613030f08063105060406050321130915060e03030a0c0c0503070f1e0b07020405 67
    0x80f5090b4550303130341099072200c6007902c0c4c058001003904d1079886d000308040000800c0200c00342c00700354a0043c501d900b0422003002e00d40182d03511205800200c0008c10050f001056601d9481e0b014000880f00120181079018100c450400b0b2400003d403650180c080d450f251110000035600f0141010342d0140c0d0142060f69003421440303031100c6241c00d81ca0501c020300184d80200e07404200c5605010075a482c04802400c05125220703026400c9001c281d0010303000f100d481c5580740c0442030fa00c1c1d003000291b0008a0388501c1240d440344a00e00498241020b100e800e00c070500c020705214640d03c8008120455000f0312075a030305a0003c840e0700052541c0f0aa601c11101c030841c00c3e0b50300302240c40241b0350340c030090b40d084881020b69074a529521440d2448200000b40b2452821058100b0700d10040b903183e0013901041014032400b645c2007002c118000c201b00c0c0c090003019048484260fa5145981c10720045481451400c1090103c4a1a0b1596108221042d21105600070707117408030350713828800144001050780b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 583104775 1250 583103525 583103557
    0x7150b15090d08040b030709141008130b0903070b0a090f0206030405070909030f0809060624070b09010c170f0106080903090310060501270b4e0f0c 65
    0x10b00001e0300c520141c8054805000c1050b100c0c0340c1507074060328000c03070b42e0031280598514100688807580c030047c1101c2c03440c240b4500800700b61543c0c0f41d40000d41c001c60301d0040c181c110100402004d42070000142c84007034003c0a000c0540e4640b85c002004407031040d00003401c0c03004800002c60140c1007100c01550858803a40c111200f656460a0348022035400d114101c00044103106001521688885110f41241c48440903244905261000908501e0011541101829107225520302d099041040c0d60901e80c00000e1404d8510701034603954020401846803102240c60499403000c80a6001d164610a10800f00041e04603420910155480840101403854508c420000310300c00392424482004110000d000104040303081400140524400540c012040403036106005240da08080305401169040c0b41480c1e500d01c40c084241d0181e500c226401c890b90109400b11a004907841501101c4044100341c20007502c01e445540d498802600703450300002e25550b0130200d903004804000070004041c03400070310 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 583106025 1250 583104775 583104799
    0x6090402031e0106180605160210050d020d0f060608160c0f0503120411010201090309090b0a23040b1008180c0301060b030906070311030a020a090506040b07150b1509 73
    0x144020b000240c11610000f601044241922889181c00e50042c2450741030150902c0000b44140c18180401e1101900c6200001208059a40200111118082032180555862400301c00d4071000c0c02c03414810660315842d00800040e41031007002000d0280b4101c44092000841d161000c4400c11300100703040d01d15075804072213100015010001000110000e8001c3c17801c5241c00c1c100801c103004024900c0741035906005603500040d6000410001740da490000000e004146207000c51044285a04405003002c5d144801880c0c3d0b1849488502910104842c02e03c10140702c00140075190910116481c0883d580c20003084078111082c900d00c02c420a40011520100c0007100000d00751550b07031340003c00903000042031141121051000d40ea10280a040034065511008240034442c80300608406105074082407400c201440340d600040200b038000c01460300c1c0c0740c032000340c0d030a240d02c41141110501000d2020358aa44641e0150341c0b04114014040980c10301c0c8440c4148540e84903003c40d55000c3d00180c18 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 583107275 1250 583106025 583106071
    0x30302090a0e09010b030f21181903060509070b09040e0a151a03030c06040b070504080d0801060318020303040614090607061508010e07060e0d0605040302010b011704020609040203 79
    0x814414503c040c00880c4100c0c1e42020305080042c482428040358000c01c0c078090200c050f210400301c0b407206007505a50384448403080100030b500708241d01680516203c107a642c0600418a1440560b4055101002261110501c0959654080c458068010800d100340d05091810b40c0c071048014000c4420f8405240c0c0a40e101810048407250000206590300820321440321b0840840b82c0d660000c1c1c0c020752a00c001651071541e25000103000400e0390042800250140b84180107540c003c280a00c11180c51200308200504011000d004010000b4a032034460207018448608000c000c98020700a07610349814000c00b2107413444141101c0800360b604101d02c003061340b80c5000a00040c0d0042c0c070009510780b00b182090320700d00003d510001d940c0c1c0c100803410741c1003080400c4c2c00741142c02c103050400f0031503c0e8201165080c08030b40c00240240d440c1008000501d0340640207d000b00c1000d130b985000c00800c00783c1110500c1000d0318040d4110000b8810100c41e82000d0380119000504184006101d441c10030b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 583108525 1250 583107275 583107299
    0x31e0c04050c18010203070f020d020a030b250536090c1206011e2f010b013005130507031a2d07120f0b030c0301060b07030302090a 58
    0x2569110b44000181c0b400c1c4010140c100c1c021015400d20140d03290401d1030320b83d1440d40200c2c1001a10500c86010130000f190707100100100115884804680c0c24585400302ca803159541203007803880111950003c4a085120f10f080b101c44170100d0504003003155880c40c0d200e0312081c0c002c0756400000b18100c00c4102ca0740d6034410300d6200b1504e100c07200f40c2d940e803a501c842840c40e001801541c18458400407030080040150742e64000c1800c2842c02443c400789001c60a12180300442c2c0d0164941210740c1e0382c01700300e14190017050440e40c083c1c80b04460701400c18820711341500580d90809440c10302042890441d00d45030000c40d000769140d1360041d80c910503911200d0800042d40d0007182e00e0010b010344c060480c000d050441d0f40c804071419503514105c0e40e24002142407070342288240c521008403000280c0e500c0c001d000e0002c00e19000c207010000710070901d40010042c80e035103800324030038030840784200020320341400380c8000d561751290b2540c10003490707907070541c0a904402203c070382c131044141c00440e80c020404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 583109775 1250 583108525 583108531
    0x105010c051507050d0e1f090b0c0904020405041a0306011401090b0c0f030f0c10090c05060a110105090109110301050405030915041d01051e100c03090518180309031e0c0405 76
    0x20014042e6101d010800001c54901f851009642a05001160b4040352610181c0c0d0782c4010403503c0c041d41c80200c100018001d204542107203501c18903091520b40081554600100030401c00c3c0e0441d40c031030341c9458800c81d140540c5100c950000d90746000a200708907204000c4c022040c611801c072950400c0c1c9050311801c580084102107441000401c070a02d0550b42080b500e4440a0404810803400c80031341c40301d00900e030050140d44c0c00303010005032201080340300b202140c4100381440000c21890410142281c040c040902080c1c40d030542000f08042d0320f140600c5030701c0c003807503201c0b0056142100361410311444010100381c62103102c605000018008451002901f801c40c0c01e40c801a55a6040c0820040da1015204030f000c003054440e20011420307100c01003405104541420300480c80280d0745002c81d68001c1d20f410460304110300d02c2a1402c044180d900103030140442c00310340000402c6807140195039000d001052985544102c05001c1c003050760840b082100c0c0d80070000c0c0d0300710724403002c0401c0c1580d80c1a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 583111025 1250 583109775 583109801
    0xa0308030f1303020c060913090c051503060f04090f050d170c161104060306060f0617071b0c15020a060c0f020a02090c070b0705070b0105010c051507050d 68
    0x1c20514281400d58150701c07404010b41d52514019540b002551040c0203420b490061000040c541c01075590f00d50045c41d00300310303080b0500555407545441c0c0c40c4400248200350040c640300000c20303d51300e14403080d40d11940380030744071062030b81c4c50804010140c040b440c402e641d81000304c05800d001c0340c4140041300400301591520881c44a00b600d004070f01501c014840181c401007804a18440790003203c00c03901181d080003420040300d003050b001800801703031980001d1210785400000203510030700040c1e180c12290b6585030140c1080500800d85a01303070046030b1100014010b101d03142c840d8075100b4510003003039000b0000c1484103a11400a40180310344c0780d0303001016070310800808080110078020301a00d40000d00c1c00d44290f00300014065035503c2c80c0103000b0f205440400c00243d500303103000d003607510054010715025028204000c0203055a48208003d03507400031808000b2503554040c1801d500d0040d4000001c02c00481054000d06400c103019150f941000700c100b155554001503801548421018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 583112275 1250 583111025 583111027
    0x5090904110f0d08031816091a0402040302101d0a08060f06031b0d05010b0303030f100f03020a05011206032003010501080f1e03040b04120b090622030c020a0308 71
    0x10342008050b0091118851080314025819030020b01d010003600e402007558a04881601d4808007128202012012480513030400c1a0001509066540201d4160b00b81100314103810f1000c0703824041a88a5800003942103219941380d18009ca06c61840d0f0030070b0b041d0506540310680721020004100c44a142d110780754941c442c00a00100f46045500b50b07030464403c40061941d0110341c4030281d5240c0c03401301c555120304d01032101c0106001c001e40200030703a090014103582c1d403441c109030034000b0440f044d0703841c2c0200c2c0b040410102d1400f441c021820250b03038008003528529403a0000451300014610540780c00c0b641c4039100080002d1207100310092031700e542604c0c4c008070b45200003410300b111b00503842030100354001040f4031041e26001c40e07041d030752075915400c0c1e0310050100603805146200715400081001d1000600190458030550700b070400301c0c401d01c001c440715100d890026613030b00d400b925101c101c0c451011070007090a0b420a03564203054428145107901e06c0310341d00042c0300b60b1040d84c001c1d0b403c944 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 583113525 1250 583112275 583112303
    0x8040b0408100c09090c12050c121b0706020a0e090103050714180f07110d030b010f03020304020a060818030f13050a060503010b0a0915030b030106060306050108060603040305090904 80
    0x1406101d84403a21502c15000c00a00d100c08100404d80602c901c9850401d650b10b440120f40240b00e032124545011000300c0a102c60308000c0c2c214800e56108110030b180585000010400d94440d58001c41429110004039074213100868640070002d5000c1507860007440442e610400b02e0b5214841040e0081d40a40e019124245c684540b07a981d140d10004041e10400c44881c00c0340f01004424107030f903040600c001e0250216179030040e0980e1198101818a1114403034641e9080c9000da01d904003c03150082070ba140820b006d0220750a4042e401f098500030340c01210020140412807040c0b611a602440e1040d16642d50010392030740a013541e1000c0c0303411403110000500410064030010503c4024003090f1110001c6900e4000014230501040c09040d020020008498000910515042d000b5014400c144203104510071000b600901c0b140011601070b501b401c0000030000d009101e0341e0211403060f11800f06c241d076404200075056000501c110207015044c00241038070b03242c81c617810344254441d44034900702c2d00c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 583114775 1250 583113525 583113539
    0x303050609180303041e050a0c1401050f09090603071206020706110a0c0f02040b1f03200702060d0632060301060c0813030222180f020d050a08040b04 66
    0x4000522542c031407040c41840070441680002180d40c050b40200658440040b0a500d184524098920252152040c50960401d0100d003103500c0048031010754490440c250341e1401503815008007028815001ca050003804098200307103401d1548680d005080d20040c07900c4081d414454420400d0a941c940c0c1e01207201010400b03030f44200020f021041d000d007414001d40041c014542c1150020050100710030102260464982d6081158040740040440040403116401425142c030121030030b0000030b00700800d0358160030002c5507040704c11884000d0b092070f100d0203409102195016600070640755980c1c100001d0151201843c02e50340e010040302209040007242e0510b80b81410300c105051050384100010000241c1090581d05041c2d44281d48903111090a2a80200041c0329400627400c640074120382071802140341c0082000301000c400170805006840c04a440340411084000c000403030f96066000540f81103907030080c03003a01ca8021541c07143c0302940c80e680d07244c005a0008019000104090001e4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 583116025 1250 583114775 583114789
    0x603040b150622140f1c0606150e0d02030616020a081201260a0f0203010b090f1608130308250c060b190308030c1b0304050307081f151203030506 64
    0x13407160143d04038020800b0400940c542c0b9011010030310600031600c40d5511141c1c50761000d4420f40e00310304100219a50761545241c1d10440c45e500000080401d4842103413458050446402a900a401011aaa41c0101540c420241d40c000c15042d881060b021400040703200008050a0407400c1500c0d00551400b8041c01115401010b00200d00b44420b0030114201c600086155009400c081c00e07900c10051800402d0052204801058022000800f00042600d501406c0d9001d00100c1240c0c000142100300201c41062003690401c1c00e81e0003e1301c3c1200030070300c00d501454104855002d2200300d04501c45841c2d4100403a1602c00340440c504030444c4060159078802c0041d5154140c98100c59448916040031407001980401041544c1c04004100b07000c2c070304030a44010038141c0c0b401403255420b14030035030390300c0d041071241034403902c14010007050001000c9000590341c2442e0403400303103409401000704058443c1030304021b40d4098001000448004000010440c81d001384c400003a1030500350103110007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 583117275 1250 583116025 583116029
    0x9010603050f060417180d120e040207020303090f010504080a03091d1303031e0906050a1a060d0203130f06020a0207090605010c030813170318010b0603040b150622 72
    0xb150003a10800001c603008010f0b04805200f15982c00f5540c4084a180c0d0110510802289801405c0c00301c0281c00c0008420b81c0c030038030103942c3c1c41d80d01c0140300b00700c01c11040e4418954000d405030014441300c0384a050181140c110604141072842c18191210b004518042a25100340d0004041080400c95600b250b04a040004101d140380040e5103031131040d0021030091000001d00705580d4001e0b10f40618502e031911045c0c001181824012012030741418400b0f000191a1040511b24200129400200e81c055800c6508001341c00c031810401c0440e000b400a410050100c881c414030350410000003414903104040881c42040010b0711288601c8000f813500085802c001580361805100344916a0800040803440354146003040d03041c0c0d10030800e1005c24004120040042e80100d00034501c200096014620910080c62480440b4000020340c40c00da032400700249400041c03c001040104480010381e640c840c002e0f10902d0140d1142201090352a07108000b04d5000040807540c0051110081820b040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 583118525 1250 583117275 583117303
    0xb0325080f010e06120f071701020310030b0a090b1e1008190302010f050103080a021b130504050309030a061a0916030e1204030b060a0504021c0b03030c060901060305 73
    0x50603250014500a0109043c02000342400d261000200c45549400642001d010081c0580d445800ea440e42c041c0c0e42c00311030040b00d266016520030701040003014402d40c0d1160001031202d00880c0e18540760a610a00041e08007043d00b510380c3c6d4103802003542d1030303501c1c0d01402d0303143d20703c00307200e00c0241c400342602034050f02e43e41d5101c22400701040703a04000a000b00c40c6909004040c08400c0c81450140d00400340c542d41c05900a04220000061187c007801510522100340c0a1701c42204c500c524039000c54409601c99984908501341704407040c490b03503000950080c0720304203c034601203440c40000c0c80d100c0414030442d800c85c1c64044803000000d640e0b03948112240305542c40c43c003d007064205014000c3e44001403404040c5d071440c0a11140d10708000100c82ca400b0750100d40d40e2941c032420301e84901035044842600a40c42e00f039000a150515100f15000e58034418080c42e00d01c11742140c0c031800703032640041c1c0c240c2c144000d00409a000c0c009125090140003088000244680755180c40c80c10242c0c0480505 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 583119775 1250 583118525 583118537
    0x203090a0803160624031407060215190207050303180d0c030e040507170406060e0f04030c030e0f0a0f08070e0c071707080307081b131404060b0325 65
    0x15852100940f5034104840d400400440e040426400401025440160403016203009501c00420f0000241001500824060944074007640740e0303000f683d80c0c1c107010060100c102403c0c4e0008009202841640c0300708509610098900a280c0c0c65061941e001982d46145608610012508043c01004404c03002040750416030b040c40040d80303016141108412403a40119114000107150034400d5100c516011760024907041e250500e810a6401407000d802905880f0307003036001080c08562007202482c4915410b0369403030400b12440c0e908890488002ea10700342c00154250525045a58980e60840908144e40c1c110140524140c0e8440c030705a8a0740c0714210741949a000d004480441404651003a40c0102c030349840b00c2e644240400744c62141d00000340c4a40e5012050080090340859100c1c01500c0d0301d0b50703001c050348241050301214070840d0b00c3c950340100c1e0b80780108607115055801ea51418001000098500da9038040c00031581d000301d170459440204062044000720501302c2104e005010351a10b6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 583121025 1250 583119775 583119787
    0x2031009110d020711030d0816020601182324100e090907030b0c0306030607140301060e040b0301020c0c1507020f0909010f0911180907270204060203090a0803 70
    0x701140d40b181071401890b55400090410510008520805111170302808640014000b2640144508800c4c1d50315041d020000700905059031002603aa4180c1d010b2840c440c0c48520901d01f01002800c0c16004403c200042c0c0d00a400e80b1034010051500c42c081c0548800c2e5240044d1f10301d080640304540f1410b208044010150000c0f03588040484281081625164210b1322817041c070340d16060031584010400740c885010006000d4190020b0742c0100f105504440a6444900b001da0704120510000018900d06000420646100b1603007070400c0c0a018000007613803c502030200303003a60301200e210001070740003a03400505030a1000c41605091851210142490800d45c00107a030450000701d1a4802c0001e400820103082c02903208000c1c40100d210308200d04a00ca14150005400c103564641c07241902c41950b242030100201e450b442100381c03102501405003001c2282c3c2001d9602d81c0c14096143c201100343c1e401c18028401407002c1e1420350020b580b541120007c0060480a981011010390011b200d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 583122275 1250 583121025 583121051
    0xc02060118090519060207151b030b011125080d020307080d02092715011e0513031a0c0a171801020d091505040c0605090a0b0a0302031009 61
    0x400704040c10220340106a11019041c03643c0740c90a000c00303d8682500f0b03903256200300b00b190b0f4010308540d4030902c240728505140c1e2505404452255502e4135081e011524001003242c803035401014030b44c20504165a644800c03114071032811090385910790080e80303400c0c0c901100798600c82407140180000c400515403401c1c007940094590085120081c14100046218501a06c580d0195080c10300e02600310150b2202e6072100041e80030860000d4500b16454038003043c1da00146606011128034182c4032035000f56101c00000060070208a440020000d062100a50112011050320000c0d4055205070b890054044a40144a24054440500000104006c0c4601a00300300c00c6480503940729115107660741c42c01d6004c4c092490f0125540d1883d44005003142d20b06226178440d02c0c1c524052220200b02d0b00e151a00a01210015103000d41051440300301040114416001030031817034000b800007180d080c0e58010303941d0160085255000425004020001c404140515520041c84202000d000c2d003070750841 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 583123525 1250 583122275 583122299
    0x91902100507050c061c200f030c09090c030109060506030f0c0c01111c39020309061204020111060c0406030c0203041e0f08070b0d0e0a0b10090c020601 67
    0x4900380074020840e007090010900c0f02c40c06040000d40310b80d0703490071040100b844150071141401c0c0c4c213a01e400e01c00c050303a00c550501c01044403403040f00103140c150b840640124075007004204841545c810001c540c02d5458102400740506a0700300d000382c607541030180c80d0040ea0059008140100b1040c8104600c2400c0c04540c2c80e00042d54a0301d9550303d00b60b2400c4a80540612030ac0780514000c00585203400d5060b0004c44010154a114100003910101195016400723041c00c240e84500c81b80549910044846401c00c81c0d604100d00480b86444c00200102e1402d0300240c2c140140241a94100701c1556004520110384206c841d001d08813510303100d0301d400c00034000c1d40030300c508040c0e4410840d042d060080085078050452a1503812100483c08500100740a00e8090900051440940003504030000580f0006a82480c402c5038100240b240c0894020061102d0900f80c61040c2401c01021503600060f560180035007041c4c1285407800c1c148100c00f501c1e103130101c1b0310031544a40010824500c610b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 583124775 1250 583123525 583123549
    0x305060c0901140705012408070f08030a050a12140610050703080727030b071107140f0d21020f0c18072a120c0218041e050303091902 59
    0x90311098a8410345d0500f2401400d001c2d1000b949449a01c203140c1e110802c150b90101100c000d03200712400d180d21401d0003681d524642c4101c0a00303610500c520800305002e50040c0c403c0083c585482241c41e88116030f80000c1d105000680c0c1e4840c007400c0b080c445c250030f24400b01d42901c5d036182442447c090450350000d008000c01070940042150310303681d089405da00826800e5425a0b00f416400c8040e481741042e0703441e2881642d1000200d00218804c6200c3d440214048046402c41803956041d55104d0051000ca48181100f0660040d0003180502c00546411914200c0b41070031003404103913080001c00645480705a000040d5650b001c0002d2007501d81c0c42e601c1200341003459880d03003078154076410002e49050b4005107005c518200041d145415240034503200c0d40c10320707001d1031203101620f141d000c00351868035020304042d40101c121100101c1e803503071b00305005401900c5011107036510448560b81041410500380100c2d1560000000e111aa0340100000544034080808640c00d1201c03690014000324900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 583126025 1250 583124775 583124807
    0x10b0304120201240f0608091506010201021e0c0d18180b030d0c15091718041e061401090312020327010201050906091929010305060c0901 61
    0x600d4036280302d200390400003d0f0050102405220f4000880748216044c00303018811000d04c088000042c80c61189800c0f500809108003d450640c148003820100000b00400c03031b9041d590200300c50302c0103200c0342602c1c1092440044005440300741501c0f026050521f5211001c080110000000211010300c0300f4002c1202da000398954043c41d50140c0071000f8050a4450701d5142c014031200b1110250092034180c81507110700500403001d0b83e02030810b800ca034407541026103514004a80c1601a10440005214442000c8100741e41d05111100103030540342503800c1d08092000420294895080700d000300800b50084044004c52000088002040c400c8107102c0600b400c180304004450b070301d000b80121140c84e002d1820401c010803e80141030424410380660381d005601c0c220002d80240070103c1d1250180e100500034001c1c4944106048484404c0200c040d600003075145908966643c50101d41c5004a6504840414940c91410302c1400d1187c008e08004070f4840410641d4980d03a4803211a01001e2380c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 583127275 1250 583126025 583126043
    0x1b090303021e0c06030f0603060c0304080a08060d020a0b0c010e030f0915130609061706090f190e0604030306060203120c210a1b02070608060607141f060509010b0304 73
    0x482c000092501c10498103541c2c200310008240801050782205051003404190301310742503600d42c1007442426100444015020b02001d001d181c4a15118401e82500044000c0004580320341c683c0025605080540c084000d552001030402c1e1b00750309c01c1c010a00c0040000c070266040486410300c2c4007041c854149100e22545c06103410700094007091068580b0303040c64243d81c02c1126110080540405501d0080780041118500c1d008442c410b03405019200b8200500080d1450301c490300e0807030701c640d00070784003900640d210402d01505038076a00c1031031100f05030180101014203007070601400303c594a4101c4401c540040265441292144008641010400304466a07500c161701c10700d0b4000000b02e03c50346551032882c0600c0102c1c0c144d900b014840c1d40408000e0301d0140d00d100801e03640c0324098812000401c00510000d1400d2030083c02401c078090142c0e03822000b0035a4146460b0520f860f044e1610b0b419103039000390703004c01a1940700b204050842a00c0c1c5000550500d40e0f27108250000400080c44050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 583128525 1250 583127275 583127323
    0x203150903071718060322170a08010512030a09210b0103030e0f030105070e01110120030a0c0e0a1e1a0c06060a0b09010507061e1b09030302 62
    0x2200700200c604603508403502c0e040c42100c0c0d03115803030030340d03c215070704145408051102e060628000d03040364016a129144c1e00e000070300728002c000044120102c1518500710b4100c110701515208002083d00c1c0006603075000070b542c1032034100710038042011032410300c030750090000548403900b0110b61001e680b440c521000300c28190300400000100315000060031b1b44400303400007042580003034803416401c9048400080400340d00381450b0803140212a0356000640e022003941c519402580401103986080740086004003801c50071102121582e0070903015448000200031b0164050311508050b02158078124440000c070344001924400180a8802c110411403054003110001640020080030303580386003001c5c2c80e01016003031400c0c0c000045011450068200003036061402c0102901610140e0350054200320501004403020380014400b115015500c05c02040c2e100d40441c013200030361040d540d0100e5220140b1414140c44000340354980e0074004104400e00000c1c1e000b1414840d0444401d481c003074040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 583129775 1250 583128525 583128541
    0x111c0c0216150809030c0a02330315030d020715030605040207210314070e220b0f04020412170f0301090b0103060504410c070b0702071802090f0613030201020f0a020315 74
    0x10f44e412264a03441115880789040a127090000d1807207400041c80d5011040410310038161688040c418002c0181c0014005122252071066001d01d2048240350018895403149c01050490340001e1090307850911484403215140441c84541c07850f40000d140500c0107540b004019211000c020300320b8800c2c03040b401c41c02002601c4a40707240300c2e404540301d00d99807016403c04014000b801d5800e20580191132841c012000790a041c0202c8040702d1189030036040c1c3d048030340c03203070321043ca0507426000a490b0300304200f81040303a20304040d5000e44a0b6060004151041d5000501282c0c00c0341d0040d030196080103402c82e0a0103081d040c100081401c401d0b141e540804240030710b054035203a42c4599038080608818819221501d8010b001c0191240c5c01d04807031a19011400d99071003c16100740b0301d4000586560012050141d006408200c0d406003a04004110030400549290846015921896100c03002003003550382c100801082442c8480c0a0444506e580e00802d0f00c40f28108400c400070b034903078000f2034104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 583131025 1250 583129775 583129819
    0x1e0803030621010203100e0604020c030d110408060a0c12061d09010615020a060617061605090913062009010518150301030501111c0c0216150809030c0a02 68
    0xb40d01c0c800855a03450400503c00c407950b814010013400f0020200016814209442190000040314004505045a10781007402810407002918502401031100055040d02000078501a44040001241080e0082401400040010000c400007400c3c41030030030000507019403d00116410395442c1005079183c00f01c040c0505180c1e440f1080d036140d078101802c142c1c0c0c1c2c0400d0031019144207200a201c456600e143e407003808100d040e4010150340120000c900321540301103800c1d240c3c20b0301c0d08100d810005501c0004240c200121060740112804441090400045204203904800d450107842680318200042c12154010005250b042c80400140c0311080d4907100c801c0e01440d80024200980340f500c0310525120b45d0400c0c401112298200241900d24003401000d89960114030213182d11030514150050018000699880c1c00b50301488000c544c0301c6251000510180c41880510403040303510100040c54004000c01300005074105101d0920940008200e6a01c0d40d07404079042144880140150249 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 583132275 1250 583131025 583131079
    0x206070807020111030f09030c0604030b0c1c050a0605011e09091d010204090209091003080304030c0305120108010c02120301030206040b0c10020a030603021e0918010f090c1e08030306 81
    0x8030305c40440c090080d2044180180400c0070141c0694058040e082c003445002d0090303000041c41e4001800c0003c0c05110300c80050b001001c9008a002d080103c1403d4240031210103a84201032203031900804d03c110b58004118840c61030f040c40c6410346a80013005c008206400501030000b840d82c80300062680520321038071121940000100031541c0c0d90396414100003d5201c0e0020501400d101c0b40000d00ca5072441c0540b00c12281c200030b00360714681c5e440d94125880080000103c0a00c241031115100b0462440d0380a800781a080000194400c00084041c1c0343c56105504151003010400040c00141c030b0707000541d02202c040c40e0350346e900c6140446000d0b06003044000800d4140b44042050492158550480b408a038000d48291603907142014020040f5000540b5a580048800011903203030703143c00011b5880d80702d40000000b450b118100c142000d0b07034038200c010398001040f00b01c240800d02e41d07403009103000d0015046e0301c03a000340380800303040e100e01000b0016489601c042c40c03c1d13906105000200c42c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 583133525 1250 583132275 583132307
    0x711010f0507051009031b080d0209060403060e0706093303140f0105131404020904140a081201060e0d03050904090f0f05010507031109090c2b0e01020702060708070201 74
    0x80c000000404c44401010f2140d4250300044404c07100c1d890aa800020001c20785412a421300d14010080c0d902c076019502004105410078000c00c0300102103011441140000104240901141403a08800078403204850b00701c030742c4100240c100700e010316001520040c40302c80c16445108060440c8601079000305280540b608031046d401082200c0b001c0c4082540e41a143c044175900d04003100425120103e50900030000050f40c0c80d14042405807074080d0300c3c0e950240c46240941000c0f035400042d28106000070300b080b0340c07008007c5441c000c242c2068800d5130141800785000c2c4d4541c07402d14000368040442d0394026081c010000b60144a40e01d45400658190350001c0582e1224482c5280c450305040d002c4806031219443c3c403001c40c00191003401a81c20b41c0c212660719070308002160082002081002d407103120b000000b081a034a005100c80890300c0c0714414604d480705411600604081991001019614135900c104105001a590720301075584a580001c1d10301c0d1214583d1005842c85400018028 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 583134775 1250 583133525 583133533
    0x1050a0905150c011401061b08090112060513092006070b090708010528110301140d0204050a0b09070c0537080c0c180f1909050c090c0711010f050705 66
    0x20707984e017944c5103041c100c802940c2e03100740d0428560911401404030520003490002c04001040c02980700d502040307040c411103000050a150b4a1000034140410700355940100f0391540080b500b88852001058103911411418813006603001c00021240d21402c5001013801c0380000203e02d600d03001b0045640503100f00c02c002c0005043c81d0175a120f0b0840c5200244c80c40c1142030814441110b0180507090513000c0400f666421642010184a41c80c0d01412149401c80081031100c00569914026240600401c20b000214248160280010301400a154034180012080c4800024100082c0403070610389420300740c0c800c9441806920240400c071100da01a040b41d96003800300b4420040001e01142100d03400300c411110003c014040040500d010900c0080310302c40001d4804406d0f54440c692118810010382d08100304c021f180030881d4000c075015501a8800f41c0b13001c2c10303401d110a2190b009400050704500f02241940c4901d00c1140090300b2a04001555942c0720026010310140c60006078044151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 583136025 1250 583134775 583134791
    0x1a0c06040206030405070305070b0d2403150f0f1b11060c03130b0a0e010506030712120c1a010305060703050903090f010210090302010b1525020d061d0c01050a0905150c01 75
    0x200e2040d41003462f807080d14500d80141082140120828510340b841801381d802074007890f58803602c544e100e40203038a440c01c6443d80441440f2041d01d205100700001c40301800102407502a000d03031603e0564246c0f10081c8142d481e54001400750000d54660301610302c982c45c42c0c1d69943c4000b20648040050300041c84000e6220906c04090b442c3d80181c50743c1c03030094008120350b9803003104066071a1260710a205900440e482000042902c6a0301d00420502504110b103048500d5a10203c4031362404603051040c41c1114014810050f003804080d410051524003070110b414100341c03c540701c2c81640441c07845000004002c0006074020b004080c2e16a00481041115042d20701f00640600000182c4034417544502e281d1546050099055860207c454100c920074035200011345613108070300c41c60036640404002110380018030b06000c2c000303280e820b00014070f001c00140414549440403806400c0d05200082c010f60180561045a25048402c210744120362080302c0d0042908920a200c2c2c40e0324654240143d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 583137275 1250 583136025 583136039
    0x1b03100f06020a020103050901051528030c060e04090b01090209010c05120a090e07022a060f0a030f09200402190c0314210601031b0201061a0c0604020603040507030507 74
    0x306030f654500070f0700c00f400195603441c0e41314201d034400c9a015140c030321100071017045400e1482440080025004000d6511280b03582c290b520031540d5442160b400d03e0700d00040c0044c541c4485458072011040d1402d108a45c2180c0d90400811014010541102d03404600d04269a102c0c507401c50070309401c4410350740d2000000020a001c0c0c0d00182900300420111000041c0320000c0e80e0328240300c3c151680c043c02100c0319803024107910002c018003004400c0149440c00500390b40d810018000708492a0013143d076580c12250290a0700d0001c0d5401c0c10191500769054045080c40035040c038443c1d1710036080c542440000e0009402401800c595645000b4800c0c0b0310a4100d41003003580100030b000340c640072846104040c90348450312a2280c0441001a0f240c4560200c002101142c0d8010005060101d40c6070070009040b190b009049d1205d0300140c0d142c0208202c001034a40041440821041c4000e2400c06444902c56594a01070f00081c050840040085c00f400780034440c20024507405419201034540da003103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 583138525 1250 583137275 583137283
    0x6010333080d020c0915030f030f1308060907060e04060b03040c0302040501050d080d09230c1c050616030e1509010c0e0d0f03030f060f0f0603051b03100f0602 70
    0xd080d403070348a94164414000d0002883c81010300000385044d01d566520002411400c0d083c0301020b4251060130010146241d082c009400c54a1401d051107840d02085416800d10b55419403004505d07420100174402da44001003000810384481d82001c0c80c80303100300408203004210507030100e03040e00404001e000030001500b4142c070840b4000c80b000c0c06180d8035201040503605d0040e100511680b0704001391440030241c0d8107d03100f158010081c01c242a088001d83c6140c85007224494203060704010100c00380c0d8038141c0c401c2ca8031130050034003004504103a030365119a0740f0005032040600c11542c148560f45a446078115070450b9200c1010b07070700348810764a40d00303420000a4444402c29401c0059152440d0b00c20001c18943c0c00c0c001b080301c500b07008552640340c2c407034035484010340c00c02d82c607100d1811000c042405480e0060014015080da1103181c400e0314112606d26400031700400d8109018001129060040410040030404080b0390b0b07510b6108042c08070401c95031014401a036450700014450303070049 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 583139775 1250 583138525 583138529
    0x6131a0319060f05100e1012060f0c02070f030803060a1d0907270506010c0c080a0b0906100608070921020f0916050a020a02120d110303060906010333 66
    0x20b1824020014440018801d0f83c8040f91031482c49040c221040045440c94883c2940044c00121118162500c41e03243e8420700090340400d13540240c5031140c40c8015580362113134521050b01480582446400c18940050900061001401e0000040007207003095442c140400003c1454050000039035000200849a0440417034044446000369480050301603091011201d85038803001d04492643d1f0395003040b40003071102070b240d1810055010480780000340004951005011a2001032506003018070342000d407180010650201500008203121440180f00c640340107031b40c90f50030001c01c0c036580c011089800f00c900d50701030440d42c0303150079854405500116584200e10b001f941c0f0150901c40c25414001c46800c1070701ca0034180c0c0324014462910b0380c4150045d00c40d0901601c1510050041900081c0ca640352070003030480c0e69000a00c600c81d070300d604150402c500882800c091030079840c004000540400303000380750f14149a10f40d0108034034074800302000503900f10500b011200301c05a075221541d200b031f414 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 583141025 1250 583139775 583139783
    0x902030f0f0322240f02030a12090f0209010f050307080c09060d0305120f0709050d0302101a0a17010b010206071706041407020d2606190b0705100c0806131a0319 71
    0x40c4006401041c03000c4100c4035503aa6649801880d09e9900d003017030000b800e42d03003000d86036514039940080c01650313155611030082100c0e190b000e80040c2090201400e0000076400700c2d0095210700c141e01620f485041d2001d520a42c00c44003400d112426003800d0304c1d68800c1d1902c102e018020b0f0b00801c84501c8114090b02d010300141d549140321640c41c0c0e424031100042540016015901c9504120700006054108000c2d409101e100c4113002d1940310003044a03446103400081c074415010343c0c240008a001d06c55094455424030040c111400d280380060400d11003002410484000400040c80325152608145070314603801c0c100c5140392918400083d01c03420030228080005a04051144124942d1500e20640e04c0c412100f019003612203400304401c110840040200744000080000361110043d4040c14220703005402405206856000e058115440800e00074240948903041c0b0070503442d00f0340d03040705e403069140b4000369407549000e00c000c0d640b04d007080580d4944954400460b03030070098080c03d0700c5c140c86 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 583142275 1250 583141025 583141037
    0x180e06220c02210d0e010b151c060e0403030b0d1406090607020d14070203122b0212040308090708060705040815010806040f140a03030902030f0f032224 67
    0x91001501451804015000303c010740900440034942d2030b55000c0f800e0741c0c0700100005807841c5140085224003c10f51030304182d00704003050340c2c907651301c584800c00d0110050500801465040c501c3e00c405c103142c054400b80c1015940c0324914000e80b1088180000d041e00701c03180e40c076800da01c0603001c0d9a400d0105e440d06003030f00a12000c640c03140d00000c4ca05040b01d40d10b8540d041400700940c40c1200c3c5400a0070b0507645480340d083c90800d010844001004103401a48011440c48004e0110040758000800b840010034410012080c0140b01100c01540050741842c00c505a62500703281140380400d0351304a03900502560b018002e500c4d800800402c1110019000e40712000715408603400b81c50760911540449800ca4000075000607a00400104580d105800910452644a40c00c91400c141e8000c21000f00c1d981d040500705500d0704000c00036025207010f008020050303102c1c0095480e4028a807a4007800000008a003001d00041c0c0c01d0341010344030b540c4080d09403009419074014001094002c070b0000c104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 583143525 1250 583142275 583142293
    0xd0c0e01031506180e011707121205090103020706050f01060e0a0320060408060114040b09070e060309010b18061804030c0201080c040b28180e06220c02 67
    0x101038082c02e41401a0211a0390300286048402e0b20300703000882c80400f884c44520008507056850801e024003030301d501d03071640c40d02c03000154441d403030500f00e46c000360480d2251044403400244c1d0010310000403851483c01325155140840160301a0203291001005103003413004016100f6200c40a150403224590b907190384005420b800d006492107075010242c0f2402801e0180510ba0340070404115107402e01800c8a4541991810603900304642a0001582515044034012040c40c042c056401200c8049448ac121410182001342c800c07a103100500303020310404000500041000c2d84000e90340c12000c0c0c85134600d1030f40320342c4070002280110382040c4500550120a5030744604035603418462035060700ca2140c0203046400644090400a010f00400402004003113000e800d0840031f40b0034001c881400c408503841000d00c0106200b540e044020401490f0440900240c103246e17400c804451300740c20700117155111580440d030400d8802c02d904808010310007607030120780701070303408050310000c66420751380030340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 583144775 1250 583143525 583143527
    0x40309060e0d06110c03040807080d030606050904050a060906060c1e0f030e0d06110a14161e0b1311060a0507061d1c030b040506100f0c080d0c0e01 65
    0x1041030000741c2c101a480740b00b000041e000d544000b07000840d0440050420101280c650310b540e2141e00705045a81140c02d00300302c200410881c1c0540e09030310b4141403140034182000105140038000d02d16100305c1d21940450000f4003140e2007a40034040240040c032805480b07200150107505101012119400d04d01c45a041d8001d10190416420358070541f03102141d02542c6040700c0c4200801045035000c0b540c1494000081c0c40c0b40b02d070322105204d1594032901c43e807013840060f1044040e100da00700c09000030000b080084840820910005a000c0c01c010750240e00c0410b03895400001c00001400e0000500a01640300d1041180c0d2000e184142003007049103102d0001d100c00350241c45915808100180012000a849500030403001e075a845503003034007000e940155525101450307035071041000c00c00e007420405070783c18041c140d4450000e171428401403d0010200300102454160a0708100d00900b4046646100d520014455900301506548505003810f03180000c05240b01c80710041642480004125 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 583146025 1250 583144775 583144787
    0x8030c010b0f190501080c0d090321090215070807080a021e071206051315050910090f06090311010507090e01050d0b010513020405060c030415050f191b060504030906 73
    0x400358000c603c1c0e071030030715190064503d400b02410309942d1031800e0013a500c800c80148034024096002c0d5503121031800e000080d0460281845118142c4241003003840310158a84080c07103070240c0c9100100e20f40d642d08a08000d8414064002d000340200d0000034001c482942c000703146000d07095010007131709220881c0a151a580c004c18410403e10081c3e050040c1d0201e0413541c0080c0c0d20134500110030203171248230381c0d82c4c0c220311040c0d08100c0781188c4d44900b4002003000c10060021003549010040244070760503112190300040225005006940700c10888042500c0741000071108020070009101d10309000e0000761a840ca680207244c103043d200c00001034a841d114250180f080e4001c00702800e1a4200801d00500c45640d00103c515203808010000355034481c14001e10700480420003840d2214184405c0354403250b800340e500000c11409101c50401c3e8400c80088540048101a200d803241c1d02a000560b80360603041900c0140c0000c0004a4060241c41d4204c80d2041c2d1280d91003051003901e1300016115 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 583147275 1250 583146025 583146049
    0x2070806060105160b070917030408070b0f090a060207092007021525060b040203010312120b06030403050d0c050c0705040e12070f17092808030c010b0f 67
    0xa10360204020030700ca035016400400d080700e1081200030b101e0455450b807014094007620518001406900c080003000c02c800682280c03649801c01941c03030580343c000590341c5e90700a0300800c2d0101c4000100300382c5100080c012103035031200207811103101d190f40e1600a51500114441c0050b0715060083c680c45110000000003010040c4d840452308104040d001d100c841c104c03c1d0352002810b1820002800000c010110350b0031921440030000394210203a1070000306031410075040300e000e140144018800500361100c52918042c0c140b82c000342401008081b5070140284041e50343e08603000000740014103500000a1a8110341c580d4207020b048004d600032110703481349a601041e00d402014003800039140c00d400c030700e25a045250450390b404048910781c109503400182c04441c41c105e1003000d802004a24500000103d400d04030705400e26000401142c0c0301c0c0e03500000440740040703080b0044216403400400710080e09106044039115110001c10500038442800443c2c441d8121402c3c1c0002031400301400c1034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 583148525 1250 583147275 583147289
    0xa052104030b1501090e01150e040605150310050a030605041a09030f0c0f1209030f0102040608180a0f06050604110418150b0d05010e012c090a060f0b090105010207 72
    0xe40e10300300781e0f50003a20b2800c00c0d10304025501d0030004210102c200014060204403047c2e001c4421044400303440401c00d0800c41c0e02540c10640c1c104500e41d10b103e480c14402410403105070b969695000b81c0e0840154507000a079001c0307044c0b2000f1061205540c07009216a00c1046410b10b40002450b0780040c4800441b041c1e019544108043e032a1a0460001383ca003c0030201c04031000c40f20004403860801c940c4180c0342081040209601401340340800c065a603249012008500c1c290400c0c00080c0400780081030004070b48402401c00100f8001000118446900030075024482c07030311031411308050242030f1107840c41181406510040760032144c08880840b40712203032458401c241c147c3c07200090305142c01200200c05140e80700040040352170000300012660410001199810540205105201078102100c0b0880c0741c2c0001d150345040d042c048980c0c84c000000341d40d095a0b03403035156141600711b12009290600341011001c2c1540c40350040c800f90700707040700d6000b8a40c0e2950012a0754001d02e1207020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 583149775 1250 583148525 583148543
    0xe06030f0a0b0102010f063b130c050d0f060b060405281d040c0f261f1e150618030212160f15050306040605030a05210403 54
    0x7414101d820350004072520300c1070002262089840491600702d45480c2e020001c0060000c1180881c98030911840c40001c2022080404050034000c1080a80e00018518540380e0070a540c0c0005208007220000005c0c20000d045c3d8440c0f203003900d007040e0b540c04202d00445009080000400b414075000c001d540079a0b01c041c1c204807403040d42c021600180884407102c2e8040480c0040c010801c1e10b00802d0b030030580100b04200c03622500703052170300303c9000103503910456001c29808020300480325889a0300c08044007680f004411aa4a0300c01e4505152107108440d40190006030340581c0c0d001f42e5044038102070100501020390154401c1024141c82002482d02d1400350f1a1400740301c640e010340e40310110394440c1c0b43c4510b0119100d60128106407003901e180c0301c0f50760103c1c0c0e441540018000924025094031030b64007a59500e00804900e90040000c1c254052280220021b4400c0d103440d8001d100030312000341100c0e2140e900781401a00d80c0031051101001e0520300d0348044030580307620111021a54002454 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 583151025 1250 583149775 583149781
    0xd030515010e040609090803240f0108070e0a080c090f0c030c030403030e0a0609110117070e0d120c12110706050c010f0c0e0a050a0311040e0f0601080d0e06030f 71
    0x464100c1000c41c070b9154480d640f1440421a036406100d42c3c01e40b28490341d52641c2c0c2c5d0400e4403100a4428507607590b90a4840c90781211805900e545042c4c0300038150a003445901f5888400050320281d4605c20320b650031428000000401c40000a103468851009035000080b1740c442410310b0408000c111446600781104001055030540820019988a070192900003001c00d500c00c40142400a010030540c1d20f01d071502824030a2003640000e00d402c072030090030b00300040c01c03440c8a10541858020007000610803e40c1039462141c890f150082c21031584800800e5644420b44800b0f0308100d0a0001030360402042c01d41001a00c1c002d0380d248003100a4500285402480c005048425900c800244101075403162802117080e001401412401411520782c0b4a010200401703000054649900851007203d1201003000410541d48624130021810f42d804a000412140700e5850038031071041d4140319115481c00042c414402090041020100d55030341c42000c1400b8081002d580804c1c1c94010003c4900008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 583152275 1250 583151025 583151027
    0x3021024032603040c050a061718010603020306011203021603050a060c0522180b09010509180703030e03010c0c11041d07080a0b0a05090a12120c020a050d03051501 72
    0x305010b4051510341c2e500e07901000003a1074400d90815034089404403032410040c0034078580380c1c001e00007034909858106280059204181c04100d4041d00c03003c02280390100541510000390844009103070003038212030340b550703440c0389040094103040d0058006000c1c010320030300f01000b00d2102c4011a504034004044070304680d21a10010007881d4a408140002040501680040c4d0304400318800164103a80752020300e05595030354010381004d03c00040924000000b01c8a64071101040d05642d815500c0006d29a11000041180c10125038020000c0c8075030704c000400c2503404210b5032101c6500740c000340700768078000b003090f01c1c0b04180c0c0f03000170b200c040c41084003001800d05911402c0e1006070794109628008500d54a6400d203105500101c0b0a03800564039a4103010781c030405250094400c42042140d071130025250b541740c0c20071100052903804140d10308252139204400200c40650908001c109011498802940d554200c200445540c01021311544145009220b1507120f80e0852454140100d02600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 583153525 1250 583152275 583152293
    0x40b0907201606030902030709020a170408040909080a02011545020414090402151e03011203110a0b013501061e05010516020d0605040302102403 64
    0x511181c20780b14100a030340010100280c220024aa0340d140004d04100c03e006042c10200707181c015110107801004407103c0c503540424107801c1c041c0e039058082603988076490040901c2c455680892000350400205806101c1032100400c400e0209070020801e60343c0700b011710b007000b8040b81700d41c0d0300042010300682101562100c40c107900410940c00000f0f02c0d0b60410201c01e22200803058401165400314003800700406541a19100e14000c8691840038130b010750001c0d400300012000e0704540c842c080340b20f039424403080061090070502030700015102d40c0c640350107103040a4100740507000039034400400052003c01080140401c2d400032601c8810340e0a10581c1440c0a101e440c103400411051144111a292020302000242000800129176a86807038202411900c02035035084e50840b090b0010403143c0e80060444540c54441500d1b4a0a007070a03000003a640703100f9000180940e401d2604100c20180c8c04a1000c0113003c400204100485158401d0a842d212071034440c0e0000c019410244003192000d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 583154775 1250 583153525 583153577
    0x10030905030f0d0b090702100b01050403020f0f010909180308010b0c0627010e03130b12041e02060304030e0114090901051903050d050c0c040203070e0d1e080306040b0907 75
    0xf80022130b281c1110070101d40c5800c1d0845101005800048001c9100152400744507401c020034608142481c0c2913400240e80b03000038000722032080c20b2101d051070341a4041c4a40e80001d180d80c2400300609551411940844a100c032011400155440004103071000c0c49015200045441d00080550350750366030b01104510340d01c0010f00c074400e0b035850f8010780d4a0303024003aa820b9607080201564441180d1500079003100d003160016a6191001e004030b1102c100d90300010381e07001f80c100c5c0c1d808004040c400000045a42d0492003c0d402000000c00c0005054021155081d8890207982c0c02160081c440740410641c09120910f5902c0400700c0010004c0346401c0c90016082030f180791407000d1481e0381c0daaa440c607000b80d445c2100e01103000440d201d2a480c1c0c06022091311440c042e1003e43c510f01d08880c0003400c8c20011413805108101424070401400081c0c01c170342d81d024000e84100c0310420300a09243c811600308a6889105a0615030451203500303080300c1560003004152550705034070580240f41c1c42448a03503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 583156025 1250 583154775 583154797
    0xb0702041d0d050c070501050702010203070b060f120102120f010b1605011401080a030210091109040c081f0b03010c021203090118030504050306090d0509010c02060405061810030905030f 82
    0x80400000500014040200c2d40300803512002d540e01201c90a25003840c07000e6003c0d078107004050103884050f0341c0220031940d020350302c0031388070f80c955442c04002042000e104807000e801101d142d10051103030790158000d10b0008145a20060140c1d00c2000346458010240548108420284400d180701c07042d10000b0000c0350310900003c54a031081040750b0b0028482640400410fa1189604074141a01486000483c00e072105042c494130043d42c480c90301a19100030303c036014403400c00c00030b030074015201c039904090320380350f800da842c0c074042c0d99280c808042004014840440c0f4040b007220061605104401256401e6005415040c2208100d89403d41000f00009032035500c5000009421800c04088541c0c0ca100761103450700c0d02e0800c4249440d02d200200040380b141d220030051144d20b500306040c1c070b890110034608106001e40500c0810b140340920f920094001c5030100d10f480020241520340d4404850541e142000250080c40480541300d0341480544960030800503405411143c0300104210011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 583157275 1250 583156025 583156061
    0x2030706180b0d0605011d0108010303110f010e160902090d02060304020a080307150e01090506010e130c08010b01020d0f1403060f100807022509151e0f09060b070204 73
    0x1603210401040d0f8008182810165a03c00f000c2c0304c2503800560610012150625482600c00108006001d860041c08060140310b4900840500711000300209210307003155800a100003802105140d54440c420204030004e40402840425103110307901c2503862061006108040f16100d940900c001c07940040c0050341c12002c001d00c0824000c00400c0103008003882140b90b581c481144040c008101c0f0b00070b40000ea040c0e41400302c04000f0a100040480c152031720200311140a450310008920643d04c4400014201e2002003000030740e2180640c8411510743c0c0c280c082d41d500201840003141c60b4440072a03058041404a800d04481c00305071030255a10100c090800303c000740d9444002180c4107002080203000408140c20484095410b024882c207012141e10030518100308905407410510301070240040e071a60381c0c000b107029880210445001000035604150214002b6010170803c2c000d14054980240161000083d51401c1c1307106100450711203004007400c141107542040094a00f0320003031101420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 583158525 1250 583157275 583157279
    0xc1e010c1b060801053f0f0a050d0906120b0310020f0d1a060706090f140a060e030f0d0e0703080a03060e01090c081f0b070305180d0203070618 63
    0x4080020110590101c04062034110300e04440100303060b0058001500900300090035901c085c00c60405c1090101007009541c042d409194040e41c0c0c0c10070300e4040e00003544610106095180408920240c4242c002c000b0348250f004415001d13150503005202d40c60008800c10181003907014203600541113480005c2c180c81c010769400f0454026a04401248080041c001460740042d080ca031145422098480c40e064680780801000150680580c5070003401c00b54886034100200700240c2080c0300d80d1030303000d83c0601c051081c03003040310380d202d4040004880f1503290000b03c1156420020603100c0e252414044685000707108200c49024107905111134059204030340e004000150b00201403c03408280b5500080c05920b409240e13894150181c0c0a031f0005460000324002540e8040710407070b4009913034112a11060120910146400b601754000c3c0b160080103e02d0008041d03102006110884550003600e00710208030342049080710300788034001d6055000a0341008511b00444541001411308140216099 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 583159775 1250 583158525 583158533
    0x6080c070501110406081605031614030106031415031c0201091202030a02150405030a0804020a17060a050915160311030c1308070308090402030c190905010e030c1e010c 74
    0x90203903c1014001c0d02c01041c1444081da201d1649a4400503014003440c0c1c2c41046000504a448003400000d00840c0503140c0300686c5014902c604c06103484862100d50300d40c1d540300c0040c02401491114040a21b10b40c1c003092284600300320080c00000f005016061441061403004d040112003d111390540d5202c1007101d000c603a2440c000c0980c0890758004d19510030030b007040203007055030541e01155402200c01c21321010850000590340c10006a0034030110726251400041c500714040c0d4444000c001a00d4200b0040ca000071544030b00684007030701b00340007a80315a008552548400c40080d8105134412000070341c0700351022020300050310503040008800c8203040228400b43d0044a0f11111001d0020702e010f4980d060180010040040101414a40d410341d52010002d100740181c103403203180c020000c100c034070061004a0301c06404111444c461840c414002610a088521415000c901c400c240403500c0d0801145031074140d407008140e42c10410b07410605806280030b5092040c108000c03403900b1400030f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 583161025 1250 583159775 583159781
    0x270b0c090f0d11011101020a020705040c09050919050f040f020f01180e0f091c2a0609150204140607050a050607020a0b06040c050a0e040b09192406080c070501 70
    0x150f00407100903441d80701000014100381d05025410009038410040d030743e105a07001c5103034001d844045501240b450005001112080115048139510003410b2007408032410100251100d400c800300300c00e00a80d0345807c1c0061110383c007107034050941c40f0240032036001031a010100c40c0e140d0005040c00310f0301c0d0320382c5080460902d00303d420001030501541c06003c0c8604840e255903074480c401500802c2a400c2002c20005440f86480c000c80c107014403d9030aa1401e26030100b0008141c1d88400080d041c0072030f906004000e801010400e417010000c500507420400641d000300d506a840d00050038042d1040c90050080e20f41c081f090035101809600d86060024406010003806410203900400f03007030b41241002c0e118110064000d80c415481c03c02091a419000016200121142d0401620002555010030040c16a150b1019480403001c02086404041c0200ca090b4100045008100d02c0c0c2c0d01184c0014900c0551072160311070300d00108200100d900c41c031a80d0358080d02d841240c9003000c000e0f1396040c1c29 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 583162275 1250 583161025 583161049
    0x50a1806050d0b041a1c150516080108030f070501020c060711060901050709180f1b030c0c0c050603040212060a060303030b0306060d03030e03090a0801270b0c090f 72
    0x2070000686408900214060585520021101000074443c84880211549012461a8010021540c2000b52881d40741d0303c0422450300505440c3c01e0361000ba021318000c12040b98440700c1c07a40d643c0d0705801207500c80c5134058162000640118070381205591040344035005a0380445503503400304000c441c007880c14005e0500410a03500c8040c1031054000b203003800c1c42d8000301581d8580e807520082200e016071015410341118284030480f00681024698000a856200c082c0010982400d502c238a420301241854900480265010000000329190480e40801904005005400b01e04418006c07464004d00464020f8030007020b000740034510303048036820020101e591042c504d983c1c0740d007001859010301030600c80724403c50241800b860003d0000c1c41c00483e031940a030805681f07001038810010104215038808800400b05881d0a60341c115803030203400c804514040010801ca044141904240f035418030290b40b0a810003001d40d10101d103e422504412151940100700410100035501c0d04006014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 583163525 1250 583162275 583162277
    0x2060d090c05180601030b0103060305060f010609091406060c010b0a030c08120c030a0e1c0606170a020312180a030f050d05160209040c0317180102070303050901050a1806 75
    0x280c0990641090001c0c0161980030758001c0c0c03840340c6a80d03412034101440b160b00030b4090074001009010000100c004180719040101584224400d1110340d903a090580c0e030494003266280040c1c5900c0701c400e00182c5d03054015000002d1400c50125044e80780240160112202d144d00000d01641844009420229190f006403089400c5580501400700180100c010305d04002e048030307107444c0203080c07040c0d5644079501c050003c016100088101564034070100002c0c034800c001250701d04070301605020000300094800d822030301e41d000f00c1c18603c001002c6080389540b5001006407004c0000700d5107100032030748034207110400322241c0f00c20b0142642d107000c07180010314001d0102c00e900094903e8130b02e1600e03070b90302c00c01c40900c00180944080c2c01441c110000700d0660603140080e80352118540b40d41101c131302d170f040142904104041c0110000d40e00c80607004045510b58503000d09100d083c01640c58220364040900010000c101154540d40250010500300342c580c0f901940e145904040c00c5810740098104034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 583164775 1250 583163525 583163531
    0xb06151201030510020a2001090b010b09281701020c070603020a0f1805101209050c0316051302030c0904060803190305010f091d0604030201051605030403080714040302060d 76
    0x80240b03c03003080140340c0a964010210329040d50b0f1000600034202c0300e400408481599030415100740742c00c0d0050101107500c80c40c54034495840749281c0805070004a41240190101c0b41200100c20b01710510b503c203400048041341640c1d00706408028282c0240b80325020540d020030855540100401c0910000c0c0542c0c1d400589407a140c0600404990f070800f155410002c0c200c1c0d06144501802c4060390403940102d4808400a8000348181e40d01403101343c0d450300d014078107070b90323041405004100324800f251700318291031260302d5030a5405072071b19850007141c0d00030f50503010660451035a58025908440c88080c040d051a032040c6c0000c00391002e94200c4413003038002082c42c00c001c0740180ca540c00c002e007050400340b00c29818041c0d00c601e942c1071442502c10007612420200414052101c100050075855020383d411032500d070034060301802c0e003519560791403c45941c1900000388120260ba0040e5810380d104400380c1c460900855039000a2480c40303482810400c8000b00580e01e280042c100340280d80004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 583166025 1250 583164775 583164779
    0x3030610050c071e0b04120c0611030d1d03280912060c03091506031e03020307110a051e12070f12060212040501020711010e030a0b06151201 62
    0x10100d0051148003900c240501071000300c0907000045901c80a5580c140c400d25800283c0302040d04480d14540d000c0b5580140c00200419003c90300c0a401301601e0040d000c00c00034540d0303580308454860600a4061310383e0401d0001030155241c1c0d401050a441100c00700e1095000340f02c480605542c8590400d4100003800d403480480d0040504101d113000002d4103281410503d4654001035040d01650001d00c8a5950303000d079103036240603034041640d1a802100303d00080058241c400014070140c00241d552100e5410181102040c01420103019585036000e942800c0da95954401c00d4000d25003400d91050092401040c59152424059001c081d540c80640c1035000d54010301c458000f00e1810040c4c07a4100d080c1c2884226000c9002900b198074401c40a85824410f052000c024040d108043e0351845101c0c080c00180141500070b060301c1030141c0003d038030b4402010010346000c5c0721564100d402d40c01c6030b148a0701146082d0006d552040c0090070803100210181c003545210b034000030f01e14903881000801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 583167275 1250 583166025 583166029
    0x30c05030d141e060d06110d020c03040f080115030b0703060b0d0902191a0a021213030204050a0b0f131404060c0f180e090f070e2406090d0c17030306 66
    0x1110000003c6500101004d041c140007050351000c0c002c0f805000c00b81c1b6164a9804000080111002000300500440d21807890f481074640303a60141c8185078004d8140c00c0017284003841840740d06007901070a07008801d5585581e4410b40041c000404140034180e56800c00504002c545c8020030302d9070504e00c40042c0e003103070f44c1c07040000302d4420700780d6005184502c240910508218118160710781207219121501c48a442c041207182042842c024013a00308089000c04d40002c0c0c1403035400075039208580c28451555a00501c1c401c441441540c507900c00000c40020307005080c04007803c201d0344002000403841000e10034903001c268030f013550200c81c40c0ba81d03101400041c0e54030022901090b2001d184c684c20403440d100300c40c0190f806500078494200795400c00700d020303110704102c3c0000406c18a000d945410b039a607021401000801c48940f40c03050003180016036007511091041c1d80001c00200500d052190503018460b00a10460088441901e15140402e030070829580c1c9110006442c001103a4926000007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 583168525 1250 583167275 583167301
    0xb01140a06020705092212080f0f1902090a05061b0607020303040c090b0f0d060608071215050a1401030609170307170c130f050a0b0313030c05030d14 66
    0x8007400464014030414040c0c2d50b5001e0b2019088055403031540f0310107089082c04c8003c072462400040968003186c1401d104e1540144201c0c1c49607980001c640445d42e540700300311001000071100e904055809a4940e21140c3c0c0320f84c040c04500c0405008000200d0321500820301c01e034441f02503a009800844500c0c40500d07010002580d214905201850031400c259581040104490180340810b545032084c0c020587c44000803841956002040840a100e03d814800028205401084c3c03d40c041c52070049205101d400044045c80e0780300148410f41800d1001c500c0007084080d010400303044c0c507222000100741c1404a49406140a104009144041498440000710603c8004d43c0b1a040a108101d401e54014401e4220020405054160781d81c0d500c4041200307100b91206456014010803020030800b905200900566609451036460a6121400007405001c11a604071092540c54401000244651306400c00c1a12130000c070b0b4141407844a08100ba25003451811901c12803070b00800c403010300b00d14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 583169775 1250 583168525 583168529
    0x90a15080a3507110d030e01092c0a06030503190e0f061801020a08040906030b0903033c01300201080112080d09081c02030c0301090c0c0b01140a 64
    0x11141c22041120303400b120484191007454182210004904007003442040ca08109000c1c0004011521355040313803501410b001501c0701d085001540304040401e00d4500c80b00c28a1400e031681802d259807d5510b40445242c00005105000c829120f0b40000000b542c100054412011264803081c203005400c3d1004180d00c280c2007405220b102544040c603d0f0b916031000303c89505170603116800d11440820b0040c1c7c503040b502100213280b05800100003612400315401581507901c503406121542d284c105105649008c141c0b0681d114060711428644001c5c0e030075820310340c2840302042451103c00300c00c2d07403000d40300000d910914003d1001400c404095862102c1f0320000242a5a441c19024a940000b04040814010350940d00d40e609040000d1104000548608a030740000604c1001294505200e0755000006000d0505601e500c1c0c81c0d40092107130087e24490f19a00c615142541e00c1c115000f0080c1141110280602c00001818004510f40c0384103940640401c1006005d0180b0910038040d02400c0d503 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 583171025 1250 583169775 583169813
    0x150305031b031303021215010e0a0b06090f09100b12151008010303050a03060803160b0f01080604020906010302222409090213050607060e160e06090a15080a 69
    0x2001440c10240000241c0c0c0f0642e9015100301c40c081e1300000c0704600d005040c00d0780c01c140114000c0001442c4e203003802c08510400102206101c2010010240200c900903505030b1607110098207100410740c00c00c0551a9482000f50040c1c2c1942540c50700100e20070362003900c00400c8904450104210a0003034a14520401403c2d200c10031060380860300240416410302006003080800600d00640768840c0c0c104001400e01c40b07054030f983c0d010b60b14190501c00030090341210710441100005032007611185a10b8100c0d0754020160139986d49030781c01c11102c21801000e0034180f690a10004012100c1c50b8403a10101200603108001a82015200150b02d00c1c1c0d509600513406003a10318001050748409510100c85c0c0e01140544c03525000a0360010042c515000341b03800c04d4010400318180b00c03080c4c0027144282071500903100380080254404007180600d019100541c813041000c12581d0800000b40b44e03020210f1240080c0c00b4204c0b9000c1d00220103164464900c3e80d0244003401c0a211814808990016007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 583172275 1250 583171025 583171027
    0x20102070617070e040f0609060302360615030403230a090e04021c260405060702130b091509150d030c060e030a03240506190201150305031b03 63
    0x3240c1407500b070040240140100310307141142075030039100c60708944541c490348401804002d8070307480d020000f0b007110301c4180d00c109218842d003100c5c404c02e0301c6540c0e082c101d03240741003c41484503804c2070b089601c0540103941010b13a003125000308010030000b55001e2446552481644541e81070b074004007850010461041d52400c0040c20b4040d41c09c11213407000c85245403414a000d95460001501022552070030100c813900c640c0b483c00802150340564040e803e031001055241e0705000d2140080e900031409100d411280810100300540780c000658a075101d409607010910081c04000b044600e141030b100501510b92001c1c2125241c900360036020f501030448118602c00d107080700c000901700c58407000f000d01407020f910104001c1c480301d5000114110000401c496841c4807440d4000e004008031030011400ac148003004102500001c0c01100403180001c0c0094203011141103a40b26250a604903181550b603102001941e40100079090401140140c020315299401404040310f80e041641010955400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 583173525 1250 583172275 583172297
    0xc050a080316170f041715130c03061a01021b1c260408011d07051207211101030207050c010e0a0306240608010b1e04081e07330e1005070201020706 65
    0x154101d46580c0001d03410523021902c0340504100e581311102d43c001900b82400d10980301d848038400050070204210a80c211040c4070000e640301c840000090344001d03032180e00444d071000f00e50143c0c0d1201009600981d0b684c64654451040d40c0141c500d5190968010440880e00300701052003841400220404003010729480d250b820401c5403580e1160152038440c5040002e4516800300c204000d001401508074480d070100240d2039442d520004c0b00204883c04164100c0d01072840d4400c2c0251350b900d9602c50014898190300800544401c4d40100003660000c81030317000000811158040c0700400b50103148100c04110220111310715980345034200d2410302c160280100650100b14003115000300f81c1b51810342800c4452000c00340c4600c44c40d4095039003403044283c081c009120b82d10071155000c012208443c2c03080d5591041c6650075030030f1518400360b907c5200039090b03200c003200f410340c402c13140501d0181030000c1101c1c006079407014880c4c001400590089036000c11541c04000e02c10180c201c504004002034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 583174775 1250 583173525 583173553
    0x250801080106050a32060c15060105120a05060310060e040b16020a06050415060803091f050d1d01050429190b03280c050a080316170f0417 61
    0x4e54407450070014041c60300e040c000305c00c1c2c0b5400d1700c52180f0801040c00b0754810091885507540c003038a86005c24603000480224001750300510407244050079401c501115540c803905400001d14000340312075014020780f1401c998003c210321412015004650b0301e041c550a140c04c10713120011009094040c0c5a4402407011230b4560005141e089590748080c02103810741d01c0b1310b0b1a00c2d40c0c00e1180442442c032810240c010940070310200140c07100e41c00036954040300c0491002c0f010343c203403545181500401c03030030440a02d9003012030b042001102030f00c0c4819451780000c29040c41c00c60f00c086030700760340c05003503000c0b405208041c8006044c000010314a0b81200da0400090b1410b421078080380d002003040c0da0b4072601c00c00d03840038000d03040700101c024000451603081c3d4500c034060340005c1034120b0300c0030024440442c480c40d204004600780d80e0010019410040141e2004102016224041e12014012031045984810100007000c1a6000d071800c42c0d102c40c0361015041c807402d80c1c01c0322030381c0c0303038001c0c5016400032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 583176025 1250 583174775 583174799
    0xa02180301090f170409020a1101050604060e06010c0303020c072c0132100f0e0d12030509070915030c080109031d01033e03070206040803250801080106050a 69
    0x444c2c1042d40ca1400300002401198240b14640c0a0b66035180080f40d050301640d04025401158406003000740000e035504010882101c01900070040740340b205902203005e07035105122400c49288242401846c01c030440362958600011544000350a00407404c510000101c130440380015007001c100c02c0318055041600840240d07100840a003041d100d8a40582c2590310142e2080b0302440018103441c51604260314020011208065030b8800b18248041020050401040c21400b590b0080c01d00a031514041d8000c8014003400342c4207038001d120f0601d01040d0741455109032540412001d082c80001403640c034004220f13402c02d5002d00030a03490401c14101003034101a1080030951141d6519107003405044c01a00101710214901c025020100b94042c040c03114400c0d01d0142c0d12041c01c414080183c12071607081e05200450320b000048e042140070800180c0c09601940e0043d40c0155205030101400c034102c4003018056000d240000c4025004204010b000c1c4900d034023601050320900d80107400c240c00700b0b401c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 583177275 1250 583176025 583176053
    0x20d0c0201140309060601030608030703020316290a051b03150402160c05040f02091309170f0a1d1c1a04080a0314060a140114030a0218030109 63
    0x5106416000104681c418001080070050015503261282050000c055842e50200c8030301e4040b030310b04040440c901c6000025201c941c1d070b140d07004500d42040742c10440d0f042c800c40c007c2250b829000140c40d41e280c807950301c0001240000c1d551b00c2c0d07240b864001a00303000d86501a0400417034403026002944a9407250045951105948a10005000c81c09001c40c0092248211000031101a1540b02c01006135000c80c420803500115428003c0c0100019030204910600c040b482d40055440f22504500f4130719000600101c0c043d130318044022400080f0069245c0c030aa10405880c40001140c240c0c19030000704841c9220108010080304041c60f40200b208071210402e0011041100702461080001010311900c104c00c003081841c100703003000e141112543e04501c0d10040400d04054218210040c0b4250561127a80020450410585051008007036130b1001c4034064104000b031079920100003d07820085026034400c143c0181c5d900742d00c80114403000440412284640d0600030820301044080c0c4600f40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 583178525 1250 583177275 583177277
    0xb10030c170f060703020d110a0f140d060e07020f060106020c04330513020307141606150501020c031f0203091606030203062b0803091501030b0103020a060f020d 71
    0x1205010301c000c500d2410540900b2600284076070002c100380c403a41038002e080c0c1c50500303007410300c02c074500d0381803001490164842d0600020f000580743c540e40c51044100d540c1c4041c0c0000114603000e24a1204020344000e80c2000d058201c40300d0501007081c0d81008101000c0990b940074002d10350401800944070612070700081e1141761180040801100781c0702d0006803a0300648a160a44102d8668054881401d8410107120b142d41c002001c40d801e00d80e0084130b01c144040c1d039a5900c038000043c4072030f400350000100661146070408504000401718400c160201e8000352131000454540800286081c0481140703500980000203031031158420401c4002100341c0e000c40243e141d54651842c0d0785045000b066103510a01c02c5c010003e52543c1540c0258003884040e00c20b00c0604000b000d0703005481e150b0b9502c02e01c10044101600c001f288042c1c01968004041d0000e440005005198440c50b501c400c0e0030903500c59615134010011864103c44003401001e09040054030b090014401030b485507000c013040d034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 583179775 1250 583178525 583178549
    0x203070e040b01110105161412370506030c010203040803030a0f0b06130609060306150c05010b06120a0e0d021b01090b04090b100e0a030204110c0d0c0b10030c 70
    0xc81aa0189904c800705040850007089540b515103100d040c4052a00074540c00720380281c0100076000b40b0403040301d40d01d490407a8070342c07019101e0255002ca805c4040200940007107586012890541d0604d08100c480c4040c8400819207081a40400d420300110440782415907204000401002c01c020066a50200d244280050103114482901c005007020f00112a40403000045c112500803044c600241aa0220b944142c0341c84d44842c1c06508452660080d910f400e1043c041001d000c80c42580120b448034450380012642810000110342990000300c00e04030360700700380360030080f8000951290710341030000714004050b40c030000c6001a403503440d6030008050b0480c440c244501d0ba64001c86001c0c1c000d080c81081c05035907070b50350308040d070007482c4074900d007403088600010b02c036041445103604420101d40204000a03881c43c684c01c200041000c0e500e81221150309015141d4849020300076001580c0e0380e81c071550400e00b424a041c1600c410010080c2c17200004050040c00401e001c0c07607201080d90000e900070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 583181025 1250 583179775 583179791
    0xc0f0f061409060403030216060305040201080412090e01080c15030403050906030a06030f0f0b062409010e0a0602060702070b1305010302031302120d140c030a0507020d1515090203070e04 82
    0x203151520948082c240c10500000c3d0001c10981c1c00692170090f012010b03002e15409403034039000c0341669410354001e80000c4541d00810003007890003480c00101d4405090901d59603584500d026102c4030b09034888905030308412600c3e0600d0038900ca20054900746075003224a0752a01d50b40c003500a001d4041818041c002c0400020f110001a0f03200388061134010502c040f2103106860030000d210b1001408032501540d01c4040f40450402e0684805841c4000001400811b0150140010351700212451410000320b03e010040719100e058401002d44140ea000d805949844900a032900c07000381d02c07101c072a00741000f00c1d240c041300c1c3c4400c0c1b00960700f0921700541d9a803a20f44001d0321030b40c80d503c4042d40c00042200d4039017500c803000a14150600c40d0f516030414154032018180d61030b0203551100004c5420803c003407440e20784290010501d191000300884204071a42d02c4814900203c1c01d0003178200c0c0e5a605502640d842c8060f000c000404100109514507c0d00c1c3d080101003240d07a6041c6c0c1d000c1c9469803d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 583182275 1250 583181025 583181057
    0xc020102030f04030c09140f07030c03091b0e0606030103080703030203040c1d0a0f1a09060102030c0a1a060d030c060b04200301150507030c171b0a0c0f0f06 69
    0x2190301c02c190509405484076102c2c05d015007000044c0c8607a00515103820002034985000d0b404281c440c41c1038000344180365480200c258064010464110105581c800001000a8003401c0c580e0000160030703140c1d01c0c0681070030322452003198041d008038440c05090004000140c81041220440d5505190142e1203484629050709285920b0300070b600c1c400c410000044a808000d4001d52254074011010b00c40d000072480700d401298010091410000d005030810521814a00011a0000f1042c4116454042e803081c80c941030042000301118030080c001c02c61006940c0c02d0311040d8001c202151074008012166401820f004130401c00180115107400301800680d5450380310344d01c8070300101040041120484d0b8102900e510900403403208001c40d880400b0340d035200e80d05564000342e00d5200c4481da90526111540c1280540c0d0b403038618007104000302d901061b940380380740c842c0542440003001030303046601d0000802c9016400030780b01924540c008100c3c2481207000503040b6441428150803a03520842 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 583183525 1250 583182275 583182277
    0x19030e100c0f1401151401170c0904020c1213060f0215041e021309020112050903030601080c0c0304091d010e0d0311070804080706110a0510020306120a03180b03010b0a0c02010203 79
    0x50785d6001843c4c4400c0c005002ea10314003506070413403000d80e10965003199102014410301e6091b1180c00f101007060160701c0c2d003401e181e1f00030a50101c951089070b21544113180115484d0f80402d030520815a00b40104202c0c46800078418021070801c4d0014000354501e210303040036140030090014002041c00c80c00301c0000713940c0700341d600d6009170013030400304003100c035007070b040e806840703c0702040f40064040d54918510b01e415205480c024440b503005545161181001141c4020004d45a4000d03c441009a100010001c00003440240042c02c0089443d02c400f046903140a100d21800807501d034100184001078640c0401c9086030f02090b403d0001c1c04181c60070710034640d0301582d80c0081941c80001404140f41c0f1001800904480c515a11004080c1c0020000c9840d4012068000c0c8503a01c001d155040c1200243c0195a1022000d8034903c1c174440340240003444c1c80e204000c15400315100316800006903200b5808a4003418031100c40d68075551402001035101e21404c9110340410000c1d613540400c40e8400d02c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 583184775 1250 583183525 583183541
    0x30318050604050706120614090c120a0906060519170a17130602030703050304020f0f1804031101060302030601031712090313090506060d0e19030e100c0f1401 70
    0x50225101ea281625116a0340c00803805500d020400300e9921000c040500c1c050b04c03080c0d03900035115007201e5040c01c0602260003005020000d103000300b070102e42c1d1904800320000c1d1041410000105141c03406041420403a80250042405005140000f0020800d9802e0749002c603800622440760a5020a04507810401454802450100340540003040144400003409140030404800105551760700004d070b07628400e280d40100812018400207001d450302d103500168466024018081405144c80040c854082021301c402500c1802d80c00d00c801d06501c144d941e690301c2c0311200200b14903411500040c1d038a420520000380405108080c407038a06d034140b001c0c0c40c5010318444c0c6c4501c0c1c6090001115403290020003030b101e070102440c0400103d000403800f40078040c041c081e01c1a441d128014140b04091308407500401d859105210703a0b042e51100100703c0d08811070107541c90310708050b20f030340c1002800a68034481b07600f0002080c240002141d03a500742c0045240e48100350a84105030540c1c1e060241c1094 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 583186025 1250 583184775 583184783
    0x307080d0302030405060105190311360f0603150604090602070b180706121d0d030204050f03010908161109040b06010201140c0406050f0409051015020c0607030318 72
    0x18160955016070036802440c021071180c01601c01d182e80b22820b100310480e007c24995540f558200e02000854865002020020006407100f1840d81e2110000360b40c0d204c200c00c040c002d03116160071041075000740c40389044d040305601c00c500ea5981401c60000f503035090000c2040f0070000c145000b20305142d50b5a0b03c0f42c0b002c242e00031000d544481803420a098040f01c210390100d0042401480e40c5100d010100d0090107990040d100e940c201204040188010000c0c4080c0754000d20712040e130340b441441d00300301e98042d420003990050303611810030f1b05102200c80c6a04e5050b000780c8c144520031002403000011b4404030401c14600f10b105c00401c1c2845500103600c14184d0b40c108664009100a0100f155851071289500303030000e100b01d5011308020007800170102c510000780442030000344500351040e0010720000124000030340c246a1202034450807541c0136a0b25243d0050420b80400001803200400c0c41c103045940040d0282038054000701d400e0f4410f44000a00f00b59485e0a52800c0d0110000014003250704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 583187275 1250 583186025 583186033
    0xe0f10150f08030316020c03030d050c0912011b030e030a0c2303031b0901020d0f0903150b0f120a020d0f06050a0e0c2b03031b0f1205150f030708 64
    0xa100c0640f0b40b203034002c0d0b40d00700c00416085c15841d80075000040010000001600440c507003520810b00600070720b0094500790844d00e0401c828021956134002501090310198000070711407050420740742038401501020401e1504102510705400c5012003520380c201c445061543c00ca0340d00345018820f0000341030307400000e10603440c2c110403c2e46002020314440c000c600c0c0d070505c61407003128210003a80203240c0100c0c016444540300300300c0035101d000442d480900600704404855125a10500180d141100340111507564408041c2d00e4a4004219640b1150540b11700e0a070150076040c058a9800000b0f01038001c0c011180d1300c1040004102d4640c882c05d0b00030314100440e0808090740e001500412849070301611901c80481e01a24004501c000c4100c0071540400000138203190b0001040391814050781455515501151540e007290703400c01412101c0e07541c5112a0400c244042c0100e10040502e56440703150200304404d0828464405c0040c91003121b184094041000000b4581450743e0031035406402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 583188525 1250 583187275 583187279
    0x1090f110f0d0501060504050303030a0b0102010e1e07060906170c0906040801230115120603020306090d0305010f0e01210606060507140a03080f1f0308040305010e0f10150f 76
    0x220380010300401c2d8226082401113981e188400c66250040e40101e80e495002000403410b000c00e142e100d000f1030501800041184800d4a00441c240008880121400b01035500500c0c0e042c6018040c2201405140c00c083d0601ea081502c0244a1400c03864050504e010b80400f1070748400d6840241c1c0c11a4000801050fa92600c5200043c0a00709017501040ba2406444082050310110364107070307043c1c440e070150450545c4c0b020700088400d81301481c07481c8600c0b030341c800011000d604c2c2400018800e10aa0000b00301d1000b81320710050071030380b05034089100c910101205010058415680d507045442c503403105c81520600b8140c41540c8020004001c10403403a180c0006480f940040c054258035000b440c2c02804210b07401b0646468610350100140010700742c17400a15206400c280460f000f010b03c1007080030b5000080140c184440c0c0c9034200780e40c0000003180410420809010b803d65003a4000701409040303940400040c2c1d0b4040c038640d00d0403c0380d26a1994a403c00b0001d01c04002007400d040d5021540b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 583189775 1250 583188525 583188547
    0x1030311161503050a2013050a15020d081515120109051005010e0306040609140105010915080d0e060a032007030801050108191509090c09051e01090f11 67
    0x40401c030002c40d042c04002920034540b032040460706ea03001020a00c680d0342800d0352503e039610840304000118890703080811316459a2081c24050314070711a88071243e044420019103801542201902009a81001c015418140c440800c0300c029050300d041b81e10100700708a500751805090480d0a00c2640f4200000d454407698000780d01407400007840341c003815168001140c5464403900c659415a00220200d000101590b10021806000703510740d2141e1180c0382542400c0d134000380d01c2090340b0358641003040d00141c0c50841100050960100600306100c5018005c0c08810303140e241c00307100c1e07000410ba08003403e00a0f0421295890520101600600c105500712a41e8001d20b206400092140c400400d8550151b4000390061403800707650210003100c015010b0240c601c00c40420f0300382da103401001804803028021041043e101c0c4100041090610035544101c9030020300000e0744602d42d08240b585407030040070240c1505c1c1054004203c001d20518800c1c05440c858500c00c810b410000343d00d035412 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 583191025 1250 583189775 583189799
    0x30f010f05060724090804030305130e0103021e270414030412302303070c020108180a0f05010b030303060a050405270a05100203070203030103031116 66
    0x1a4180c000601603064950060010501a0070340c02080ba4070184010110412070b10f005229060000002143c603d00c50380c0c0d882075980056004501080000c2b49400010f10845501409095480c207030f14900c0d0324580004014000c0611411605482c4440c5c81000c1d4031030b454400e0620307a0f0300e100c102a15100070210401c0e1001100c040d101d401040012190441004c01110100e8820703d00400c450300c5aa01d8a642690440300c01e01003000ea500b1082c031068209021002d02265940c640400303009000e40d4001d50505441e040130b20144081040109144e080400c440c0d005e6028601202c59903248208484080c400008030b041d6071140541c01010024075032680c2c0d0503184294000e01041643c0000e041d030702e000a545041d4401503c4c9002c0c800c03418168042d95000a11030030803101c0a107440c07102c00220001d0101c015581d0040000030007880400c1165402c1560025421451481c040e00b0084d00c1c1d0206000c020108a1881300c0b520100c0380410441c000090100b50f196002581d40ea0441d0300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 583192275 1250 583191025 583191029
    0x1606060602030a0e1806090a140c0306010f0c0507060e0d060237020a06050702031201030302100c090e0412210b100810271a0108100803090f010c08030f01 68
    0x20010b50744d03141c4070304020404101c80e00069480c00c0301078403102d0402c81d40e41c000030000c000302e03940d4440c1c1c20308001180100b40c1c050f014410100743c1d24201800010b000500041d909000d22100601700000603000003540c1040704c0c020303d072002040c01d0010008416050100d00a04039038004601001e8031002c181c0a00b16900720045441d044001e05103c920002981c5a441e0300560026415140480e5542c4c0080703078030101d00c0c0b040e00e145c022503801c2c48591807000c1e08184c00607480302c0c0010300c005a0b24890341362600c5160404061072803400f80c045048400080008240603881c56590404502841c0d0416040155504040d0300c101070308615801040c06071000d80c420050090245c1d8124068010b05001e61190f014140800c0c0c1445003140f8140e046004000502d821888014021143c1d445600c910310b88020040c0301400101700010318a1030060540c4c0d007000050300d02081900320000032185144011b03503043c804820058016140b59190b03020280c040c3c5400020084818400a03400e81 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 583193525 1250 583192275 583192277
    0x200301110d0b0108250e0105040815060102010e030c060c070c03020a09140a0603030c030f0e030706020f0d0f0923040212060909031603030b03161e09020703050306061606060602030a 80
    0x3541d11030300c90710303100d00283e560f4000701134980305da24030714078451409120a00418108035181a50350301005c0d00d803c042003101c0707203d080d008083c0806981c0c20300500404003082e400075810000c13451461902c4d540d02030540e40002e6400036101c4c04010000400e440110380041010f0700003951031100700c020f0305080105d43d450038142070000d00e40009070310401e4140c1350141d4402e146d580c00c555050310b903418415980c80910180d101401c500341da04015800103001c10741d020300041465001141e03c0d02d00101e000509000c4d8000562804503480741500302200c2080084000300c03000d9020550207500010880e54115000141001e24a4651a00c4c1070140c0c1d000d848820503541d9044030300ba143c2c011036110000e520700c1d11000c940400e1180c1c000d0307401000d000301038034015020030f0014942e0529507403162079804040c0c031482d000118003e4440e0020300e188901136113050215600100320748001042c103840f0f05c4021440d41d5502601e080b5014049074001410003040361195030103981d9802c021000d030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 583194775 1250 583193525 583193537
    0x280f1e050709181104090204020a0e0f040e1207061116110a030201120e12030f060a0e0f27010c030501210809010e0312070b04020109080307200301110d0b01 69
    0x80ca611661190801c01c0c90002c0d119040c43c0d640d503a94004483e0354083d02d0740c1c066103500821000da03480c0c0c4014095881d160702c0705404d001c071a10a00c11403928100c1c9581c4031710701d4661340403031503030f00803170a078000380c08c46184555114480d242103401003402e01c0100c034040e200403450101e40284a42c4205c022409400b04040360080c507020400746480c02d0000a002485494030118a1117070b039000134034001c0c0c0210503250400c40c1041500216001103981600031002070701031050900f000b003c00000782032260131000311351a0062141551f8030300a0a45141480500c0148510341603143c0b10094a2030030070002c0c0481020000300601400382130080e464416101003a1070300c50150000c00e1659180d100e041903060404060043d680107e440e4449605070103581041d0005a08000c02442158416011083c0c00d08090000509188040d000003100d42d0040062070040341c10380b100d030100754a5010000189103c00c202107409488518030146003d040490220304000068000d003600440a036941 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 583196025 1250 583194775 583194779
    0xf031a0109020309071e051507060506010c0f03081302090708040606060f02070e0a060308040312170f060f0f04230a0605100c03050412030302090909280f1e0507 71
    0x40301240f0050701e44418036444500f00b0440443e07040d000c00c592420301103002458540d0f60010070110000f00e5407020141000180c007000300400c604ca401d070070010030301c0d00559501650b0f0340c2d40d450140089018007441105400a1b42100c40e4407681e00080d03901a1100c0300505000d2009040d0740c00079501203070721a04105010861a00c1991030b501c06a0300c0768020140c040c90020b410300b5010004e40228001d40e11340750048085103c1400601c010b42c440da4907000c9840702c1c020000d080d920102482242c5055500034090302c040300f86002508000112200d550500c45400050403403410034081c1504903052a0f036450509043c406144c0b001110000030350300c00e941c1e503021042103030160b00440b50700c48850860800e000e407107501841030440c400e083c580e00e490344405241000ca5030786182140041d80005408016041c0400c41c960800060401000c44440306001c4180090800e842c204080d030640500500340420341400d040d299410a402c9000210812a4901001200401541d1a2040c5000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 583197275 1250 583196025 583196039
    0x101d0c03010e070b13120503071b050a15031e0c110c010c0b0a0209130906150b0a030b0613090c020d110c010305040203031e09041109130203100f031a01 67
    0x300701d82c03010b4950241845500f06203011180d0b0b0040b142c003101514402001061180807078016036103140c02000110380320302c0f00303160414080c116018060751030340e9482e00400c1542ca8507800300b010360b0f04603071059420f40c0e1850421001408520488441240d59101501c507141c15035210701d003e40001da50f440e444002d0715103103031790791507580c40309500140e41c03403d4a4021803001c080740703904070005050140ca0300c0d040e200050f04801000c20005c14907036554030f5040030480c2510a03044403415065040704141c2c070301482d0b80014000c910103402807513200c107070000c5640c3d101400c854140c412825680039141e00c9030707052801018200721950241c4641600741e01c1d024050912010750009200080c50143c0240340110040e12000d08100c1c0c042c4020310803140c0b0b24a0044028a4089090001540740e8032801c04200588200841c00c0c00b80160400912106880c2c040305110031000040340580e0b640c5443c840e0641459803648910482c031100078000c002c111140ca00a4161180413403072600698031440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 583198525 1250 583197275 583197281
    0x510052706010e0d0506091006050919020f0405041a0102010c02030309030316261009020a1b03110a0b1b0c0613020301020d2c010b0109090b03101d0c0301 68
    0x220404010050a00041066203e6102148004400351400781d14a0307980c1c0d14107240081c1540c100c041030f04001180c0500c1e011510512004040441781c9052034100000120321004042c42100801c0d40c00107021002d80704d0942c1210010903002c1c00803c20424003e02000e4441401c41c03200e8015401e00460401983c4000b0603a8042e60480020b5440d503200c846074404601c205012400900403d0b4030002c2c0d00e08080103111210302c8171200c1601d10b03841c010108140d5407800390041542103205010214203a98401c0c148080f080c042c007400703217956070309083c20b07038800f80744c1919205244901070311001002000001580074582c0c1c00a05c0d646400500c2c4100d2140c002e4429003002d50340142c001805040300200c05a64650000e00014505061a4516415650313500f10f208840d108030f034094460403802c51702c404c021591002c000c00460040d00e00090521070144a1012081e07107984403802159010301c44c9002c060240042000184c4507004480e248000b007032000e42aa001c0d030b000d08440390030180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 583199775 1250 583198525 583198579
    0x304030206030a0903020a0204020c0c100219031d0a08031801142713060e091506101215140a0303050a11030c060106050903060c0f071401090501051005 67
    0x4151900b1556459400070062a6440017074046101e80203c1c04050380310752008290508000010704503411080080c407a04000c2c5240d8041150720010505480e0011000c241c000e0503494601090f00c410f1064004e540b1409140304250f0040007203400284105000004041c00488070307100c2d1254803a10382c010b40d0801000b100ca0403034043c041110040c11000d00d076992400c98801110094090300e50030104008810714199007080039540c20082c0300038803000c0d00c1c2942c4610800700404907003040101418201e007024180d0760051a0a041a1001e28001c54100646000c0c21404100d41d034140a1030300e001d41c501d4070030040c0700c202100c1c0303070030080c03c244591500340d83c0c040c0c403207915181039818120382c094502c8501c1c40f141e0106020895003410207000840c0280306075551142c683c4070100404d414000c2c0944400355080d010040ea04080c1d03006003e440c61260400341c0d01105455014400d40034216252004015501c0d0204202210b200d400300c0ba400e541c415644030346041c1c43d40e441c0120140ca11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 583201025 1250 583199775 583199779
    0x2030c0a0e04151806092306060312070f0f150e070501080a0b010c1b0b03040605091c020c011404270b0604181d07170c0a050d15020f0d061703040302 66
    0x10b20b0304000c2801d41d0004a291b1784200540100001c80b15110081070050040709000344e0062004d100552030304011083c10351400030100c900d0010320f6600c50341090318204006240e00d030707200b0200c0280301a09048a01d18104100c00740050b26041140b907131a48101d00070036010450349004901c040d4002c2c81400c0c01883c0603154541c0e0020301303403240ca41c02171001c281c00304456014074010600f904020040e5000d0b500c01d2502140340d090a03101036050030010782070400ba580c26440300042d001c1d400501e801e030b43c1e0001e00b0283c00300d0f90390401d03a00d00c2c0d00c11070704010701111000425a14965240e40e0308604c080b2414800c201000c541d004014441c45075208190903a45802e814000c0304000e603110004541c4000780c0784814041c0080d0f201c3c1081426070001071040804e0594150611b401c0c02502901c1001b247c1d030f40c0541703040400040111000070344c09000d962207002048442542c540c1125010024880c859031a40c06d607603800c4000e0130060003085602c090110408005100c004142ca040c2e940c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 583202275 1250 583201025 583201061
    0x91305070f26010f111903020c0a150908030405060603160803120a0608070b0d1815021602190501170f180106050a180c090b030a020702030c0a0e0415 66
    0xc2c262044a040000341e400c2d50b25540c400d4000c00b032060038850401c10800c00908035895801805075810700703401c001c0803401410300401440302010f00100d201c1c200a6840012a680b242513400e50000a18805100500d0440000b0500007400303400190244148001c5040304d44d1149042c880e100c080030180705030410340e1b0051051070060f1440c600c43c242d00100301800000d800396100200c0d4907001d041d03484489a80c0700000c0c211a80d01150044011807445d8106c90381c0034100da66070781e443c4000c906c0c02050520741c3c0420f10381c80540e012009000e031a9001000d030311700350a800d61440040701c010b2040c940032a9040301101c0750300c007002041502c036030400c0c0180030403035450f08281003110200240600d202e55981038046010f5442d4020b803406481c210810300c80e82c0008215001c1210900c103d81400d0101055040000700d180300201c3e640300c0b003956009a113850103840030032710b80f4031903e84e640da11413401907000c100d4040c865030052240380100c01d0107145100074807000c0226001087c9110701228 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 583203525 1250 583202275 583202309
    0x41802131a03030a0e0a1202060403031419080105042a0f02031b0102030402040b0d2411030c1911030702010f14070c06020f070b040312020c091305070f 67
    0x140541c030424914038000031000607082210006410365125503070b41404142c0c030401101050410b45100400391175020184400b1029580015880d80190321008080140c00d00c1c2c0d0080784800036083d6106000c1c2807201220007403d108000c1c005a04c00d02030303e80281d1030170210720381108401004005000d40a26580c07040c01d8005000c031740c18035030030741844150701c03040150002c04201d001c4646010b2209000050b124146841000103445801d44114414641143c000300494013001c84003100400032000d50308541c0c00703c2511806451064120031000c8804010442a03a40c2d0000a0038040007210030340140da031200b0015600178504181204555005000d10b00065001c0c0b0408206000581081880042d00700665206079004100848800c12000400c2040580410034180c50a816034040c0021608096041c0744a00076440042d2104c154a05208a00380c028000015880307400b0700640c850340380c80184c855860120550844007031155040000b00c6448081c0d40c01e00341c2d450711048800d180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 583204775 1250 583203525 583203559
    0xb060d0812070f080703052403120c1b06070507060507020103060509070c260d0f0204120b040b010801201e0a03060e01090203061f02010f020d050402041802 69
    0xa04608011140160204081c1400900e04110284205030594510364002c640090061044102400f24003c3c1410001030256142030507a6001c0070709210903064881107280c40009141150030080148101030005903420010800701741c15031188140c3c00001804450401403080c240315140024100f60807a0310103200c40d40c030079030050029600500d404a80d458451002814441c020366801c004900310803096000c02c0030601c5001950003a00014802c4101c001007202080d100c0c8404c2d006616540b21891442c04801741c0c10345003c0c00c03490707845042c0b011140c42e11814444041e40e007a500c85001000004424405010b040c01c082c40d6420700902c1020b001820401540008a41550304a4015104406920500054500d5200994001c158189000b000805403201038201242d40d600400400c60f01d0b8a400040c0c0541c25028200548038147c4100308178014207021900b00380d024000280d5000b00c01340741c1c10090140b40215803c011019010b0f14141c041c07842d50800a40201080e440c0c11100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 583206025 1250 583204775 583204789
    0xc030c01171305030a0e030d080f060f040914210f0702060c100c031508070f03240213030314030402012f010509060109050f010803191b06090b070c0b06 67
    0xc1614201c16a101c02d96503000e0554000300710b40740004e01d4411401801d0302e0300b044404509485420b0914880c142031001110303180b4014412406103030841b0384003019827100e900c00154560840e1030b200b0201c2c0c0e4800382c0f80e1a170310041c1c5103200e4543c1c0400b40c0701d12030100034100c48207080c21743c0d044c1d480c086c0c0319428881150841801c0c3c850344d010340c2c003455410600c00e000340400c0700115070300000c2d04000c811110818400d55000100c0035840f0381d506000e14103d4840031000d0303903001300c0c2d40e030000c21030341c018500724019404000201c10f0022074451041d118100451098902c40d450751003100c00d1242c1400704500048078083d000811700350341b40c41c1000342c803810402c450511140400050400780c140c582550b500351041906580028010001d42099216541d00241d2000c404c2c507865142817401c03540c80c021001034400c8841c0500302061002c1c002d200c076044250f0000b04020401c80c4d6400e0400c000e101103002036442003400f10004c0c000324801c5494075803141c0d101414000da510b854042c4120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 583207275 1250 583206025 583206031
    0x118140a080f070303030612030e120c150703080f150d03110a0c05030d05040b0f090f130c02010b06030618060a12050d03203108030406020c030c0117 66
    0x304010800115011005000202e04502c01c400240499440c6250050441e845035000244d200000072018002952080c6c00c000c1101007210100e003060a1000303020700b805c14140402d50322814158620110011030030140c450b4500a441c0c2c40f030302d0390760030300341d805115007c490750300090311078806201c05854092500321200780245400c0b094881684503080ca03000c1e08500940f07040710302e00401c101c1c0386010011040501e18034074002e81420701c0e02e03203014003d0160300d00900c44240042001481521401c0c00b020750f40b20020042602c020600d05203000420217071010740c00650801c001030031503003400012240901c10107081041000c521880d58841c8040280c03405a000000b00000282c00c6a00000076280038001e102500000c0c0000c5d1780071b01100c2c900e29841c42070b608803c0314030842800c1c240543d180070102501c50b10300301a410804d24140c000050030034111440fa8207011030003200010150003941c0b401d800310b03280141003504040d510b010419107507000501c0e50702c110348001c1f000d19150350 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 583208525 1250 583207275 583207279
    0x30b160c060203010f14040b0a0515070605240f060301060c0503090607061b0c080d0209040219030c09050924010513060e091806180f061f05011814 65
    0x3009a941c0c0c0d010180e0384281c1c0900f000e241c42140a104041c0b0140040720386200c11a0304021410260003c038800b054103115180c402c1180e81000e07140a541e941c120303548264441e008120f603241c401d08120301c0800b4040c01e060300b210380e60346800d503c0c10070b00035010242000802440c156840d043c01110450450001283c15000a1247c1d180a441d8000640344141c0b2500000c02d04099051714140411961407602c010440f0280200021950480484401c00f81390074000d40e8604080c03005c134005e4031032000640d404010a00c00c50302401d5065200c594258840d5540e020b5047c0c4e108100142c01200b0750340c3c6802d203801c40c085400c1c0420040004840302106040c12820100e00210085d411107140d800030001ca071095081000c28a0a180140d902c000318110b804c072500c484106042c0d558000030543e401554800c0040030f9114403c001c46103101c0c00c030030700b16081480c10480c210f0b010740d10030084220340222810049003c0d03024818400303840400d41d00d241c02007890100454403413078031042d40035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 583209775 1250 583208525 583208537
    0x70309051504080f0f150127060803071a100501020c06030a0912032004080312040c0b0c0a110904030c110f060a180b0901090513020909040f03020f07030b16 69
    0x1502d80420710144d5422400c101c0030f0709480601201060030182103140b00384502e14400c00600c2510038468050900d0f1418008862601745010884002440903400001d000c3c84041580020011120460200403032075444107030381503d1342c04c00c40d0701010700ca000341c501582040624500a040c1140a558040c0072aa0040f074407441c25114000d0528000840d00c00194881c1d0f0180320070740c01802240140103d00407074610300780c07414a4003a1280501c0d80745a020b0803e0101240c140050502c2e03036006441001c02c0c040e0f83d1880400095a60608104121a85400d91985055a107070a0b02c51500c199010303190148116580d41c0c440e80160f04d0805c000758000c0091f024031840c0d80f1100e020b070501030f00588039417021101d20800b17008844110351084000703220030411014666884056030086440541c8c10070041c0342e10044103000790094180d096084045d0300100014410042003080f030640c041d07001d5500c401010020961526038030b0002070525014417001c221450759080007001445580e107042c07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 583211025 1250 583209775 583209779
    0x80c01021506030a0b040312060f033809070807050904031e3e07030201210902030d0906081305030f03070e0910080f011413050a0602030c0a0305010b070309051504 72
    0x401c2100f41d4041e40011960304003401140558409c90001d000d072a00b0b4203c0c0c1c01c0c91940d80c402c12102c0020100d10040d604034085002d59002d1200b407162030074418140c00301e8545400c41968a0721144a0f80c1518400c1c038100041d541440e01e034080c01160075a5440070300c45151f00464010130007010300310341003000410083c00c20352107000103444481c3d215402c0d04440c41d0946490611255410070a06443d04107a20400040c0e07044a0340b03e90300c20b003040e000c022403000500e50000a000b0a00044e4050040702c080d1150300b503020301c03144240c9a0503180d2034416102e0f10000c07040106090001082c1c3e070f00801507a1186000e800286501c80418035298052144035400318901880076940d08440c0a00a142441030b0901400007000d15091400204500d41102c12142c00080c006006009401c140e040c2d040d040c4401448407070601604034005560302d0030036403504061540400343c0940028a40030022a02410080c00c4652254140d60b03042c2c500303406d010810050180440117208038076810040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 583212275 1250 583211025 583211033
    0x2180603010c17070f023c010203160f0e030f01050103030807092d0b0d140a0c02030301120515040b01050906010e030606100e030f010605030c1903080a02070b030a050a06080c01021506030a 83
    0x1013110f03885420501c0c1144047c031610000074100155940d000e900510803c440071036140b03a180005901031400e1407090006410035560141408a03071034250080d072401140c81c0e17030150030050407203201e992040c0455403000d4080300c900c22140125190024220a138201c24014000f102596402801c00d01d688207944100351001540061154200180c0310b44840c0117000c1e85000990b480b01d60000c0070b024405081000035100c1c4414040e01c2082036a80c801c5106100c0100300e405401c6080303080500303c900381030410785d1180c0000d00c1040c1c401c00b100700004615510616800750700d610081c00803c0d0719111007041004400c403040d080300030011612922080da40c0c3c1000f0385103621107000c000165083c140414141020003148803103004504060407142c920404144200c1241d400890b826143c040310300f400ca040070010791103204400d07804014004107540943c4228012000910200b142c2a81c803a41942c54135540403a280c05a0041d4030b88400a801c84031840d0b600c03500c018183e400300f415a590b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 583213525 1250 583212275 583212313
    0x4a0405060d08180d1506060f14031008061807051c030f0212041806050a210602090a0e011809030e0f04061d040b130b0c0a0c02180603010c17070f02 65
    0x1064070030303001d41c80c002600c460446c450305016006034070b40b16042c0c442c0c51001420320103520002c015290b90000014440c0c03046c101c00b0300040c180c0341c0700780c800c103042030780d4003c2c500784002103204c2641c025040001414904000c84c00c1540b4400108125030800c1528180d0b10100314071444401c1d030090311440428a00c80500400250081180380002c41860f5a903050031902c0d02d0300018043c3c0c0314003c0034403015108040c86072b40034001419414072100645400300280c019500724581190b040c0c1c4010139070701c0040c180c0702c0c181d0381a903e11001020004c640d91007601c0003004050041205584180304a0811104403402000040c001098059403030440106540e200702071110a11051010321040000303440c20741d504044161084d59070b46009450f5020281d4001c2c180d4142c40300c000a045450500074144001000e40083c10900b044070b818082c071404040c1100c03414402c0d403902c42ea400c40d950190b070f155001e08a40c40400400c9031348604098842c0d641210342c66055104010742c0d0f58010003101 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 583214775 1250 583213525 583213549
    0xa08161817010e0102030c04030b09150a0b15070201120e151801050117060a09030e04020c010e0c060a17040501060305030a050c010f05040308074a0405060d0818 71
    0x400500980c11004400d800c5030843e280e9110640d00400c28402c680643c8010350341629004214014030744c4480780c845281110038111004207105000c100070f00d15405610100c540034046e104008424804501c1801611907010008d005ca20410018040305103141e01542100011800300c0c0c0c02d44000d2100d82c0720803070f4111074801c0001b0010484c142841020300880b8010500140da00c0c03070503000100190749035200108241000703a0f4800c3d0303079814903200754980c118503500680210342d2400742681c4240a03040002d0781551621410440b002c413410408111500310b441035843c0d42c01030784500ad0500d85054090401e5130b456480d0380300030000c0341c02440101869991a00c0d0b035a40d4104c821b8886080d50201c601d0082c88601c0d0000700004a074118840e140e0041c800c1c5050724000d0042a510aa00f02044248010680740d040f130049410021003012010300e100905510680311050f01000195403040342e680b034008400603d0b210003e0750b80701c00b81c055076400004616120b0500000301e01944d0b069 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 583216025 1250 583214775 583214789
    0x9040b060a181b0503010f0905091c180b18011407051606090506030c091201090c09060e0901051501080408040e0f0601031a0303091e040603030e150a081618 69
    0x10f50070b145002201c0c20044260600c0c541040c9003558904034500c84403200c244a105a419202d40010b10707400e00c14000001c900d051780d21404461041c69400910100c6c02c0381a0717000740745141b003001c00d141e075075001903490308942600f4100c9018107078001107540c0c04a9081028980c4070074001503000403400d012819140c1076580d82c00c41d4035032401c000240201d00e10b0f4050781c018403081090142400d03a82c0211800240e080d180748020304518400c050041c151244068190741101c0008204620590407190441d200e15015010303030785031040c0c028201d41d82aa29400d5854072b4565581c1760354010342506900600801540303080c00d40d00c0704030444641c1c04490b05420340d043c00003044003030f42c0c05200c3c803c2170301e100142d0102c86290342c0700441d13503d02c44c1000652152080c10315040c0c4806466080f203403074100c050410310680e41d903031401038803015a480e40548540404a010585014200141c8450141a40d590426078880100b0709003007402d18030800080200f4415000a5408102001c00091040e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 583217275 1250 583216025 583216031
    0x70c09060b092817030702090f090f070b0703140d02030702071d070c080d090501060b0c070b0a0203040302040203040f02030a050c04050702070608190e0a05010c03051509040b060a18 80
    0x5290400103026414050060a0035000e2202411030400000000070356074503a0130203c581090a43d41c502d54061144000c0d07111000c402001300c0b0060314401d032405401588101c038410070042d22040e032204524003c01012510074810300c4086403240300510030b114040e00d6103505c0c262007640c00d201641c1c411030340b07400961b100781c0080100b201010b04c144003510a035010014141040d00c0d0003020000d0309003007e01003070008285040e42c0d10255219040c0541d02030008c000241d138441d1a80c1498001002e50203450180c2180003c0e0799412034210303070000c1c210b030740030b5460142140c0c00c11009400141003960140b400628200058404000038000107005e50020300145021b8410170060b03034001010f43d42103410031101000080d8104000d5900f01c9a01c03d500b110382580140c491000700011044075030580319240d8840103008042d030200c000703c140e6a500340040e954154940d100c0603408000300350001c1c408000a004194a161580d811900090413051096aa43c1100e00010048070250340040e82d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 583218525 1250 583217275 583217287
    0x2a060c030a0903120908150903092d100f0c0303020702090f040224070f140a12080106081005010e040f150906090c05030c030a0e03040f08060603011a010302070c09060b 74
    0x708544100013440d11600d0a44074060410603115181c80449150700607901800340801c113106800e00542d11085030180000c0c2c0d01c07001d400400e00700140340c1394100f41d03454880c50f4404014240481c0710000c02040703451310030908426000448140c07000300d00c2a410594244a200300581e40c1e00031090155041840b0405281094010070000e0360784101c1c601c400c0001225018010110302058504642d045200e10446081a060820400c605404429040c0c014a500581005608a0701c5416050aa40e0341d88036a03884190a9440300020b0b64031280017030840760304010390b41c819231b128042c0e2400500040b6400d0039a00690060300c803c0028110110210310081c00a18040e01c41e00300248020982489070008104010742280700103050398841000000c000b411009207a002031040120030012a035850750740c0e94154154500600507c001f501500001c1005450140140500200025803c500303070030110005400070351010f041200c1001d002040010f101d449481100010821540380350740e614 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 583219775 1250 583218525 583218533
    0x7050a120603110d0f02100c031202040e19020c1b15070206070807080f0f13060f0807120b09010b040603050c07030804020d1a040302070e07022a060c030a0903 70
    0x40155050030340141ca003000400100b81c40303404003005020103a0f04c40300c03070343c0481c10981c2802041c0380c3c0c040d400c5204103403801103050b0b01c8605130003068040d684d02c942c0c800070500e03c082644594440c403480c100055000c00c40b144504000000e1504214900520b0410390450a6080c08003c2d00d14a0340524481d0440740f081c1448940340c00d0417043d680c0c0880c0303404100c0d40080c0d0680120400504628800b141100411261400715a11900c0340c3c040681c42d01145501c0c00305951100301400c010704004040055801d01403140800d2885090321001141d0ba56070704202d9402010001c0d40d003006031101000c1c9210f494803071115028000600505644a003807180180640e140500014a80700c000c02230000801c0e07002c280140c0140e811920310b5502003a07814414000300d01c103201c0151484601060100709900001d20004940004c40c0e19046a07541240c166203551038110040c05031701c680d80d05854080303090b10600c3d0003c90000c100b1420800b800d0030061a5400607254a000314420301000d00c140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 583221025 1250 583219775 583219787
    0x10f0f0b090f1309020a080703080315010215010b04180209091b16030c050111090303041806180e06012c18070303080415050709050108060a1806180b0306070813050607050a 76
    0x6080407c0c0140116451591804110711004000401c1107607503031f0000d4016032081c0500d00b0401d03000c88600500d56125011200c50354040e100307c12034030641c5100328038100403600079541d07029002004d42c0d0960740c800480c45401c0c00002d041341120b40040215000354100422504500e40c002da54440c0710f125945419821166840e6405505000500001c40c095600200301c8040e94940b8107145904004201400c2c054901d50b00809088818511410f0501d00785500800780b0400703207805c0361000d9a031110703501080d20b15664140720000621130940d9500a8050240350019000b01110f515820344644490820390150011800545035105000520200c2450305c8840ea102601c20440303814085806000340d1181e2151a060080a80c0080c005507a1403107030314028010320035030b03d20480c02c040c500c0c00188028040c01e2040b41c0141340c504901e0742d02e0710a2240e00c0780054014005904c1d1850296000c542c014001500030131002a110009881480700e1802004192100c50301c1c0e00c540718000c0c0c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 583222275 1250 583221025 583221029
    0xe030a030b0a120f060908030a0b0102010f050903160f0b090d09090510030b090f1606020d0c081e16050c1c0b010605160206190305010f0f0b090f1309020a 68
    0x4603a005150510500f0300d401094000154022908456221342d803400c40064010f8800190581c90040100081e500c0a03401004450800f42d0007001100c031803d698100311101a100265a0760052000c20102c0d804912540d203020701402020001e0790441c0d4802801200031141c04005400842c0300840380c54104040300003410603503406103c0344c0381800307484076100b801c0e10000c2c000f003004102143c060708083c0142d01400240205a035007030304038140d0b6101500441e00c0303048010b11483e1940c0d0002071050317650601c0340ea4007608040c40d1020030511428071114205035400049010005a46a101380c490a089800e200c0c201600340c14085808210741c0485481c26000740c82e100fa1141000141d0b80c148580c150358040c24800d454402c10000d5807546150900003d402142c002020340c6d103000c00301e08001c400320450b90180242d0b0780b100300080058606110f9401e03900240302e8240800713203124015100458ac0a82114500e02c80316002501b50118155030762140c0342ea40110405600f881c2c0d01080c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 583223525 1250 583222275 583222279
    0x90905191e0e0304081c03180b04020a06210f02040b031302102f160f0f06020a1a0a0209270105010810140604030c0f06020d09060507061a040e030a030b 67
    0x4c00c1c5454840880d4a0394000c07640c000046104082c0c484036a0f010380d10100c034000400c060361a01c41440d103010b5007810740039141a031281907448030004602d840b4080180080c07031400101c0554840343d03800c000c050032010102441c83c940a10010480d0f1500c0d801035031240030308081d10448014a801480155020601c40c0d03001c0060032030100e601e4600240886540d0300844940140d0901c2003140c680c1049100310036009010034003a400101d40e96004004001c1d180fa400458003590f5840718181c0c0e8500b11603e00502c1c482e105042080a040458050f90b40300703c074080301501e0000c0c81c0001a0220542c5028207940c4a804201001d0b8907a0b94005580075040030309080106040164184100d40140e204010701508662481c482c10749840342558021980f003817508030081d80300c208100b8654524090540140305001c07a140d10795114200701d908541d000d0f1980d520300710040d1900e01c0604180b4080c5080526042805101d41c6c40e81d20801c000710074884003071600c0d10391042008044c0e4007034a480d14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 583224775 1250 583223525 583223527
    0x105070204140f15062b15090b130c020a0b0403020304080118151a131407050c0f03160605070c140f16080d080402130c0e100807090905191e0e03 64
    0x1d00d440d07840d030002079040c040902e114508000c1c846c1e03250301816941d07601c080c031618125000640300c440b0343c0084064610450f01113401c451801070380d50461b0305003622940142d101200e81e40201d400e4120060b0400d00a1050b240346c952519091801d40b2564281000034001200c0c4071001d00141c40e00464905400400602428210aa265021440da242554800d8520030740f4852084003d6102030840d10140310000694502400301600d59001b5103001400c50190141030355081401000712042c02558280d11421b01040c2d86550000b810028810018004143c0c040390100b040e042002c5082348402c001403180f5590403c0b81400c1c1703000b5640c0304a000c1c003214018000c1940100f001c82c103484040c50941d141c5ea60390300014916107901c45061244c1e5291060499815512000c5580c81d91400c5d5004031a10340c0001048801d21700459074a030000e400c0c14801d00071201181c2105401103ca203143c0e1640510100c40881240c520614a04800c400300104001100d000c0c050300643d01c2c1640059 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 583226025 1250 583224775 583224787
    0x90c021e0115090b01020f0604062004030b0f06040624140901020318010c08040806070806120a031d150904060f050319020118080f010b1e0105070204140f1506 70
    0x1e05922a05405650801034503604c40001c240d20030020120103500c2003040700c0c0075050904185004151402000803000e100c95205400d04088200b25001c581e800002d00c0011382c0d401c10460304005000d00788175030060f05c41d03c00040084001d6091034000842c80134400d0380440b8510040c6c5520058a00000415401d01c1110b40c140c0c2c012003540c60035001031000401003a04000100c5003213048604c0107200640100e00400c0c2d0700000a421445000c1d01d071a04c0040d52110000c002c0452000e0300012005d80c041e269010020f84240e071a0207030105a9849042c00f510001c00040b00c00d40710071030100002c0404190032407640342c180514401000103071011000c260600c00801d13102c102d216050000e123010f44c68100116481071840303440050054141602c51030712402100e803248080c0e0f40c80c02c3d0943c00d000c00c0002c0ca00d84401c0b0454440c810798110401501041c0054510b03030410207099031b000d0340d980c11820007420030014040c401c80055400304490320f002a808409c4080d9102100e00940061100c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 583227275 1250 583226025 583226051
    0x50c150613020c07090204060f020105070c021c020d060f150b03100b03100306090804290405120a050304030309030212010509100902040f060801051806060f010e0307090c021e01 78
    0x9801011801200507a0340d0840300c510751300d0410301c0d51040c00803601c00100020450344c0010b10098803c1c143d4024481c540305d10000315500c2e40a103401a50007100e108801c1282c0043c150005046440500b8291121559858040c00c40e0001e8043c0d456194440302d007540001c5804001d28060468042ca072030840c1042c0d40600302c00d0700030b405501415240003012605c542c9000c1078420065034480414840c004441c9841e50b010780040c4108040f840f403030f0080708010f0a244d1707000c4050404200d4043e09042c50300041001c85c2d182603074100c04c180035000144011032010b20041014600a490301064030f86940305220741400410150700e002d03407410b01404404e1001083d5501d4000d45000701055814036400060000c00340486000b8540d894031400140c80341040d08800c0c890050a000c80b00c0e40c00109450f25101c00d01100c204c0d038018800328290300c40c1d60240c0c071585070711040a4104e581d5291121031070380c11213054101400c003603071024607030741c0c11a41c0300c040d22107071544150020b000f60245010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 583228525 1250 583227275 583227289
    0x112203050c0d021c05030a03180201170606070c090203090c1801030605040305120f01061d09060420130905060d050a02102304170f0a030507051606050c1506 69
    0x288151140c10030000700015950384c003903080402c10301d080c40e0003e43d5941e881c0c01d558035070020440c00003190421072003600d0001000243c40100d90107071154a22071000940c3d0100704030700140841d9200100f4000140070840896a600c0a091502d0005139242400b548040c41c2c487c110302d042e80f140802e504104010b99072881001d0440b41d10100c0031841d921a4942640c0c03e00900100c0840c10350200c040200d1120300081e524101d502030f0f02d42e54106821070080c011000f04c103201594106e0346680104000f401c007a404203294200c2040045181440102c0008030f5901160304012610700d60901408a140d0703138442c01d50015403c07107041107031000a40c0c40b60707202d06104c1070103840358a08690110205000c0d806810b105191120522002e040c07240407401e4942040c007030345801184542c0554420305000503482c00b20b8500c8001005d02d00d5885d03030b0880352940115030445140c000c00c60709640b41d0014140c03038409481d10786c40b585d072030302d0301c00c0021454121500030b00003a08007404140001c3c0e07190720f9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 583229775 1250 583228525 583228543
    0xa0f2a0b0c040f14010201020d11030f0903090a140a05030d0207150804170703030f060f08060a02040614180a12060e0d0e0409210e10020303060a0501050703110111220305 75
    0x34404c408140804006034028015200050102400d26040030814000340000b140f144404c0d0001e030f4200d440b590b80d859500c2c00356080944d00085c11030014046826400403c00410740700605084819465002003400c1003e545c40f80005030340010810320080045101e044008031541c50b250a41b450a07440f41d440010100c405482c03030200005e1031905042c400c0c0c02c1890058240c40040c45010380c0c607080d922005081c0d1040017518018080465110340da180221421906560303142c0d00f01c40d1031440440285da0100101c5e041d4002c00c094450515160b01d0341070300c001c141c00c0e0081e12105070f0740c1c1441425140e048030400c500d0342113401c8840e0141d4202c0c0315407103441c10540380001e152085140c818100e030010340d0040d201c10300c400c90400c84160700500d0507410798001e403120119814100c0060380c4d240401e03505c036507016206000c14892940700c0c1001e005010300030300d003480c65409000ca82a0848181e00480c402c3c6c20000034a00c441000c800c1603d004001d41c03045400e145510b951a0261901b2842c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 583231025 1250 583229775 583229789
    0x7200c040e100501030c0f1a040611030c060408030117010c02120310030b010909110a030b130c0b19020705100512041407080606010906030507050a0f2a0b0c040f 71
    0x106001c1c1c4207000200018809910340040c10032240d40c4070b0900030541181c501c550202c00e8442880031914070031010784c0070711400d01c1000041c01e240c103110060302c5c2c2c1020380c00d49401d50321041c007803c403c404042004900513400b03040e01c84d035694108402e441d0090140941c03c02c00341c4c1042240342060f6400100402520400f114850b107035259035010700d1150603140d1001d41140100c0b00082045203583e8030050405104891380c2941451138000e014651000340b0015100c1d40c0380400048220b0002ca070f4820072540708a03184111140c03240800e000c82d8116035500c0d1421500d00c82000700540e010810000500030440e9201c1d03800f25a0b0070028031911540c03101030058109100803800f003020301c40c0c400104040500994180341c1c0c80e0308456940d100c04541180c0064845140041c080b80244600b074081d06080c0d40b03842c60500011400e0b07428003079840f101c0c81003000605540200c20038003c50b00181c2c135004449400183d4a5040070396116034041c1890900745010032080042c1103440c040d034400c4501c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 583232275 1250 583231025 583231031
    0xc0607021822061a09040c1401020a0c09091502130b0d0603020301020712080109061d070215070509040e0607050306010c060b130605091312120905030c0607200c04 72
    0x18250620740d030415010b00c030b204085010b0600004200464224900c540910340e048043c0780381d84410413400050585000e0322107070044c2d00502087c032040841003039001c0e0600444281508a40d251400c080341684451001e40ea20406882000528952094441d401000130b60910f41141194480120703148111100c0440000d80700c08040c4080d00140300454005008540390302c0c0509003441d2000c0c0900020001075481d000100d081c1c2c0451103040291504610004404a15001080403049000d4400d83c250720603803c004070481c1d41082c8680c401c465940e600b40c6c0304e650a5040c0030540c0c02c42860701e001500034001b004030440d4440c2c06e0744da00503000d00c3c02c0c445504090800340b000b88046181d09030085030303007410040600c0043e005074007210419542006140e07a40f108454510310184002001c034203101c103108101d6441900082850b5040f05400100d00c4442d982d60782c0b030b503404600c1042c6203400210030401c240b6000303680140c03850020407842e410501880601c40e1180000c2d4030051149075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 583233525 1250 583232275 583232281
    0x30904090f05100204060f0f0807050a030b031c11030712230a020a0c080a020a061d0a14030d110319051606060503060a020a05090409050316140c06070218 68
    0x1121291022a150072100303903066603419100a0b0040c1d4001d002d401c01065141154103502803281c0c1d0400c02500c0260340d44909c41c1c40701030003104d180d8450103010003055100c1c0d01c181319981e0280580d100b60708006842000303030172030b10502800d4001e07800102589034005014002c0450030100307a294024500f458403441e002d882088404030852031040c08002400c0c08104000c005400182010845004525a0480c01d50f1142f085640e20002d560003034110781e9010003044000d01910302010f5421200c1d4030081e942c15040082007106041d50b100c034030b141c2044611458907007001d1101041d90103a925190000340c4a01c400c05999201d800e480352000003030003050080d180e1041d010b807015106103840b9500941c0c814140280680400e00409100b0b02800c0c010a0400c0210b200303d42140807207484079030074616004104401000320709429181030104205030340c0801c01d5110904081441103029001c480f84400c00c241c540b4540036070b100d010301010051100943c2c6c540d1a0721641081c001d1014245a03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 583234775 1250 583233525 583233533
    0xe060f010c0507140a27110906180f101d0a0306050f0901050f10031103120a0804120f080c03060a0e0a06230f012307080304020112050903090409 64
    0x100c1c0001001c0c02602070942e010402050481a9441c080403c64107501c4550312004910042200440c0108080e5480092907120805940003262080200e076425414840e5540202c2e006a21003d5401950f0071020000502460010741c0624860800d035000704042040c00c2d03015208120454a56115a10040d64a051a40e03150460f23030117554010350600640c10207030380c0380c2140c3d001074920f030902d9404d250020700c07003142000c4210710a0803501c044005183c619111504081c402d090032a81502944080c50700c6100528000d1049100640d5a40814a01801c1003c0d00020404100040151000a41e60196440300156030025119050300f9580c0e200d03080041e0340c120b51a030007011406014001c20041841603801401213415400c520450b4101d500c48070040e0f5550003510560040803101c000038254815030711030a511440384640384020b420015110107a80040000b10b031a0b82002041000310350f4400141300c00d10110380c00902032801c0c17a0038041e07240e014900403940a1540c0c1c001e00c2c0148 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 583236025 1250 583234775 583234787
    0x90402092203090e0702061b31030519030e01030506030f0a05012304080a05030c0408100617031c0507021e030c010e060403021f022b11040e060f01 65
    0x865110340010080855140c0a80303110f10703c1c03045041100c4034000140c04c80b0300215079640b090108511010040c1032001e40c521030340d089142e6401924007004c50b002c00800d42201c90358440322000c01569502c074a50f1400c1c80c9004081c000c65a40e002e40d10291000003a0004440d0b0a50482420042480d580b001c010918020607050010614030490780d802d003c1c04019400200d940c2e1f0303d403070f80e29140d9440b01c00e00c408010064038003c0241e01e00b04188412184035801654110655107102031070035523900d0b8064603107030700384558a0708603540b10403c0254408032216021103002a402441c1054800b8071010080c0c16240428548141c4440004011606c28401000c141041d0181a010010840c946e81d0f503d40000c030309115158640009400c0d04280001e01030722071136040d0b00900c120300302c0003e0200709140b00e00c0300c403032155000c0c40303030700c0407031070b04c054050324103400f8050380f51190f98900c61260a0700e080301070100f03a8210811080c8040108200c205600070b00556070040c600005800403500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 583237275 1250 583236025 583236061
    0x30e09070311030f0f010906050310020f0c0708070f1a1c020903010c050d05060301180303091e060906110f090d020315090703031101110a030b1815010206011409040209 74
    0x140b00000104814242048141c0c5d00641143d036150400740e0700c8006c0c4800300c52103406041c2d410351000d2004101095035400030003203005402c02c29401e104900f04681d00c1d102a58000482c0c0b90450101070040401200b8014010300c0d07a8801082c47c00340005c08008903110340b020700070100c100140340c012000403d4049a1020b0b0303024008011500a104008203150021100c4c0c01c041030900340490031902d414080ea80b040f5982d03841c0303210584255078040c4d00405802034100d400c0d001081540d0844003080d14007071541400394034041846802440c2c14000c0300c000d002c440071488824041550341d002203000341e641101041e1042d901100c15400081d10b8a400f20700702811500d2007808000316014046418000c40e40f2940346c0c21101e0400c1400c0c103081c0c1e1803500041d10408024011101014481d400c980d40c00c41d4068000142905045051b410713000c8100da1004070102d03180400c9280e9681000901d00610801e0203510011800308000744082c1c030041c002901c00e84062000c42e980c00103640016513 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 583238525 1250 583237275 583237301
    0x80904110309010b01030f06260106080102030403082d07050a02150a020717040b0906180301090303020921070e060102071203020a020901060c0f06020f0c01020c0106170a030e090703 80
    0x5264900b05010302d000c2d10003000c100d4000b82c14200c0c45400c110050180c403080e0b50580c11001d203182107203540c41000203007040c3c0821545d9200d0380c0019509000b072000350b00841c021340e1803068074541105d0b169000a010703400300e80d80c1c03440d11044c400c600040c0b00c11244c01901d5854025920381104508034038003103545d52155010340201e414451100e0840d8005d1a907030740300d0080852024441c09011140b400b445c800c11a112004005503111403410100801c0412640d141550454645401180c21a0780c011310481c0841c0d0b0010310641140b60640340c4c505002480c80301094007030b682c40030703481c1c48601074410003010203809008544036038002c1c00700718050318602c504413242c0240f41c24003c0d581c403182141640a005074400100700f103445494900c4045402803a5041c18100943d60b80c002580050541e0403103090500c207044d07a0000c01e0005003104103c3c0d0380003140d81404c1621000444400e5056910b007540501c101000081d00401c0c00b8180100441d41c5180595401809501805000309502c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 583239775 1250 583238525 583238527
    0x604060302120706140f191413051f1403180a080304061802030a0b06040213081b040c0c030305060d21030b030d020a020d081603051207090f0308090411 67
    0x2c02a048005490011513095503503c0c040c2c12144145e030302c143c1c030884290074449041000814405000c03a80c001080046502e031041703031034200d200c40e40c410b504141e110500c44801c11f00200181d2030310a41e0691002046080c0e09200a0070700005008200080c2c0344100c4018080700084620704a0021441c2408a08003510000e40303451405225503441200c0440b851b500d801280891584540b00083c5140c0e4050000c0c800c480d5952501d0321081002040a40d001d03800704140b01100c42307645040401801003074000e28104c80428a43c60246584820b246d015900e0409000c06090780b140e0410031207078040c180055036850740c00c04104015070102025213140c410320384000780f0b9011160b0019401c1129641007085d1141d0008040e103811180080780010790000003000c0142c5030041a04400502c580641131400308036801075041c600445400740c0200e03002060112440318010340082e484105840c1c0a844103041c001d5036169403885005c0603003540c10103d0b0303607a046d0315540d0043c003075807180c40b00c06 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 583241025 1250 583239775 583239799
    0x1020a1e020307031209090902061c0605100c0605090c0906061305030a1515030302030d02130801060b120c0705030336010e1207170f04030c060e0a0b03070c08030604060302 76
    0x10113103035220010b03640010600b5000294800240c440d23005115401000d241c90f00c090082c080c40b0450310360a400003607690311103002a49035282c13203210b901088a074851418001a50800d0310071100c0003802403c8582200481030300950300d40d6a85035100c01304071012911448864581c071950320f03254100301c0d01442402c40140a000c58828810406050080c00740b24444010007410039034800c03840003c0140e0f02c21b0100603254200c580140c1101a42c54110030300181c0c0d145181e500b0340b006c50f400110560300001d07030156001043c3c1c080b2076201000d090080d282454981e200c55403444001c01c10980c41c9080402d42c2d03200f0030200c0e400400280c440311480e03c4181000c00d028000c1c074146182c10034030b01c00d8031078980d418500f403000d80707200541004c040207082c00b00c083c1424050b44040003140b240c0100300b1003c80004d47c60103000024000555030a44034810880600c401150244c018121160080c810050042d03884003041c0050703a031002c01c0f10f8903030316078101040140410f500000e6101c1180903c23 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 583242275 1250 583241025 583241033
    0x105060a09081f050c2a0115090504052e18140d1e080109050717041103190f0f03050405101710080d0c0f30090501020a1e02030703 58
    0x28456401c603264a04012135240c0301c0d804001c0c2c0c8545c08011b41ca8907062643c0b071035581d01080303001486c10b01d0f0b4000400c00302d40703144078000d420300650814081c46944000740000c3c4242046140903201c40003105202c200502d051080f42110070441100131b407629000d60040b20b40300d458050411541c04488c0207482e10a5850785a1540c2c02c1c8900350000504401d900c95509801c80506c44006a150712071050341d9003800010300242000818007814400800041da03d00d01241c0a41032007580070f8140c0801c400c121a0401d410400b9090001006c2a0880d110001090345110f0041c05191300402043e0350360000d14081c0c1c2d0320b0145a01081d8010303180d903c0000d2150304000c4230f00c00002c030780110740080e542c1d4000c003560100446c011300c80a03901c42d03409050040d0149a140c15464050704180040020690711602c0080c03407010700701001c501d00e803501602c43c50700c031740c8940d9105014200315024509100c0003d69400e900072000e070040b040715005200307080304504e00d18041c1d038018040c0d544103500c0c1e080c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 583243525 1250 583242275 583242313
    0x20312040807150203061507320606011701090509071e03030201181212020d02070f021f020c01120e030a020601030b010902031311011b2603010e0105060a0908 70
    0x402075454254007001050380c40c90910172281301b2400100305020540d002c40000c2656045103504440c0984480071880e0080e460507101c10340c528a1141882e03004110802c0e150800101504a41c10b02065240c0d4181a02090a415041d101d809030000340c183e407145446490442c45a00c2112861703034002c0f904c00004940380c58001682d000b03400a01c80d000d8142c0e4a1115240d0b42d04c0003500c65100c02d42803060062180181a40300c0c030700204050704001d19900402c2c200d90080c0c000301d03482d04d004010682182411104010346812194540c003802c040280701a484107440c0180b94100560100c4d2021031074419803004596010035000c580d120174600d00065514042800103641d1808c61500001d4000c2c0d07035000b03c070f111368080f0f01c18403940669980c0701e5440000500550341807150901d184010001031210189050703021b8000400c4030544c01c10b5030342d50000d00d10603901a00c01c1c00c10043c8006042080d83e541159001d440141e5200900c070b00c00c540081164000001c01d00494002484030000c0385 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 583244775 1250 583243525 583243537
    0x30c110324070905030606030304030b04240c0f0305070f0810030c0f0503010b0a1d0c0c0a050606040c0306050d021225080d08042406090f15050306061f0203120408 72
    0x622010340f6140c031102055500c4004682c0300368194020842880000e46403614640c0192240403003a0340082d0700e00310f4500c5440303a525002c00b030a694a0304184031a9000b580d21407442031905041225003088a801000319005c4015001170016090114981200004c42c400056400200315001241c0b1822500001000d61003801c3c07013982840f00c0b05c0020714000154504139482002e1741140c080030b051071444054001812408040c2c0c0070f010b4040181c0e4103200045016100384041c00d41440d0001c00c10040f00c003082003403010146404014041500c07064020340707030f098045440c000100410488a0310f0040b0840311102c14180f14446100070001038828101540c00c0c4100351200100c0c3d540c021540c898003150013800c840004001c40201c520882801c140705580c590001c0b4189440e410324505072500b00500b10100c0d541c64030301f00800c04040020001509040b8049c0072181000000601420389a1018201d4071156002078010399000704121006802c1c0418041c80602c0d1030704080401e41c0143c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 583246025 1250 583244775 583244777
    0x7030e040e060705030403080919080d0c0e060f0325080f1609090203060103060308040b090a0f0302031c1701120b1e01170703080d15080604030c11032407 68
    0x301c4000c999142010480600c604101d544090840c1c0d80d40d2011201c42d4806010341c2c1b2140078001012000314490240d6203243d50141c01800e1361804500362160480e036901320403200300429040703204c007030360344805c01c8800f40043d11f290340d0307145e031030740800f0400040105440381c03000d20385c803020125904d81181e200c2d8030900d200f0700514002e40d00c0c06540d84407000202100d000081c42501c09003d00300c800e03170182d90064410300d80000c00d107440380e03540d140c00e0740150440e420b0350b800401d4181c100d151003540d40000e8241d43d000c1492052443d40800d90b41c0703c0103e5004981c18804022100c1288103400c00c0801406c038019030405541e4888148056040d00c43c000d0350941c940100150104050700c00942c02503a142c01c0002c581e071b1a000103003495481000d00e6800d6801005000004200c00001501022040d02030000b0a0034000000d20340e4a0790540c444038194004004100100343c22815658049400c500c204101e020b1960010782010803000c1c040e504d140028116071450111140001c1c440c10403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 583247275 1250 583246025 583246031
    0xc0203040518090d170402040e0a02030607180602150c03041a040308060f0102010903020a080f0705070b0d06050d0c0311060f030a270c030f051e03070614011d0c090607030e04 77
    0x440b000031117002c1c4940c00d008054030121000b00f001800c0070360118141d0701d420000c4c1c540603001540000d08000c0d094070705d00e001400406140380d10f0800540f0580042c2800d0004044024090342c18000000d0010f0540311400d0000c00060103200345c0102400305100e41a40a12040c541380c903015195040c15181d10b8003401c0410005260b42d401403203404112078068004040c0724200c0e43e2134050580c09042d101c01171040900c1140e001560401050004d00017200002e07448452544200f012941d030b03075208900c280908108a00856408403104050341e800280d940030015500010840ca8416100c00c1d40d041c00000040201c0c0d5507850340020600340710403070f03079510000b0441032002c0c07400811080139004215800b030400001d07800d0700090010390f1182003512050003000c00022140c10103100503179210f070800102d200c1002140e21410402c0e4aa80c1e114502550500c400c0c08903042080d04000d410002035808502e032101e050b0300307450310904020109070340c4929500c0d0080c01c028101a0b050b0190341 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 583248525 1250 583247275 583247293
    0xf070e072a021302070501050f0a140a050403170f041505010501140c190b0405060a18020f0d200901050f0924131e0c050405040c020304051809 63
    0x310034840803400c5201050509031240110310602581000d0715400caa0241d080310000114a64900180100a0054000041034601a4000c2420f20402071100350282c4c5803800c06d560300e4040d402810780204420f50002515501d515058551642a51403c0e01d40100101009407407098000440d2007036204601108100c01840c00d410700f9a1003e00501d4041604036001a0001004201400700c1c0342c07000e0119039000310716000c0325000c00803050702a941740350441c00308400d00008110054015840c40003c0100070038090828808054990009105229103d918040e1740d60701e5200200c07c43d0803402d00f42d41745006480c0304041c0d41d160450140500c03001d4000040b20310f00445089206200640390400ba96142043d50070202d0381c000f40d400d0b000c0320140c2a40800e0315110401d10340e031481c000001070341c0400c501e01d03480c1501d01a10f10824582c207215040c0f0060341e000058030100c41c401e41c2d0104200c86030380002d80c114055030b0401c54003d6074804800140c0000c80f041c1500405130a015200c0e585 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 583249775 1250 583248525 583248527
    0x20910061211090d080d1103010e090307030c0206071b14180405072108070803070801351906020403020901050904030c021003020903030c0105010e010611060a0507050c0f070e07 78
    0x1440d01410b080e840201406a002581018410422420300c07411141c0e161100c04061002210125407002c80760020101c0103112403918070002681042d41c1c0401542469013a40c0c00400c01c546001009010b02d9021130709030100100303050091a000300031003808030740c3e42d2102104600b01f4800740e8110b210300c00c41c130058601114ad43c21010301554000000e00359442c02c1c582011030149a66400450005000c1904e02c0400c4500c405041e142e03118100c440da5904007054000c082760410b80100300c916030003410000201034000a041e480c10480ca20441d170f140300d8a1192800d000b00c0410301c6c60500c0d00d2800400c10816140c5c0140f05882c402ca031802c0f8180d0b222028090061002c60f80140481c4a48c4480c10140c0341c8208941130701c0c4414940589458a05004a411a000307481e000344d05030f44a8006021610401a8050261284e803500b420388408100b082540c0c0c400c06880300c4501c40c0d88001144400c1d2092044500c0e1021007001c96440b103e14007081c070303500e00007403145040311094030300401c00d12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 583251025 1250 583249775 583249781
    0x402030a0903180315052203050307080f090616030b0d0f050d0504060207090b06070c031a0912090f12030703090905070801060e0402030a0f06180b031c1b0209100612 73
    0x520f4000f005e85890815540c84040148006400c0c1070000c0a507440c0781c03900032100740342185104d119030342d0341c5c0e00d038101854054819031000e064130080740008030401001e150b002074801d0f8001c0c0d4004e0304104044e07140714268000e200800d04203411007500158001800460180c11810512a804851100c400d405044500d23025a002d9503005030469482041505040e42080001f00c800078502e51400543c2e03990020a05415882111040c0c1902d0303d0340c8209500010703040d4042d0362100074101e03800560394036205030710a90092a10603c0040c511038841c2e00d45003d45210f0005810880e80d0350b01d000d042c00303416400303c0d111780407000b414940001c019034850070a040c1200c01584400e5050300d803401c10800603410003841d04058070343e02e4160340465480c1d40110402446191030f0110a2040480c1d1481514050207005000350301c164054000c404240d40301030500c01c420b1030080d0320203040707606203a036000030348002a500c45140c0c41400300c0c00c18036645542c2241d0198503031215071030700c0d8083c0d1425 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 583252275 1250 583251025 583251029
    0x11a06040501020c010c0516240314070c29060306011a040302130b040f060f0902030c16050f0a080a030b1f0318080d0203150111030d0908090402030a090318 69
    0x140c0004c403200c03c1c203501404480c10503e100710243c1c0c003401e0303900d0104905002103a011043c074000c0d8104800c0444460328404510104600d01806031248501d030315101c40c0d1010f0b2082d810019001e1400c0240044403501c6c50060051005580d80300340000c0140e011002c0540c0c80611901a40000103400329410082d18648000c8040050410b8990f40800154401c0741d007140e134150b80c80d21005102d550700ca02c1880c4011000b440000307141820b007410f404421501d50003c06480b0720402c10b005440411030259200040300700b070402c4085506282c81070411044001c02036851003206400802c2007403c0000c3c007842e00701560108100070354102007200c42c0040098194100041c02002034440707101c0c5c0c00c5100b4903004960710604100080d40c1ea00b0341944400392400c004d55011042c019031003902c15141c01c034000d00740b9100701804203004143e42c1f60b11030201030000380d607600c020301003c209100040d14221440100215243d18020800201800c1605c4044000645040d03040400180000b12041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 583253525 1250 583252275 583252277
    0x50307090b0f0909090321070302220e10050109210203030403030c0614040308070f090f06080405100606120906060b031302030705040c050d110d02030915091b09071709011a06040501 80
    0x1102c1000b0b203c00e518030b01f102a00c0c20041507001c01280006005151344400c0300100f103201e0345606490701000b41d2010001500035a03010003059030400c0782d0380e80004032209817051588120304001c20241c800c4c1ca80781c81050001e4250001250010038140c02100c41c6002c40e0003000d040c86440709408180302c07500422103005010030800004250210b1044100034152026804c2076040c158641d42125010801a032258002901b59810401040010f20000300303010682c0106100d0207003480b0000d82078006110034a07038030b550344e101d0900034860305802260090803050251580d90500c1121202a01c841801c2030f4001c0c803c03100c0000e03ca05045c0300d8000b801006035605030401042800d2000a81600500b61040c00070074403115018401c103100942c0503000b00303c018600c1e58000101d10507500030040200b02c258000092404112214900155444c070b4200c482500380c4e50354800c15215070390340c0081c0101d070394030307510412083e207005510181d40020700c1d075a800c04812850040016920490103924 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 583254775 1250 583253525 583253557
    0x20102040303050319090b0a1a0d12300b040c02070e0a02091203030a0e1204060210020d022b0b12030409020c0f010906091e05070501050307090b0f09090903 69
    0x990420380340380c0650008040e0400100d014031b1b05446e1003c0d10182602d020702130f0f0351b854815042c030205251403c00b5826007036802c03403401d84180c0c643c440541c42c400c0030501031000961041c0ca201c074540d810010481d40c007030600d00915402c4a4094010150106000d010307526181045000a0000070a14102d03140700c210040c0d0341d921245010041c2d0032044440382c000300701c640031100e1401c043c400346210365003100c0001000c20032405500d02d050707000786443c0110300c0c041006204850b03010800100c10081c8540240e5140300c0c41125030000d10580c00c0120700041422207401d54402c2c40f503c005c1a0242c42941031003145008400c0100c0440c50390f04022055000304410059107186402502d5145045c0c0181c400807400b0500e85825141c3c412000c40d070b8640c1c0c42c80c0b0746003002000301c0c407094008a03140403400d5103c0390350b03112a9541200d014513814840040006200d0500c910144070141c40d1460246456170304500c00f800321a000741480324401c1c031180700054038040000055600d8841d07070507615 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 583256025 1250 583254775 583254781
    0xd0506011d152d030618121804021e0a02010c020609010b010228020d0f06140402060306150c0d080a0e0102070b070503250206041a01050f0f0a0306150609060201020403030503 77
    0x3241d202d42c0b09014124019030020f4211240c1d42401000d01ca04444002d0394650068201170500f80318120714801e4040c0d0040c815074201d91031801003906480350554005984410451000e04190000315106400030000100303155144c0e410741149405002c25000c540c466142c020347c903401d88a54429040c01a8044000e1000f00d0510a101e2080d400c04500c90701510349654011842000304008265000c00d95049108100309079071007112800202d243c901c0120381803540c000b9145200c007030812840780d840300c07840d20138028211044a6401e5090021601e08015541001e400c000c01100c521007507600d810a0b0507550700040c0200c0b00b6669010541010b1aa5160025119900f0242901c0781c0e82c01d01d03c40c58801d00504100300d03040c007481034005161a203807500d00000d00300740100b41491043d500100400032900d9202e8a503d005004a07091000700c244000030a08031300550b40040e100300d017065121001b50365404d18000c00c0c0c0d186595550841919004c080e400c0c3e21842c0300017030001c0c80030400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 583257275 1250 583256025 583256059
    0x6090f15020c10061d0c0c0d05040e0106051201120201140a0f0201140601080106200d05040905180c011b0605010906080f01140105280e0604151d060d0506011d15 71
    0x9880e845006c00c9100f50400652105451400d4116264580070440000b8280104604a0510350051240745400c03840c1c08180402d4400100781031003942c40312100c040e590400c41e80980301f40c1190210711a0100d84031b1011a03030041c1022842c10801001d5440d0448002c003400341c01018503ca90342c10b86400c40c0c540d282000840e010700e0000c0001c42987c0803072494510b40401405201071040d1070307030344030350300d883c02c204011040301c030040c150150540c81c9400803a4241000301d0340035500d003030900748142c01c12003055403081246441d44d0700a165624260001c0749041143d441202038810f840e049a105c101c10f03102480c00c1300c0c00b55a41038140c2c0c4820004000ac1d241c501d103049140c2d00052844403101700c060200c100d0721407050b0008415a07081c9410080c45060501c142081c4001e00c2010b080d00c58941a50b00a101c10410f4800e8800174800000038401e407100e240045165900c9800c81c3e10310742c0d54502000c0c5650103041c20b803140e84c0c0000007060150382e240c01044031450009041096143c843d000c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 583258525 1250 583257275 583257329
    0x30f0a0323030a050109180302100209010309020604090c17070203040e060f0d150b19150c140f06070f170a1b020604020406050414010306090f15020c1006 68
    0x1901881c04180749084082100100c0055409044405404221541415983d40598042d0610b01390002c40052101010942c002060800c03142044c100503616200c10004801510110001039049800050700140042e020307806842d400ba0696100b0b4400c10b2403403040711030b0720070a44034400144c2c002e00041c031040125460b0b990304000001e003001e2224603440e0226904e544120800d035201c480309041e4194a12290180c421700c141c0071620300c0072506483c28034070512040c60240265288020141041b810b004d10184070819400c4014008440a10203881d551840c0c2d01c0300d4500103002da8008111030a01981080d1000c0d20a41c96500b91380804021030245004001c003030091850320750000920000d0890311990101c101e590241400b0718042c01030109484080e4070032805a490550701c1c880000e05200312505403584000e010403020501d00303158101003181c8001804100c02201c8032a2038480075801020715110450603280c6000800700080c0031541140304074031182003190401140b8640d102 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 583259775 1250 583258525 583258547
    0x1080f09010618092a140d02150d0606030902100302070f1227031109150306010b07021e01050d020708070c03080702030708011b0f030209220b030f0a03 67
    0xd0000108181c1c0c452000300a00c0340b07000d41e0328141d90b540e40c0e0901800442c4000c8410b809582c041034080c100c10100e0039541c91014440c072800c1d080050301c070900c0350359010740c00400c03190000c1c04d0a41000c0d0410702004964003040702860410b00c0c150002611500a00441545c66001060315507810a083c40940c06540301c2c803400c8444144400c0c48400040301c0e4041c00010920641d00e150052450030320714004034168040e40341908009460401c00600c02c0c0445080b01d140585000c040c5883c1c400511040380401100d40e58140200000030031118603140180602c80d000300c84241891039041c0b0103c280c400311400c5940052070802c10000c000146400801c510b911910b0614940f50303044e22100c040d0390316500210f40c0002c0028480d0190f140030040e00f40580100030003009a015510b2080c04101c1c01c000400342486000c058188a442c040e6040c4d40c0441c1700a00303404500c4052076200341903c003420703c810400310b252110302111810001640c2c643e9603440b0340200301c00c0125171002c0e00c810b400c0f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 583261025 1250 583259775 583259791
    0xf07080f04120c050a241a031b060d020a020102030609011202181e0a0b03060c13050f011416120302040e0a02030408090a030b0402091b090d05071a070506010f030201080f 75
    0x2095181c40040d100c00c08010007001400b082549180c4d060046c04195040d1540c00d001014801a111031140c2d404070711040b000c03d088400c2241c0010007408a145c0d4000d207002090f0145c0701142d07940e1103039019001184150400c41740140309a80700c140c604c0b0384400004010350480200c0440a4850103401d080ba41c00c0041e6003210711002801c0303010700e6400c0004413090400c880d110540c0d000f45040401900e5000014080c14504200c069034080c440031800b84103183c40b80c01038564206090740141e41c0f40400c1e42c02e2041c0c065640c402c400d032201d004d00d80b0383c400b194900c02080320046498401e1003990b055544070f040b42d013460744030241e0345806500058402d0300c03458410001860581c0d1030085140007103209a20b41001c52429004024224000500d1155001c01120745c510a84003440101d40c12142c044030b4170020744145042513443c16a15802103020340748030300320b4121021480d03409000300610800449134661f880c0c981440c0034008900c4001d0200710000042102c0321010072400d9030110203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 583262275 1250 583261025 583261033
    0x210803090a290f0a020c07080a170405090c070305090a09051603020310060c02040b09100e15010801030201210c0e090a02090f060a020c03010f0e0f0c010f030f0905060f07080f04120c05 81
    0xe0010080c28010300c1e501100b02e0398440038207027013044801c00010024104c3c0020850500c4d240001240d01c8040003400680c160100041c18420507005800703503400d10b030028080844480c0c42d040503400420040d111150580100c10b4002d514901c203000301c81c454001c020040d0025850a074068481c03180d41a0200e902a031254956100c58846140e100c2c400c2c000a4110f1401a1516451900840014200308401d00344000605420303600603000c0390441e5820b20f40020034282e09103d482030055000006013009041103100302c50329502100000452808840c88070307103a02c80205c1702e8200e1144090b00360300050802401007036841e00c0000b8103da0300301c43c0151802541d0760400a03003111103881d5181d40c003d59504c3c08110006040080b003039070750320a400800200e030121340086c00122000c1d01c2d4200305921203043e0500d02d181c64000718000350b8400201c60340c0e820a0520025640f4080343c10400007050000066100050001564080d40d000389828941c818910f4003220840484c01050f541441 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 583263525 1250 583262275 583262287
    0x308162c0910150203090303030609131a06190e0c070f120804060c030e0a06150506071101080702070609050d170d0b0f0307030c210803090a290f0a02 66
    0x11a540120b1142c440410b40201c2c490400074802010540200700008650044c03100c0e040750f40740001200d40107082291400300310703514000c14901c901c0110400611000104810b00c140200a026403802014101c0c0c00102510400540300c00141140c031401c0c15240550b0040b800448880c1c0c002d0141c1030103880349c00500390711501d54980003000304c120040024030342c5007040b00303010b141c3c840c0c5011400075140900102410650f816035410f003280028050075170fa00c00c84240c3c0340e042c855a40041401615441d2904008d040070410410080c4002c1d02140c0c0d4400010130362840070030301c03406540303180d120f44418505040500008108115040791251b1160801c050001c0004c0c025100c15003c0240c00b040c2e8941110502c025500d80818146c000d92041c64180000f5050320650402d403030880000c0603c03d41803041c841400344055201170301d0303502c002081c007500d05404908809002e0046020341042c0c04c034000c901c1c41d0348a5060000f00c400301885c000c02d480300d642c200c26a030400c03012040942440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 583264775 1250 583263525 583263529
    0x90c0c03130602060702100207240f0f1e050405100c0203091206070f02030a02070611010f05012c010b09040e1c0203120f1005010c05030d0f090308162c 67
    0x881e55410030805603100e482044405541000b01c0d001c00b4440c42d0040d0708018807943c0d240e541c0d960b0800a17107100805c0c0400c164040c2e0090707005043c103c80e503c50610030800700b1004207008000c11100b0001940c11072800007900e450343d010f114022580100205502500c8828100c02490001c8001045000c200b0000c1429982d407820590944849009002c0d40d0424020140c51482c420b038842c0290341043c040170301e94a401040030012110941403009065403021244d0b030051403400341001e4110302e01000411044071030210050103a2071450302c0c0000010103055400180d02c00d02c40c582c10f00d44100165112420950031116a09032988100d810030081690140409003110b076860700140e1000c100b14503c0c5603076103600380d084203100178107030805c0c11b20b051800018403180c06550305101598582c20100b140030012600c2c0c40030101001c100900b8401007880c0586082c403025800900000c1c0030a11050a03981240003941450b116000f5031107003502d1200c80c1c80c00c03071143e0b403091007496103d0040715 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 583266025 1250 583264775 583264807
    0x7060902031507110601050a060c050a08180315010e070c0807170d0c031802220f1505031504020909031612020105010f120818030d0f020c0609090c0c03 67
    0x382d850300c00b034003405240c4103078002d202101094184000b41d0007000104130b42d450301c0340d810702566441e18250482c8021401d11600d0b011048400130a60880024000300520a100340540f15040840170307150400d5840c1e4080b42e42e50b001b8000e82c00d4040d010000f01c0e203050702a01c0030140c43d9200e400d260f402e000e66501c50a90402091054196807a000102e02c0203400c0c49100b50218028941001c129a40b40c0c0880d06c001702c1c00d00f200c003d0282103124210750030b921905250b4050900c130b180382840110f030080006000b030900b147c05011107242540000c901c92401107071001024805200c40200c44d0b03255020002c103850041c2c144105800100950f0030300e54030180031072078407a0103004825103500046000a08680050740004000c0d08030070313401d10240c03104040c5a0045038124894545401580d1600c1e98408241d04019526129807901815800d40010521480401035001d9514038a107010034844280704e500c40e034580c80405000024403e116040c06400e4010003c4101c0c3d04154400c0030b0301c150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 583267275 1250 583266025 583266043
    0xc0b070206011406040e0f090102070b0903070c170318150a0513050d170c011e09060c2303090c12060f1f0e090c0402040612060b0901140706090203 65
    0x68001e540107100c09050aa2049400384042d20640c3ca880c1c40d01540c00d2412102502c3c940100e5500c00100742541c500f501564a03140d0030519003001824000c6050380d40794005a0300301c6600705a0040002c40050040c1c0b08038802e84610f024502d4288082248401562516079241d80b02e001160006d800d03280c03101c0a0089200702d516031079518080344012009001e0039603c030328818025000e401c2e00095614007400f0a24444071b0781356486940c07450065000d815a0f60007800700c0740d2000c4a04080442c25081101c1302c901588003002501284c401c01c5410300c00c410401c8000b14030480c1d018201d96000301c001c45c0e000940b00152440c9400070300014002100208031214031f40c2c811024003005191002c01e00f83c119400301d525901c24401111103074403d2003640f140300c0701c5001d00400256004010322911800c5a00208210354998941c42d02411400c42c00920301031f601d1520328041603415512044801c030752816107840307015070401c400c09005548804012190326465440344401601c040041540d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 583268525 1250 583267275 583267277
    0x40602030901090906080a0b040c030812040b060d02060307050a0e031c08071b02040903170403020d0e01020613080309030d18020906091501030c03020c0a0507060e06040e06100c0b07 80
    0x340d01d040c0d5500041814007aa049840c60902c0d00c40d003000f001e640003c0096000754082c1101078142c1d26400d2000d80c1440c1e0358006030407001f001401d2490703143c0c80e143c1a841a8070410805840d070310b5038424840f000c1010000250400801c002081c1c201d801400600a15045464142c0142c80c0314004603061012140c0d5405010b00d900e0803803080a6000450355038454010b00d400c580f00c1054058040e0340c4c41107039001038001d60b543c61000341414400c848044a80940ca0054480d504141c03400070341d95481c06510310001110100b24000661000c100f076402103141c0c00c0500502112600c9500490388003900c130785078030b00c0208090382e040840360141c14000c00c091071b403107640301d201c40c0148440c0400060095201d40e60a0041180d0303001d003107488001c050b4080ca0001124070114906030300a01c60b9109925051080c6031022082000004007002580c9042d5148024500e4060621981c1d02843c000d81507800302c000d00003015428103042d03208880980b464400c2441c91300d92900600d041c0280c8501c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 583269775 1250 583268525 583268527
    0x31030212030c010501150c0f08160b01050f040b090a05101e06030b012a02130f060906090b0d120e3007080a03030b060405091602010c02012003060406030804060203 72
    0x1584410b82031049500503d5040d10b0350b600b4100c0c102c2c00a0585001381001003103c2c9000001c0f20910501c2e1050b218044040d454a040a664070f04144000d00000d101d142d20440c0d003180b4403082d03801d2074001c0b200c1e0481c0c060000709142e1501001100a407030000e03c40c0310101c40c40c52740041d4508a4140506140401c8080820305074140500203055034140c0642d2418482c030502101c4080c89410021032090303964040181203d502480000c9080001102132488c0a04242c800c02e4800160381c0700d04206e07104517070200300707903030742c51107420292005440100d0340901700000c000042442c82c40125110207052500400d42c10141000941142c401c14420306c034405000004003488030500805000303800100014684585082690b5643c4c06040900a00305615250060000e0701c0d41402e940180500034102d403143d107002c0c410044032001c280744110040d800c2409081507070b401880b800708016442100d10b00d290003050810b010380c0e0b10260410390003644d0381d0030010118000d02c0203400580a164051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 583271025 1250 583269775 583269787
    0x30604090c180b09070804030c0c1502010608010e0d0905120106051c060b030727090c06030902100e06030c0a1205070305010f051203030f070504150207090608033103021203 76
    0x150203c660b096180c0780181e02050a1040071900f054850307078850351518007400f0543c000c0c6810800b100540d80040540e80c1c110b4007800c907041d0190081000e5481742402000201542c40915550f120300f500710b2800300c0d40884c810700c078078140700c0140c081042240001290450f95180450040404604414401d00d10802c0500802c01c6500032412103e404a004100389800e1030344500c61015032200000e070034040e098204486071100d800031507c59402030a1010782d03a80d540d002801400f001d1004920458448018407040c0e0f000e04c440700707a010703c00380401c2d00310780d00c2001010455002c103020500f403002c000c4034520308031101e01410303200309801c0da03004c00c40d540740c290501403d145942201d131044041c036403e104030400000940341d10003001c581700901b940340c1c50400e0301e032803003a81c000800f60b00000c3d0a48858940000e0300d2001ca40500301d08010b070607038481e0b4003512130041c14080686040c041e01c0400340d00c1c18520407400c05503e0b000e10380e442c01d590f0741e0000300c01c01c03090080c0101d90f810102d10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 583272275 1250 583271025 583271069
    0x30d0207150920030703020319031728090b0406200a350a020c060114100c0809060409061d060a0b0a1707050306150906040506030604090c 61
    0x9206101881c40009210002d101c3c1e03110b140c00041000200940040c03206280c0c519642004804011500a0f00b6641015440002e0400b1840c1040083c5c01040342d03d0b040c034000c180385500b03072885041075851410580d01d444141545a480c1c41040011858071440e03c640440c2c1c1414560f40070380d02c2090f000a44c2404160050444507000a0004070000300348000c0200301e80044d9120550090818907010346a000000c088a000d14500a984440c0c80001008405516a4010a000070f0500d0483c0e455030707030b01c02444001420030301403160020403081d0f01034040c81c0110010f042d82da100e090094200003000c0d0101c0d00c0b030340040c3d0107006826200c02041198500079a640250000048000441d500d0204042004c1c7d00e10340c81005511b032800100c4140b6a072040110384814140c4200076181c5061080d4003c10743e4000f55038842c811124030b8031413644680024112034000d0303005440982031a10302000c00c940340d000149940d0f046501c506542c00081c44800c900340c00380c5a90244103c61080320300c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 583273381 1106 583272275 583272293
    0x6140912070b0a02030c301b100b0f0607051914010603140f07030b0c1b0303040f0308010915050607020613060f020d03060e150d05030d0207 62
    0x1030590035290340800180041c1c26000112440c0c41c220b01347c0d01039001c1000320f060302c0001001c20601042d003180c01c0600700341d80100105031000c00d2401030313282c01c214003400302a40640d0780d2092524031340340800c6c144075040000d40303000317040c00e60599071941e4600081c0016400300c0301e01200d180030040c0003400320510405c03403c0207004060762407400c0b8420180700f1170315214078012008100300002000070203108498214080c260240c4490303040791050b234020701d4a0400c0315512400d01115040030001507004e06d100380034180e5040d03818100100001c0741031700034060b0641403101200c5c6040c00d1071900400d9030070848615036200c0d50f9100083c01c40c070030100706c1800c80040d003100013501600040e00c20510300d825025107040d114480c80840480d4130b20701402245101a4021440040107116140340e000c0000d00f0171800c0c40480d44580d450b40e00a04d600c2d20004d80c00051800c10012040 = true := by decide +kernel

theorem cover : BRFrame.Cov 583093525 583273381 := by
  have h0 := BRFrame.cov_init 583093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 583093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 583093525 ≤ n) (h2 : n < 583273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
