-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4436
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:36:29.351006+00:00
-- url     : https://prove2.me/submissions/982372cc-0e9e-4daa-bd5b-cf2d1634c2e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 797661870 ≤ n < 797841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 797663120 1250 797661870 797661983
    0x806180f070e0402043b01110c100203060d151b0302160b06031e150c3615070c0902090303090d14061e0a1a060c0703 52
    0x25030071441c0340030018001d17003800d03044503800030098407910b25071154110100c04a00035880c1d02801126071559560b2407490240304803c2e1401c0042002401e080d641950381e590b41d0f49045c55188155000300c045101341d11007200e4068455070000c0001c50108150300c1403001803c01400c020035000700181200c0000d03009100b2200d0480c00350700301032065402601d56814244003d41602e406200c1c54649004004580c400f8088520f01c2d40007070209281d0143c600203d180004d003121400c207004206180d29039008211400000c010b41c60300b00038080b588070440e400078003014965604114603e0300390245034040300003020010711a86140b460705844900c038104902130a45181d4040d4010070825059190007401c140b4214403600030040200555810142059001d42e9000862107154949402c01840c240c00c07180c0c0308850500c10400b809045100fa075410b1403018a0b903001c2d40300000c0c2160440003e000c01c070091034114140745454680180712240746107003404000000c2d00b904401100329084003061 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 797664370 1250 797663120 797663129
    0x1203060b070c090203090709020417070b0327030f0a17150f010e0607060609060321200a050f0c0103110c060105270108012715150806180f07 62
    0x80404241041d143e2030080d440580100c1e501c1c07181180000f01051540000c2c03018241003400506a90303102c000003481c0c24041d0300321410303926017403041043c0300c0349100c071880301c1507a0715081404c1050a0440b0900b14400c2480042202200142da400c03825000110700c41403801081d01d4215958644100e906c0508044840541c00045402b50886962103011140d10b82940140040d1800200c0d42c0c407001201c00507440120240c4d16900308005004a82c5014031041044c0c1c28034031800c1054030401005003118003044410041a0300074002d01031b00410403481c1e02540300d421200c1e02400c4503082c03a5100702c448580c50010f07042c40c50621040780c2c1082600c880a100c4d00c000c0c40c1c0350742060f04000100d0102d400501e411402142500d00c80802c0314510b40c0207080607400044e540034118117890314500d00280003810150216160000500001040390009001904c0014048a01a08a41101e0301e5501819071b621a40d802d0020320807500040c40907003d900790403180003040b407440d06070301c0320340a101303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 797665620 1250 797664370 797664383
    0x50109050108040f17250b07051303030f0e0907110c0a0b0d0f181a0a0203190515030f101d060a0207050a150e010b01110c010e030c030a1203060b07 65
    0x4118001070000c0303550301101c0050145d11402e10b1869503d211103807000070b001414243c0c0d203045000a0064042155070004003500e030103450078520391003c24410380c3c1d6110003410080d181c2545035106124030040c109440d030050031a0142d00380488004e020145806040b40280900454a00c980c03030200304000449203003000c1d56040100a00c54a40200007240c40e19881d50307124880e00442150341c05541340c1076489000407408107e0700b28101c00101600600c1d5000541c4108140100e40307900c0e020b0680d00c16110f42000c40c040c3c0e980b103c115180200900f195405100b22403001401040103d0940034200345084c0030080754240540d10f042c40c081e0803811015035004540401d50141c0c09800408130940540c0403a42550026a20392800307a0401014092240ea50704100315814420302a070f0404000074030340207665002c0550010380310b00c0c000001a041c40a800780750031583d1400d01800c0302c14640102036440c080182d08200c130a0207800c50511001900d44440490f1071500c403410780301096023141 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 797666870 1250 797665620 797665643
    0x112210e090916080d081e060f01032c100b01091a040f180e07050a060c0f020402030f060108010608010b0313230304060e091b0a0c060c020705010905010804 69
    0x41484800340d00588044080c3c02140079800400c0c82c5090f00200500e545002070a44203c801c42c020180304d8050400140c0303882c60411501a02c44502c0c0d0b4540112084640705041e07448500180d00900b4090746210120580980e820035502c104540200203a13a000203440c40d0010300d00c103000403154180987c03408030b585460240b10321400d20300510362050310241c002d0f280c1500c50a521004404035801611070030702c165611407074800c0c0c5010341803026202c14001d1414508000004241c2000c90042c4010000d1040500003448020201300d044c0c0c0e900074100719680c1c1090420301043d5182143e5a5000c038144000000b45140704a00c440d0407075000920460a58449a6900b411030600c06826140c03a500e60b4282503220032441c0e03100042c070034090019981da03403900502500401d002c803241d0b031156152204000c044062a0b58030340c064525052840c4e51421a400162a560b07520754020304803500c0c0c44a03280c60140c0000e80c030b1003a10001d817655122107580d01e00455220728202c80040107681440c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 797668120 1250 797666870 797666897
    0xc09120d081b090d080309030c0114060a0e090d0302030705040b0f09011b0f12120e100e0c090109090303150303030608011119030c0e131d0c06070326011221 69
    0x2174080d68121007800300b941c0c541081c00c0340903030039203190400251040400c4c100f4400c2502d44451003000a103640d0511142629184840503110801100c2c0601072680000003e540c0c580305034100c3d8041c009195101ea00c40e024060034600d940c106030b03041030220750034000074000003044c08058104c103640b050045504429590741c02900d4682d101d40103061103d80341c514a0851801c1c00f80c0400d8844410081c00003000e11405207081d2000314020303070015001001c41059a0321140340c80e6055030034070b8801080c540018a0201c0041040290311154541d00700800300030180d05801410407210040c0c0244103410808143c030341284500394928140c00d0b0581c0980103041d003e60000701d806402070030079001c2011517101181c2307059003900091000c103913a10503d11986d458400040b00b0990740ea0700425502c1e10003c04980d0303d04c20300c000034061151244031500c520070700030916160120b0040d001045543d44105201280000d010202e89158801d191902d07409180c40c0030000e081900d80d075401a0300201c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 797669370 1250 797668120 797668133
    0x80109080a1b0210080a0f230c040b120117060105130b030c060415030e0d050403150f0911011d130f090501021b0607080606030c09120d081b090d 64
    0x702c42954042e0001c9a8450026079200a0180c10981990b100c010b401d28282c8004c2c801c8074001004003c40618282100c4c2c44040c0c06a400008070250207c854000d84840c00301d54510301440c0d001e141a11030018100705110225171009040387c0c244c01003c1e22021452842c41d8842800b400b403550080c0d0b4501440b4202d1406800c0801d0743f0074060240d440c0c18100c400844d42075480b030b40100d41812402031042d00115850312070b4030300880030840030304422440618002d01501c22448003420707204000038840790241199000f50360602c1015010008184680b0b0900002b40e0900701c2c06000c5600c40c2c6140c43e40460500190084c004000e0450002c2d0440b00c0d0450010200d80d220300c000380d640d480301c2c040000c2c03091000f4042d10103030002001d85001c04418080c5064801042030040103101c4c81031011b01c0d142c140a6a812000b200e003c5501c8594441c0483e42070400b020813980d0305e00c2004041c440b010742201409010f00405046491071803c40d21848000d8443d08120982107112880e224020500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 797670620 1250 797669370 797669387
    0x10080705030708150a08031b0309091f080a210201050f07140702030303101e180525030f05010605070507030f0204200306010306050904051c09050a0303020313080109080a 75
    0x481c0c0384c0041c4c1503150313502007031508845812034a01c5034400642e0520200158408070240c0d40648004c51401b505030700814400003000c1e21109a50607002e558180799801075544030090054101195a10581402c02d16444c0c00240000354207942e080c030031615080d01c1800b5091007210a80000119910ba003a0122501588501400c1c0102000c0c0322a000690b810310040d4040d100101040b0202d130f040004121001345e0850803640761444000041100d188401e2440001b00c103040c0c0700203621b5842041c842c101c142d44030891458040b40c480c801d0346258066001e81c100c0300c5682001c000d0307030380c9664080d038003442601c0d809081a40030080c20000104440e48204200d0b101910129502c2e08114010401c503009644030700d05910040100038a0396498441c501c0100b001300c85142c01410315448040c4c03140d620192004c0420420300a04c8051030142e03103400010000a40728209841d50303810000c1d00c0e40c00a0722030001d2004c91050004010005000e540c805503000130500b443c2920749002540d6190 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 797671870 1250 797670620 797670631
    0x71b03080601022e0b03010506010804060915050109020a080a0b0102030d0915060b19020c0906062d090306130308010b130504060b0a0810030804060c110d03020a0210080705030708 79
    0x421302044100c2800714074442410b0001c401080d20400160701229420b49540b40040340c0241c2c500810042560381c801c03552a000740d0040301c00102c0d8030860a01500d000d07110f01c88041314a06040c000943d21080c0c2d8002d000f5800c181d920201583c84031400402903c5107041c440c0d0040c1d10501804107c009144c6c080c0b100288a014070740400c90300d800c600c2c2c00791411648181610f43c07020030300310b4240214030001c2c03114079002e10144c4551441d0100107180120044c1034180a4280072801c001d2640305c1002c900045404680c42c612a800c180441c6203080d4004101580240901404100c031450329090600103036a26032141e0102da820500704403400c1d001048411140400b50750300052a4986209002c06842020340f280c1e6503101005016000000c00f40840705155000c0e0700404c0401c7c01d410a0f18203031906858400941065402c01c0c8500100e014521540710300040d2440042540004440140c1132003507075003c0d01c50803940c20548201c1021100080826010000144801e01c60440a40d110 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 797673120 1250 797671870 797671873
    0x51003060305073c0b070501151811120a15030f0b01090605030d1202161403030a140405070302190b030708063109020a0b0f040905071b0308060102 65
    0x641c1d994558a280010315400400314442400012210122001d1061920407581d10703c0f082280503601d500007840e00d20b215042101001280141c1000310039000142206440c00c0380c481041c1d2103182400a826145a00c210103616040c02041d441003281e0540d2118003000454045641c1d6000c80c42010b40350882021440400d0f02c02d0110000b02c41d00141c1464a00a28090300b2560400c0100c008030f41c00342e04418829401403203140b2083c0d50004400440c0414000c02584036001028a00070242c41c40c08010301d0721480302c42c0021185000409548901d503030304020700907420030241c0617221500035500a005604124000d00250801d40004403a62007500c1010742c001c2c0c0d440418120581007a40c03d0b4001607841c0f030034040c003417401c003411102d08031600c00001e2650b40001f001407000c0c0e1642d0407446140c3d858031052800c1d9603845480000400507001c0030303a03403007840b0b0038001240da100d8001d0030841860310020661403407055441c1d41c040380c3d002185000d12520354070305842882000f840d80341103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 797674370 1250 797673120 797673131
    0x40509040219030f03021b030a240f0917120103060507050f0316080f0c0d0506040908040f031203050105150702030c060a0e032a060307110a0312051003050304051003 73
    0x702c410205404001d60045480c81039401ea5440c0c000d05005000c00721900194120012860950300030460142681e03010b0100600f40300500103040941c8201c1c28030701c1000d443c0000300d0a00100d41d410060030544103203d4041c1d010710070306410341140603203079411051034810801400050450b80c8500c1d049141800c1c204d04058111300344003103035442110301088420744a800a0303c06900030a07810341145204402104920b00350700c18994038000c024111807000e8951004c01c440b43c076140d201c2d00d40280c0240b0b40d550303611740b1503000001c0d203841840111560036445030320020441c801d10030035050312002410521540c06805010496822948040c0e03494003c100c440c407255a1f40700001d00801050ba00c540612400c88000c160401c01c181c076103e02e40a0b06421001c01544c041482801c042c40d00700d842c0ca803203444051089410425020086c1d40705d2064004000c1456008283c28025508a01c0d040c80340e5a680000061040310340e100080543d8410701080c4034611f48090b40d102c40e02c0c640d1500040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 797675620 1250 797674370 797674399
    0xc0204020703031d0601050603150a050d0b180102030601050f030415050a0b1c05030a08071413050405060f0f0f010507291e010312210b010909110405090402 69
    0x101e900210044011a03500d00e01011034020500740c1101c100c400340f015040b290b24002c08507095200040110002ca0048080c03642c1607030350500a00c001d040052b003001400b0300a403070540807515040d101400d101c41c10080c0c6034000c8405000701c0b441020706940720f909282c020138100d5141d40010f03004840c1c030000480248982d842c584902d510941c0300110103e100d034154024468580d482d031a841500c2c9508001d50702c00304500000b1a040b441c11494040416030326a1803ca0301610b00d014540b071070b614002882c00c1500310801e4644140da808072020801500c8013010070241c4200098a0350300180941440420380c074204120b0020b00406042c03d6203408072944c4c4004084055546007044000320299404100b2490035505902142c0108182400c81340c18800e080400c20500c0000e105090500e03000ca034003449000c07901c044802c074101c0166941982c0070114080c140c0e0448136800900c07007220004844000d4003600b540141d03691f840794940781c10042400a0301d03000600a136008850880100b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 797676870 1250 797675620 797675629
    0x3a0306050d060c0e0102150103120c0b07020606040b0f01080a050a0e0102120f0a02070f060203060103020d0203090a120203040b090f12070f0e0606131502101104060207170d0f0c02 79
    0x6242a110b05000a4480c1c44581c010749183c00681085045601c01c040c3c0902c00000028a141941c0d0401a5030360091104901205c0800038400020314032145081800010b5400041c160300404007260b0a00050681b18188820b5415a000090002e5a0a800b14401c54669400b241d04a0400c0a0102d441515942d115003603910000702030001c071000c9810440c1e100301001000b0b40080d040d02c2d05514117001501c0e65500c81440c0170300134064a50008c007042c5503a001764129400d03040300107000c1d0340741c2c0f800f0741c134071520760303c2c8900c06450044055902c40b8940d480801240c05944a42503441d04001d03601c02440800c1444515003508410044403030034070f500041100d01c00814407a02100440c03802d08902c501102d85c0a80310500524080c841080c0e000d100c0140d81081d01d510025241140051400403442c0c07a030f40a40116106280c8828000314a01c41c00083c0240e03445a02181d0386c4aa890b44500e20f0410305180e030302c1e501d0300401050207183d8070400b140748030501301d850003404c94019900000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 797678120 1250 797676870 797676889
    0x5070e0a0f03031404030c03020126130302060601140307030902060f030f160207060f0e1306090e160f0b0f0d06080c041803090b1e070b0601023a030605 67
    0x7800d0700362045004108040d48440c0026540215400f002e007014910380e2001007030380107400001d061040e041044030050b441d00c60030307503209071004401c0d95160511042c030b005544100503040d0014080d1000161544d4020220007010904c030081062860b941c00702d0403002000c1c4d10400b00d0340094204120122846000050340c0a10302d0007a60b002942001a0410601c0410715040c1c01550043e440400002c1c1e0010841000700400341045080342d910040010030054105210310510b5180100201d003208955110f0300c0d5901c550000c54901d58560340c03014501500900c02c0c90144200500e051000c000d00c20044c1036580d060208581c10061820f0750081541d0003900010005c3d0700c000b4034680c1d185001d02034841c00b0b001c1841c0407a500300c4c1c00e4800800a01c05070040028206c2c00087c0810340544a148030f100e00c050403228591a408946003900a181c0e080d51505d006120300810401c1c10344111400e01a0040d04600105600108081d075401500c003e501c05c005150341c0b15000122900c030380e03544 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 797679370 1250 797678120 797678129
    0xc2a19170c3a0c23100f39050a05030409090201020c04090305030a0b0a08010c030902040621060b04020d0603051c050a0f0c06020d02071a131505070e0a 67
    0x1146a00046144012481500405207003010b4141c400c5008100718078202d900351078001d98140a0389848081210940c43c1c0c400000e034220050850400016500c40d0840d003e0500139a01e40144080a01900301804820400700c41440384610540b01001d0010f05c0d11110103104a003034506040a54440d241144c005500041d96551640040821981d0500c800925003508803420071009031070351801030090000a00c1c03003182c3c940d60000300c2804da4802c02d40800411101c0020f0200d8003003245d00030f0280c900310408034007440c2408008119044408401c00c0c0d500d0701041c00400e00b0362652101c402800c00540c40640096080101c60308102e203a0186030007441c0140010550050b0701040d45514200181d060410000d051186400c2180e22041d1007080900b03c0c94a501803408a0505c04001d10404a070f4512a80c4000b56000400008003403078240134031070103951540c0e0750310747e01440c0610f44082c50080801c0a0030548004039055580140d4100101c0c1ca0308024010600010698560681d0032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 797680620 1250 797679370 797679409
    0x203090114090607121109120f06070f2303060d0305070807030504170606211006301106030405030d061e05040b03100c050c2a19170c 59
    0x130030000c01e0f0031031035103521030a420004000144a000d540581030045078002c0e486481d00c01100b580b60300d0b040100d140842c405605445040c1000200a0f20315440c10304034101052000c42c1c3c0d00c45500c882c5090400f180780e110081884c5955181c20000740c0c001e072440440c2800014001200401c9110015020b128400d46032590794504159000b4250f00316951140d400790300003002c011540d142d0742c002850090381c1d005020307110028110b07a113080150402c01544414608440042e14600038400314402d4421520305000d90070340064213203038172000346001511203c00a036500505080800c0150342c014060015070303041410400048041d540f56a0080c5902c9a0a940819401c172070242c0640052204890070051850b1441c042a1900d0442e0003055a8940d61851005010702840c11103110013108002e4070030403c0c00c845500c59680c2e10264540c42060100c8108c421800c0c581050040f8080c05d40ca81040280340025090788080c5513091080203018100c404070050b00c90382c3c0202c903c0900201d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 797681870 1250 797680620 797680633
    0x203071107031a010b0306220b03100507110d0512280506040b040e15040804030f080d1506020a061509020d0e100612080703140a0c1209051003020309011409 69
    0x200c180c0103d030b0301a0450340100c1070400502a440e915014250f00308200100c0d0354a44512282c01c0038010038160a030107405000711070802c01c4004081d4010781c0b0481d1140c4800e0440540c0851460751f03007580b6504100410810001e00070301c44d9106c400e503540205049600310009010708c000c03480603011040341005c480d0b160701c2400280e10340b90041c84082d0509540800841092003529503452002317030444002a01a20302203803e00044008403009075800812003080c0d030200e0300d01540240c0c4404c2d0800400d03450f01e00e04035038815400303850303008550a60f03005211803880c64541e100107108480010481c80c0e50075000003610340d2940060301001c1041400001c88a5400032000e0420340c0c0c850511a05600d030510500613092041c420501d501c0d007280e5002c2d04c4030428038040d03031401076002038410080c0300840c16041307441d8010b890a4021f4843e1140f020078402c080300a9940681a0089a900c04117540013044100c0c03095000e154098000d10002c200d05401d1090a14010030940b01c134030701600320300f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 797683120 1250 797681870 797681903
    0xd0c080f0406120c03020906040e0a02070f1a07090302090c0a110f0a020f0319150212180c0d11011d090a02090a080706051e09031f060e19020307110703 67
    0xc2c450840015840c3c1411b52414401c440000c1a0780b1503401390f40000300c860b6020504034602d55041e80c2c90690700849210141d2094107200200c042071a85c071024200c94080005d001c21304c03480c61102100e9000d800c5002d0380d280e141c80c140494002e000e00008202c1e40e44034101503540c040165200c5001d004014040e101001d005210500000d0311250307000e60706c501c40d0341e040e0f0012650341182a541003042e110040c4100c0703020328042d1058a6180b03400040701014401003003c00d801011902400f00211514103480317005000c40042401000741c4000084810840154050360411000c011a00800980c042000c1c1c0015210882610070741e0030654003003524181414418451005080000f000384441072401900400b42e100b001c00c0c0b0342c041c0300d900342000305242869042d01c65020004090311312001c0010b8000c582c080381042a610040e0034640002040022088224052820b4050480610340d26620000180d440900503408119629541000b84401484058080c61190182d1360544415 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 797684370 1250 797683120 797683157
    0x50a03090209070e18010e01060509030328030501122a0f0e070f1713020f03030307030f23130f080f0307080f060d030c020103060504020f0702130506030d0c080f0406 73
    0x445c00c13600e206140c0b003c01842035107100c1026a044801e00e1a05c2c99075041e4500211707042d80500410150b48d01c1c2a440d8040860300c894883c2c0c0c500082c55a010000340c0e0342d50424052301c40c0a103001811181200c00712000000722400e440326642c01c0c601e2191001c564820003085001c800c0c3c1c0c817500c040400b4205110715646d000b0007000c6400c84a103400c68030701c03048031520800003201406007201650012550b03000c41d260b10460507000d8200406890f01e91500303001c080c0240c010005807610711440c1c00d100c4007103210740398214110b800c0d85d07050204969131145c1c40c008e0b41080d03004090720401e20a020180000340020b005102146020001c1ca403a0305001e20003070302d00c3d84040e104813001004413003003041940382c2404140c0780c0c58040c43c060fa520580b6000580050400340c00c940c0d042400012014041c0031118010020b8520030303294204207245a5607420103ca10a40300e442d03160300418042c1c2016440cc504c04070116010710300035840c00b0313895201c2c3c0105602c41d0340501d020848541c9507401c031110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 797685620 1250 797684370 797684389
    0x130902030f060a05100804021f030c020c090c04060c02030f0a0f0c09061505031509071d190e1b03071106090c0105030c0c03040312032405030c01050a03090209070e 72
    0x2003d40b04071807407a0901000821840116800740100034002c00040e0a6640e00071005440c4845400020500292001c00801806041c0d40503000b512070003a0700f0b01582480d050452150907403403801d500300350402c17504580c03610510f00140c0c0d06100c0e040b0007401d035000510134a1601d621412401d0a0025186000c008880c65a40b00400745440d020042010a4090004114000c41c03450410b03640c0da94443c00b24240c004603405981c100151008206031160013042c3c6030f224441510043d20020700b4802001144494002c0010486401d13907020000071000495860300004408599241c2413584e0728250225001103c103040060181231b00b100c0011420b020494101d0040e80141a4002842c00064107038800540103014000f0700080c09400101c0074019036002e580e001000010700511010020094484455501194980240006884140b1801c89811078001070301401085501d2401900c41e500440f281505147d2a0340c452700069407405a5a1300c00c3d14075488811121620314107200d180742 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 797686870 1250 797685620 797685631
    0x405010810050603070c06090b07050a1205011203030c0203040e0f040210020a05150603010905060c0c060f191a0d0f03120209030a061104080d270b120408130902030f 73
    0x408081042c4810303240c100481340d1010590030718007040281c0e40740c010024400300d0009840b540c034140c10700c103105072700000034000b06030385640f00115058124a210125075082c4944200000e1203603c400000e0301a0b0002c1c52070211a0064038102a070320070000903000c2c4d04440d00c42c0c0202d01035080004600d4203e2503c00920710901c000c215070843d5982d03250340d0f21420341d0a8241e4900c0400010020369094004040041e80070040e110346003002800140103401410004283d030003100005244201e04540c80352080384010103100b803200d91352055800904800c0d4034000000381f20300d40d00d14543c0302d00f00705440907403180c90417110222185c10028810400140c038550814010400c941c0310ba503001841e6070400d42c1100000407945200c04450710544210b83c400d607410b025400e0101e88581e000f400b551001c1140c904295070308020006418140d44c1c1c1c50040f0071040b9414000b94044211a90010f503002d4454031b00d480c138141290600003490541641b0401c0c0742c0d5000810088083e030b1100070701d80c018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 797688120 1250 797686870 797686891
    0xd020d08010b0d0b0402090312030603061501080c0f09090411151303140c030604080a03050c0304200f060f040807090b030705010c1b0e0105190305060c09031f0204050108 75
    0x7035042405689051090a50f41c0f0041516001020755944c1c640d03045a003850001401c0314040541081807422980080b6a1203101c2e015401c000740d000c203003c607000701440b84c0503035407010315943d00b41040c0602d421060344881d40034002d020021044d01c6590149002d54002d8504900d000141e5041186849525446020080c02400440c0c1042110003120017607941c010100012246042501e038641081c002c0443da161140350140814030211070014550180e07150b40a115590710380114200520041d90020108404011014840c0b4074056041d0b0100400030206207142e0348440c00580103410402c042c00c3c40e14000101082200342c1000104010309150314140124000c00740026269605441101d0602804868907400c11481800d026488420300001109183c5c1314150020740c1d00c001d01500d8041c0c5500d00580759042b1034141402c0c01c580c0c0c4400100101d5a0306c00403000305801c40f541940d00b6101c2c03070320141120317900303a00950110306202500503120b038a0f03e0001090560090032034481c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 797689370 1250 797688120 797688137
    0x131b0e07021204180f1a090906070e010e030a0f1202100504020a350d090501080f07180f03060506040c170105091018141f170f0607020d020d 62
    0x4580c211410740c0c084884c0000d40004121000f002100a0820613a4000245140004243d0703102100101c000440c1016545508581e9440d0080c44d510401600c0c84400720ba805007200540d50301c11036105c50403120240c2918515200c030380e03441c480c44003655001c1703910f10140c2024015103035040200090b002c0c01100d0504c214180f6030003140d40c00c2c441d40203003400e9003c80610740042c10490402981b1040817814032007019041c0842007915100001c0344040003645034400021558420342940e4000c031403113031961070340c2d443c5d01000b51940b018207201c81c0383d82d04664a00040010355020074000450040401184510b070503000c0000700c03042c00c0c1c08502071081408201d024100340040d03250545805482c5111241c841d56a902100000d036440507110f200c200e004032242c00080c0e000003c84000c44e20b1007207115100c3c4054420700058a100c54011800028030401c030215070401100081e0410b482610301d10b840e010069818014115105005684442e04c0303204956810811099484074500e0100700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 797690620 1250 797689370 797689393
    0x91a0402121f02030403020c0d0503040f060f05090f0a0503030a0908010605012609100e0d0f0e24070807030906090603020f0d0b03010b090a0603030e1512131b0e0702 73
    0x800361660b0315459000c90b03000c40002c08140c02000394000b0801c1c014840008002103140540c4d0329800740c040c608512145101c005070702c0703000e01c2c3d40120409403034460070304201004041c068024000282c0c0c42c0c1c8011400c5000074281c50510040080c400030b580c490340c5040c1480402820340d43c0b0741d40f140c0c1c10000601d500310220300d801241511142c0a80c9a0030040d41c0702c5010b002d02e0040401120035246103403101035941d5000009e05d4040c0c402680d22480c144080c125410745501c410701c03081c01d07001394042403a400b00a40c940284a40b1101100c0d00c24100f007640e403900202c50b040a1412404181003510601c2280e400004003c0241140d1070154680009002e8894040c001c606070110800d803145202e8056540030340105a0003a00500001054a01781490034068812032006602040c41c0700140401410034201c004400078450002071300e4200760030789020f581032004007844692140911040005a460b40883d81e8821030312045900039030604441e440c400c08003030400030641d1b1003800180c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 797691870 1250 797690620 797690653
    0x5060d0b0a0b041e0f050d140a120305040302100504050d0311040314010b090a1109010c05190507090e03120106050913060311010f03022b0e0f0d0e1918091a040212 72
    0x240d0b1f855100e0a055074060500e0401d030710344091001300400304140300034511442c5034590700c103a2140d0300a608842d20b803c9080108411540d0968020f491038100c1e600203031410f4000d030800071400801d400345c68981950390b00d030350912a03c0d5000e00401ea944a04080c0300524201c06180c0d049071100307000700300307401c0300e400304892511500505d10f050107e1019004d09110301071221000144500084541032003007031030714a031100014042d42d0000c601d890005088602e0000079904548040b004501442c0d00b48841034900b504001c107000d50060703c40c04007a102c2c5403035000c1c40004500c1420700e1140b105c5804005000c640340c2030b104404040c414401c00c2584181c403021001c110011844882900030500c6480c0040e01c0361940010301c921070850541905040000c0c102c42107440f83d42d030940702d0030071582007082980301611140304c0404129401c0c040d8401080310814401c05c064800220104181c0e00c07148041a018002895510014204800d50074601180203050426001278010307172002e900381c071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 797693120 1250 797691870 797691889
    0x50c09131b030209040605010302030d0c0503121f0f06030c110618010b120f0c0301021e030a06090f02071106160b0c041a070312050105060d0b0a0b041e0f05 69
    0x2420488005110044140072204a500a99009050511189030508022014200c20b1004038041c2c4100044c01012031f10a00880700f07203607400b5000d18501040308018030b401072030140142c00b00c5e01c10301c0d21075030070708001c030988000806801c41001138207450640b0280440b02400b060106021200c0717030000707140c1004250b40d80c1c13203250010750482d90214481d803540101091214150821506000700034030b10800514010100185412101c0c8503e8000500d0b00380c3c0145450400c9598025540c0902080000c028581c003da05050008075036036a04e5034030b01513400c0c5040702c0b140302d503000803c901403080096015a80304003c0d83c1c040d1910208183c00c3c684040103d0010f442c0d40718640200e048003030705c40700301c3d0014925014940ca06c0e0502e04402309103a489640100c2c0440c04058106d5074074071260143e20b0403900020304890621580c000108043c00ca060f02c034940c4200c3c2000045101210440170304080d010481001a8071549078240020410498020001c00b00d07500e030003001540d07184041c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 797694370 1250 797693120 797693123
    0x402010e120a08040b0405040506030a0b131406040606090b03150c07030e0631120f0302030c010f0203070306052d0303040308030903090f041b0f170a0603050c0913 72
    0x2010807a46101c4492070915050810042124100090000740040440040d0003501c804441c10081e0b074850a08056544440c844018980b001b180000f500c82c1c150000140405800b40e050b071181401001146810044102c904030781941d41c0300c50601c100b0589101c1e4142e1504140e004100d00d600d50801400c06860041003881c0c2458005000010540f00d240300120780000641160b841d443ca203202c0d0303502d03505003a4811b0705091103140700300785e000d03001c400e410100c594551044444028545035414013184044094055100c200800c0e1140c00e1b003442007841040c07500100607140d00380f420006064880643c02640b1680c107408500c0044905d04110381e00815282410390081441403000c603055000c1e5610103040002c0100401404090120080813444401c584440683d4401d9003040100c4011804502c0040741e040e04001a40380140c0c0c0f40c1d80001071070700b000c001d081d1441d203041900c2c0740110360b10020540c6800e0200108402084814114042140c03c5c0c1581d203442d6010380c01d8035941020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 797695620 1250 797694370 797694379
    0x4140d0804141002070f17130303230705011b0c1a0703110a0201050a05161e090801060b0d1b14070c260c0405070507020f0f101d0103050402010e 64
    0x2040080702d00c0801c003c42d603e0024000954599035035013840b04940088140585111601c2d0501d20842c01c5018121120039114402034500c0c2c80c1507440c221010755090050444501c02985010709583d415000f80c51414480c0c00042103541d055803801c85040241601501800f0358200f80c00c4c00075814005205012a100002c5c80050baa021001c0340589546402c0720342c5138100052040b030301c580c10740000d4410b2000c00018045519001c0303011a06008191192001030388103414403c5000b211785502d048910585040c00c0350743d0716182d2031406c55015500c40d0409200008401c8000009070194155142c40658005180e00550002601c401c1820800401d05140004d00c41c0c02c101d0740084000141001c00c1d4250584004880b0070700c05401d1b40300c0b0350034080c852440c05020610f014040c441c411002d035941c0a040402079821310400200b5114460781c0051204407049840c0c44015084800090617512064248040080041b4120584100381c0c10982040104005030340c210780c4650806401b9103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 797696870 1250 797695620 797695643
    0x1080d021240030309060801050d03080f0709030222110301050f12150a091e02030714030f010903050310080106050906120f01090606050a050d0b01120c1d04140d0804 73
    0x452514040b001c1c02441c0ba41014020710200a26900c2030061050b200c5c180c407005041d988500801c8080d60300040001c0c00101510002084c120824602a81124a90030710444c920340302d0b400241441c4001621a40c2032000754500c96a0b48003c0c05080c00900310003245a20710750405c00403074000029101c05034000e0684030b00d0007640c0c4500f040b00800e204000c10300300200c0c1c103003108958090205001c0a0703078040041e102d0342c45407050200790503101c40ea008004101082c68829000310200a03030302d185030716000714004524458403e0040c0101d5500c0b9070340b00d03940c0f45090790101384c030814650029145685440c0b424015a00c800909540145080703031802d074400351030091903251811f000c107080d045500b0019140104141a00100b09440c402c552801c5036a07220720512010703446031070f4040c152140e03000040043e60128901040b0705800384444500542d10b0b01581c0401894215400c081700100c041003109005802c40c3d41c2424116a40c040c6c0711000c02d0150007041e40002400292441e410b20 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 797698120 1250 797696870 797696947
    0x2250f0b0615121611060a0c170103080d1413201801150e0d02040c0201110406091406040e04110a120807060509010506060d0b03030d020301080d0212 66
    0x49000241e40342c0c03518060354480100251202c02041901c0c2410034054501c1c0c40c1d004513003d031140094040618004048a9a03100703550005407420710741c40d50a00a065411425801d008036400780a90b020741c00780d07680c82200114210840340700c41640d807000341810083c00808002c0c1c0e6103420351250440c00c404000034105041c480c55038241200c0ba5800b140b078103c01d4001c0c0709400410f80c1281c5400c00c0c0d01a00c0088a403064074418a08642181d1040004800c2c03001491b00e0b50205519498034800001c40304c200030907041c0c003603005070003c0c00441e855030010821014a0b51036158a588180c8580381001d180000340b0004040140000304064800c95030032510b81c4030510454002c2c0034680d12605141d0003410843e0142d440240155034460400c00020620380050254600401c0e02400b01442d190b1102003c9000700300c50700d0040d90500003003010a841c00300c240050b60180011501601d07800301d040c000603142008041900820a4052058038200ca80180c800c81009408411008400818 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 797699370 1250 797698120 797698129
    0x2c0a0f021801030b0402040507020f07030201050d020403080f030405010f1401030b180102031501080a0903080c030a0f060611010b010903230309100509090117033a02250f0b06 77
    0x5044008144030a07140004188003070a248140124002d4400300510303101c1000880c0c4450348142e80344850b5122410420043d440f8400400d2070712014038006003050340700e90b10410540c0c00b450200c01c1890001c4240400d106d004e101d41c610068142808004852200c072000e88015014480030b002c0071762400001d401d84802c2403800c0780000c280b600840da0f074030b0403aa07581d943c45200602240020002030000307030305d05c01e0391148084903034241d11900c10700e0b9200b1f400c02886070704c010300040c21a41c0303600b1610000c00082c0507620103010561544030007039014078803090840b81408101d50400c080d8840800c00300b40e0020b02100e000c0d940b11140308c8485030040d105851841400c0340541c000803440049680c8550000c00303050a0b02046801c010315076a03c41702c10b501030307440070a00c98107a0001c104040405244401080000e03007008110080c19031b0f428594050b43c039030721903040300c0d80b900058610303041004a91004840305109800d140c1d0001e1984603c0103040740e00c0310080c688000d0300003041140e5103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 797700620 1250 797699370 797699389
    0x90d2a0602071502130503030913090f0b070e01030c031518241a040b0f2505010501060332060d0227010b120403030902060c010c032c0a0f02 62
    0x811180503440c295040f25000020740c071881c0881d50391550004040b0b65407a003c000c541d00240c0c014041b1100c070b1207c0400740000c081120048940144603524440000e480040c490b1151030703540c4901f4040d2100790005426954840f540d2420103181151400042c1030080000041da031105011160b0010444109001000b51070300c804800c00901150710030f026211500c900070768000f100740c1c82e081c11214012404500403400794041c00c0324280f0818480030000c901404140888600e8600882c001d1110503081610896007525240d4590005210494060150031004a125a01315540035075050300c15854002c03420302080c241d031040c0c0104505541e40b041149c440c0d90020005201701c2d0003080c41200e040101a4090b5116060314000100c22500d017003943c51118103926510380a50b078581d000c4004095550301203034001070a11581141c0b0341300744a40d05000545032000940301d4061120440c91418120f50a00e49a0b400740040f1801c08010400380f580e60f5010114183ca1078640c80080c1e03010702c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 797701870 1250 797700620 797700623
    0x60504051303020a0f170c25030b0c03130204051303090e071709010605060a09090b01030c0e0d02010c05100605090108031612140a09060e09060a05130e0102070b090d2a060207 77
    0xf00104032031b508280003141d54503401230164803015690202088064800d20b1a110141481e03d802d400038190440346002154030041203058110308055039130001d0220303901520b200741400d449035015070805030030180c0070700074225881003130b00b0f940360480b002070003070403d041c0c6160758451900114404d010b00f50000b00190400034442611641180300050140015108400c401c5003001c40e00e0700b1550088c420113403020148c0e43d0360300b0304012001c24401c440385502c604034100640c040083e00400c2c1c0c2440b1141e100140d441d0085051403a00c01045000c1406800c00602e94104125041c5440e401c40a00700203a580001c02a90480705044251200e40b0035048540c3c040c140041d0251910354040a80d006032800b03078441984001141c0c05002c03060004603449c0c2c2e000900c1800502c150315001c425260780e030b600003202049822169880d00e0a98004000c02c0390101e4061040c01070320101440800042c06080c5000c04003490505000b090707254000c45021504052084c410042c040d0540454080c01e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 797703120 1250 797701870 797701913
    0x1005040306060303020c0306010902030f040327180b010e0f04150f06080a2d0b03030f0c031809040b0f1302100e030c060a020c090601180603060504051303020a0f 71
    0x2c940d41c0c24040c0d01c4034511400c444c0300380619000403c01d005940700703803405104c2d501c207400555500c40e681030f00c050048d484252118000c6034032014514200d031946001070b2905c02d58050458170740e010800c00707841900508070b06006c0345c6c149100d126144c00b01188403110084070081640d2945404411900604ea049154000c007540804150681c001032054003444942d101008001d4010702c104074224090381051402c1c0c60020504007040f500c40d00689564000201904d141070003540000709994804400c04065400110b00d4001030010300d204c4001540c410743e07805105180607a2184140d0b0340081240450444040100340303000d10241c01120210ba02501620b0701038036801018156030100b0024901c24450a80a0603550400c1010b0f220302c003a06800414400d440c0c9000c000f40311900400f2030f810003882d0400c515942e004035001a0007084641c40004503682402d0500c401d56030010700100404028008800000e680008c8034a07240d9040403408921902d02d1030b040703100c184081c24110b9803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 797704370 1250 797703120 797703131
    0xc0111060f3c221b1e050315311a061002031e090d050114010e07210903180f060905030d140c150c04030b0a0b0604051005040306 57
    0x1409151482106001c42d01c0001400558600507900d04038035003600c1c4800d038288401d8040002a40c0141d000700300d40840320400044c29200c40100e41c2007226000160145c20000c1c02c1008203080c140310680090081c0e10803000c81d80380100610050b1401954500c3c800c411110186021101c80568405c1c0258010f41950440310740c4440b081348410160350191240b41c0402880d0301f49030000049075615002d40d1142e86200c4640141443c1316081030408942248610740c0140003e5000e214650030032011883c0e0b01000e504205658051003801407240d4140805400340302440e482844142810300c1c1c0c0110042a243c8452404031058201d45114410407000301201007030030780d000840c480503030f09640c1c0c2e40300c010790f5a002010fa03203005220b11200403c000310000180c030030401e40186540284903084503001c040c490b0803607600e07007821a000b2858080c041014000c1010551a50360080c8005c0418401e0000c2000021903600c1103124481c0704444080007441014051001d03540115001340c0304014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 797705620 1250 797704370 797704441
    0x10506070503070215220e07110c12150109060b07080d021303051c03230c070f210309210e090a050711030403170a031407020f0c0111060f 61
    0x1a04515045190043d0604800c0c40c0d01b2040550802194a0064403418a444d0000141c440c9039070900141c9d01c60160480c2c001298813452616000884107800070002803034800f45800d001f02042e0000780c0c04500b000010025130384150300ba1b5043d0340d005034206036291a1418008000d00c500700d10a41c1c0001c030850700100344103001c41c0404000703030708980158411070078a0086013250300b807e1500440c1c84a02d06e012000d0b12013400c00e141d0041120803240d01e0034510b9242e144c01d000d0b01f19000c44101103556600a005006601011003002c19802c040c0099001c95581c1d03100705441c00d04003c1140081c40030151214800c0810180c1c002000d000e418103802d01d09100006010221003013004030b403034410052900d0344004226805c5a0b0407070440b420302e02c2078501c0310030103a00c84e0418104040c1c44400c0c9400c01e91282e0340c100c3c060b082d00c4e00100020401482403c0c02d0000b10303c00c2a05020043c00c200000303440100e811a071210301c0010241c0300c2d03034a401d56146142c201d4001c0180508006901c400c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 797706870 1250 797705620 797705659
    0x604050f01060b13090506010c02130b0a0609030b0708090c0d030e030c01140f07050102090406081e03040807090b1203070b10050a05010504332c06030105060705030702 74
    0x44403845030024000903855072400c401611030302403051086503071160100800c4140b64000c1d5002801454000c50002d00750300005c4850000c404a070a035540e480b0800c0c0d4951400740019401080b444c01c1c01d00311a480e540750100c0d940c500030400410321082d070b0001011724006008015440344014070f204141e81890038001e0680e1641044c2a0191050001c225103940c003c0d15a1002d07200c00680d010302d003844103054010345400454040702c0e199000d10440100340d0300c6000d11009008044001d010f2924070f00b4000340d044007070844403415500b0801041c0402107000c15044192860f0b000007182d08882000400d00b0b0540340440940365020102c1e0a404104050071500d000b1010302007115802e0341c450f4100201542c051180501003003080008000c500b20b81040c03580700b4110640007000d07101c4a01e082ca21101159881400041c7c5030b182c041000c86c6200f000d0140700e41e100d150110380e804840000c01c46034481801014400e1074040703402300400c2420170465503003076030140541c8003e250b03541810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 797708120 1250 797706870 797706883
    0x1308030a090806090105010302030304030f080d02072121110412060618020903030304111903050105071704020d08071401020d06050406080606030c04021b03071208070906141803060405 81
    0x2c18150240101103401c03070f08140211410381e0b0300100514a802c0ca1603858590162504108880030540ad000b44821000346102405445014101003070b40714010502041c070481c4600a90400d1100c6e050582ca2848200d901c68081039034140800038201e00c1000041c031180c091980b01e109419921668201000129000041140d00f1007100348802c003142d140b010183c0c060307004180e4069206200080100368015241400a0805014081c12075140ca070446c00403e0241c2099035a130b9142c00520540d154011080f903001486040b803440c0609042c0c1c0010780120901c0409443c651000c01c081c4140003441600c05500401c0100856a501c402c1d91000046c00c154405c040c82146000c0000070705000c0410759912605000f8003a05080070b90350201f0000f5044200880805040d94840c100010810801844424000c20581201070554000240880c40082c401e808104511104101c0d141d0803801c01c0d502d05103c1c4040c1612240e82006848600044011407170f40752050320240300c240200130810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 797709370 1250 797708120 797708129
    0x90c040e0601080702060f180a05060906070309020a031118070c020f060a021c0e280b0403050d120b04110a1701050102101d12120f010b030402061308030a09 69
    0x1468903039a140801520b18100880321a409170308128002000b07150215030140e44254409443d001a14041c0740103032500e510b443c41107420364004401c4c0114000b040080a61002c504d107402c0c40310060690100b46d240d05c0f503100041130b0310302201c04000542e40f0049407010034582681d10744494a001c0500420300300350010280d0080402e00b00a9299040080450b6941300d8a6001032046081494191014469101c010410400c9050070340c241941c0f6401d40c9048400c851310811400b100c00007500b035401099501c1048175100c2080708000090011a2341ea2001400781414440301e004207160383d003d002e00e58030040d8894940b0744e00d0340003040d43c50060708a007a01a6151802e510608a00751000780f020b00403a409a4030840704060924107a03000300010080e400b05083c08602c6000795940740001f080350149000c500420844081c0740c010500a274010700345000c4050700e500d40411031459210141010380120700000c0d402c2c02401825031100001d00048044969644254a0080031107012303001c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 797710620 1250 797709370 797709389
    0xf12061006050703080103110102160b091216120c1509031109100515271503040f030804060b0d0b070e040b1008090f060901060302010f030c08061c02090c04 69
    0x40c04035041d8810350036a101a039041e100c4080d1030f421a200d10511242250701c4604500c10302e0810400380e42540c90707100041072109205601c603102c0c00204480007614a42c031503000d90142078038208483d0310fa0032881c210b41982c1000898010740f82000591080140c03c2403280300c003040111110700c6e43c00001801140d00850055020b0000c09081010360303201500d880304d281e4030406060000380350005840032100d50942c1458900300401920040d407030b41a010740e007520342e40c9014810450034050303541d1004504115199145180c10342d9800d10300d01c80502c01034204909440050100841548a0855030340c00802c614010012442c2c9400389482c121841f40c0005c11850005041e8240b41c06445118400104002c4040321428801c95580c400101040d04070300c00d20100300c0e5268000c6c0070f0a80a08d01c03000001c1031503030650001402142c1148519800c05203403445c40c0f49003541c0900c8581d0064802c40d00c25012000f0815104924100c008019510610400911040802020060040710700c03107103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 797711870 1250 797710620 797710651
    0x1141c05060d02031b030a060f150b0f0a0315030b040b01050406090b0a1404060e0403050c0706210914100902041b0503070305040201090e01180605030102040807090b0f1206 76
    0x8082c44040e03600c821000307401d54000440d0000b450f4920001990558000d0f0032200348642e90344501080d140c0d14841030443d5507403007203110410a8034407001005020000141860300c520444000c1c868458856004105591071a00d21103024841410300d00442d0080e820004a09180c02c2c246440c4c00c088c81030500c12860501c0004581946000c4c02e000a04010119170240d8a01000e4101110800c1c40c02d5910959034000818140824140f07107000714080c3e901e017610740c00540e044070301c2c240f0f40c2d4104205005034005003584075160040072081541c94000042034441d21454002101c4542e1146070015006085100041d480303103174001c1810500030ad40034401000c0c031080010b1034207400300134900055400c00014074003500039000340b43c0080c418035110304100d41c0e80a02500321a020303003100c2903441300d19900d1480e00420b4080c03000a41001c030001c514161074139180b9076980c1220302ca01c03414251600701c202d030307680e9421040c100411000f4100d5580400d0403079007079031541e8040b10709500c40001c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 797713120 1250 797711870 797711881
    0x20a0c08011a01180b090406051207030b10030b2e06230c15150301050a1d06060a1e0e04050705100305010501090e04060207230717120901141c05 64
    0x904c2c80d4205905440c155042c083e040099156141d40b140c04d000e500583c0b214000034075519251006001000d00e880134041590031071411b01c3d00410042c00a2034090810310040c004a00000085604010300d440c154070300000000749050510903070070305250448083d20002541c2c64100d03241c901d800030310103003a9202d0342c150070854034a400360b9000c40300e113a40404040340d05120046401c0360409494800d081d42040613200190079070310119851840e450f205c00305603405e0714881803940300301100d03800642042e192490104064100783d1207040e1100100c440d00c0c084001100b00034038060300d40e0300031045007403910b410041c0c1d03103c1c2140304440c00b0f2241e81000f0884103201c0e00c00d290586605035188100309280811401e214a009042580c4007903003000440300040342c0003201c40e640c0144144078000e41510b00c03100d9041031b100350b100310f104c030f40c0544d1540ca809102041c00e900e00c4080040b03440e03c4225200049a030010703620161928400002000103060214000c0d20a248103405014856686c1c0c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 797714370 1250 797713120 797713127
    0x30709051008030c0c0609030312010303020703031103070f060b210a1a0f0105040c0e031f0c0908031b1632030d0e060f120412030228020a0c08011a01 66
    0x141401c040344c1d60050f040b040c4840c42d1003801000c660400404a0303007030040946209104503400c2c0d0045000d40d000d03070401c000701a0420340b429030381d500e148091410502c070b035166a954000c4880c402820300b5500c4038420b80d280e9030441213814107040700014001038094a49803075a41c4c1458101554004d44030f008500c401111030320018490040e80078000030300c0c0d1828050101404100c1010400e01a0b801202d1465031410001609000501d09200c903182d01050b160380c084480020b192030405c07004103000d00c40801300000311040003048c0c1d11807440841080b8026030820f402c400088001c0e174003c00c40010a81e00d41881174802d1001c0f440d110701d07441c1c004140d43c044100c0710490b8075050f801c51928040c1d60fa002d0039507941081400b5042d545400054909400780d03030b10405a080300900c44100784000c1c0709845a109126071f070241011441d1007541003900e950a12241904880c401e450307241c03548035500c24065007445550180d08a0708050315401c1c018041c00b14403004190580c112000109298070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 797715620 1250 797714370 797714377
    0x1603050913020c1506060d0e0105150303030105060f1e19120510060c0606050909010903140403020d0803041a1302010201050610050301210c08150114060909060f03070905100803 78
    0x10340301c0c018611074800904540104e200107156551100d03050011582d810058043e6001001070b1742c0000503245400c9204880d80b502e0440c400307000e940140300600580e10344104642c0c070044002203168a800350719140f171074400b003640541c403401000482c954041640a0fa50641d10051a407900c1801900310301d074000131107008407090000040590410070070107000f0405800c4844c003903140458641d44400100c0d50b00d1109030b5486200d41c1d52400114185035010307010595031042c0d46519481d06146400045100c43c100002500d806070000114042000991008007143c252280d003550900d041c041707544038643c1c0d108060340075500f0040001c03102d2410b05040c400e00e1481d61645421a428584500b200c0c0c3c0010b600070018100040c1d8000103c0c4a80540e840100b0992006092400c00d82c00d210f1103110069208000a414282d0300c00181c1c2c0e10716060b0754400c24151151000d0741c1c1e42c07100203000c1c03d80f600f40d09905070141e0300300400c11080035001785109002c1041b14610a5682d071450716960311 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 797716870 1250 797715620 797715637
    0x10c14070803060105160f082101050d170408060f10091806021318020d1103090c060706090b0f06120d090e1302030d050c01320c160305091302 63
    0x40410000f040d66000d00094503019400c840048510300082c0e4503500c00203d07800301913030002001f281540b070000e506c0c50640703d0007000d04000d00301549440e003c43c0700303c82d69101c000c00007525034003040c10780c035100d2050b0b80081005a08072043c1d41400d5050504040d002d4500c07052100c140c00000c10850300070702034400603d81c211034400c80d0a0071a16040000d41210f081390000040c1c0c400d0004002c010903006400e10403002c400140e0b142c04d1090a401280e101e410650a400030a104000c10b130100400c0005c6003c10540c1d8040d83d8254030b20f40340000303040040300101108003050034032400e8000441540e00c901c2055903c0c00c0280640b0005035a0356070082c8802001811044080c000e0446000d580c580241c0f498250f184a103419900190812188020840000c1d40120702450004401d0145440101080315004035103080c140c98110038020b1404400240003110001c1610000004c08544601170080c031042c403940081d01d0020180e40c040c2d441c2c540301c0d502000410f5500b490714404c485089 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 797718120 1250 797716870 797716883
    0x2150c0307030e030c0102040902030f0105040506010c0b09120a11161a07020d050d080405010501211b170706030b04020301080d0f0c0f0c080d0f120209030c0406030302010c1407 78
    0x15a18068214081d04000c0c03c40000740c002800891001c41c000d0000e4000f419480c8005601ca15069800d40d118000591080e8800d509080500840c3d0340c00140340b002d5160000108900c5d13980c0c2c16104c0e407a21618000405403c440003e1201195134405e00c1210741e15061820b6541e021040c6040008c9100b107402000350580c240030b017084141030804014202d09102038031981e007100c00340e01c0302800d103500303e2044404154401c04001c1005004e00c0f9041c09003003200c01b403992424000e1728000050000b030341c004043c00f181426275110369402d607540c10014040d0348400342038000001d0140d600c500f968800c142c0400e0404000426030325090080e40e0503102204d00400303864108800844d0b4280032002d0240034807460308107203400b0851503221407400d40c0c02884103240d0f8503d000301007440c00c40842603070700c104000c00004841e00755201500350344481e0000f60168541c40c20b0300000b810403208044e000d030b0051604000000300350301904a2001c1c10305944401904080700c07a8400c0c060310442000801c103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 797719370 1250 797718120 797718127
    0x1a040306150612020a021501060503090d020609030307080a0b280806010b162a0e010b130608060105121609050a0b03011509090c02150c130b1e180102150c 68
    0x1001e0603130203011030300c4043c411075840c900c00700341c0040d25500030381000700015000010002120300400600300030002900c010011031410380c40c49900d900014061070108a020b8002c520f201085801c40110354a004152010802c02c3c40b150303208450782110122030348030402e080056040408a00181202c0301300d102d01c0c0ca000c03002540740f0f64408031100106d0341007680850711000a0108554408500c0c609110010914200b0360710855140c016070109080d140100548040c501c11150100100d5005041c10342083c0ca80b680103032418005d80a60020901c80348041000c00c01c0e40e180004401d40e00340d1138642100351940c0610056010074018400d00440c10401081a20000021218400103a1034a07203440c6890748203150a1b1124401c0ca140141d0004c0ea14220032440009140c4e08001c07401c10051a0429201c01c60b5401c034981d11400c00641030116207500b080d0112015108240c00d03045a040c0c2d1134443c09030000608418807840350040c881c9804402c40420003400060240288001c860f04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 797720620 1250 797719370 797719397
    0x70807030c0f0504291903152d08030c03030105091003051f020d1103041101030b1302031506040312020d0306031e11062a07030206221a0403061506 65
    0x31840c14074000c541d6401c0380343e0103185100b41d001002c2c1c81076540c010b107010b240c0c207481c0c20020282c400000700000c0c1040308210030016808081480406503070490301c01d101c03030810400ea49c814491075500403245808002020340000402000940c161075040f500c83d0f00c261a0a500c8450ae0750080c00002c000d0b6005404c00e003445c1c0018a82129108412200507240c00c61440004040d2500403000600399540071081c0410026104401080c003407007881d04005900704070b07000034540c40d03500e00c030318030180d50000205400c0140407c4030a1600030180400e03030313181d0b0f0360701e400ca041003105418040140540342d2046032403882405010b080326042281030074440105c0302061010381400e182203501080c0411000c2030307620b4104c0500162010051f0495203180d0340000c140058200810000d542c0d0000c0340c1c1803005035601000ea070341201e9024040c188442440740c2d1819130808940000d180710004021001c689415000100241da20900b000c3c0107803803141e10100720700021405440c0204152941429 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 797721870 1250 797720620 797720639
    0x504060806072106080d0c0b090f1e010605090c0a0f020f0d0e06090a0b0306010e190303050a110604060603060e0d17060102010f0e0a11010801060c030318020405070807030c0f0504 79
    0x4014219007200140450307443c445c0e01c0c42c001125461101282000f0244810700010702c158513485a55800500040381100501c2501c42e600c0c0031248040500b00060300911000035032140d009090090302000b0703d41407070300c00c00f03203160802203443c0005501e09442199a51011903144004111070000b800101d403401d600340c80314144448110f411100503c21030b081da03036406980c5001410b0b0380408555078180100010004a2904800d5008503e1b8400d40d19030b07461000d100c1401c40e80c042c90a55200c0240030411550040c04001700c404601c140320500c0103009007944036404481c8282001c01004040d185c1013900c4002c03000340100801c004000c81c1c2c01c9410201c1c5811351160051000003245400440c0c0034040350550504090b99a02c82e040c0301040160b0842c3c1c10b41200c40c00d0a00354a2580340ca00001e0444192400c020101602c42908105010307142d5003a10000358028020b21481c600b142d8010145802190704000080c00c01880b61745c040c0c0500501c0114001d19a5003510706410700d82101c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 797723120 1250 797721870 797721917
    0x170a06050c2d0d09060e0f070e0c0d0204080a0c060206060409080a0e13141504140a020d02040e012705062404030204050421031806090f1704050406080607 68
    0x299a0040c003000941400c2c41a4480c0c4d8282d00e101d0f01c4005000d4954054191a0610600e014030007030b032240000b48420120348182c1da60068001c42d610f40d55011449082d4080c0c055a444001544a016040700802c00c0005014003074988036400c4614540c2d40d002004140c403504400506041c00070031080110b0740c404c540620203020083c04500c8500003024020046540800c00941d05100341c0f81848001c40030240942c2c402030341140d080c40039031006011142e0101002c5d01c86050a680020103c1c410100c9405450042104d0000f9640c10340e51121403000740b0001007441100354484050700702142c01c0c1d61140340d005c2c0c4005030800109a2030311004c0d80c20030701c0181c0071050191040c000040183d6481c010103110300d03c40c80d5000b070000040e0901503800018480c1c08020b15003060070307003030149841690710000d0302d400130004904a040790905900440700080040c1001c6450503102d955403070180010801c540081d24204940fa0ba108462900c400b825110707200002c0e20503910410b51810036212 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 797724370 1250 797723120 797723197
    0x20d02012a1d120c01120203062110472e020102090316060804080307120c03270c0b130b03090127020906010f0207170a06050c 56
    0x81d00b0140050340026840d80890700d12500541c0c4052000805540c2c018030280c04500f0903041542142080c1001a01c2c440200074130b1207400ca00384110b01142d8208004111460000340410445c0120540788225200b86c241c030311924070b00380c5040c001c14440800c0c3c0c1141c40d40380c1201640140320800b8080106580009001256030f0160081a00c4642c5822071041c0b803500311034000583ea07078011f1040c14204000e0039110041001c075048104015034001c1e80c13465019602c511103595956940d00250f685040348011a00e4861801400c01950360709a801076040003040c01c0b0000003140700d03001d00100c60380b80c84401862a801107500f0458844e14001130310800c0c00d000d047d0380030980c440e6084021a001100d0031603682e915210001b040c04139a00c6910101120f00d1007240301c44400d80c01040c2030f800701410107410071a00c40042d01020340300f8841d84002c1c080c3c400384071103c642800d8119940d241070503410b40e4800e1070031011a04003000d24040b0364550f1400f0171881404040c03600c41c0400c035000f4a02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 797725620 1250 797724370 797724407
    0xc0903070f170c0a080d030c0c0f06090c08030c03160c0b0a0c1a0103080a080a150e01030b07020606220b04050a021e0306010c1407080d020d02012a 65
    0x804501000002001c0300580710b0b494054546415070341c400e9103004440d10120380110700200c01030113118000718103400954900d081c0458070486889084400c59207400001d014201416110010000a60850b030890b90003000c0001001f62551826910380c401d00d85d0206199004000d003404204116100240702d42c0100401029156200081e01640d440b070042c03d00040c0c15180c0ea40d081080b031100b04038240350304c850002c25660450b41c880c020380c414030003260240003501001405d200c4082c0c00c20240d2120074196110026500c0040da08007003001e001c2281d80c0074481000078183e40c400920b0901c50000204200080f00b040100b1916000c1c0d440440c2c010300c1e80390000581591a203002e09801101200c100580d152a00c0c0120500360070161451a00100e0070018013040c0d07030f8804c2288407403540140344000c020040c4180e903071914145910903506400740150f05510140c001c00d00d45401425074000744815444900781074000c90303001d00b80415413181e540c8a5404144074048000c8460b00c00c49 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 797726870 1250 797725620 797725633
    0x20304140f120303090715050301051c02041a0111010b222c0c03070510140d0504240b010c0f030e090c1908040209060907050412030804060605180c0903 67
    0x20042402c2204101c0e040000f5440001804040b543c204520702c01003c040c03014014401001c28000e101c0e11041c8a081c0c4652240740940f000510080108524264010810040341001c0d20b052014132004003009804220000c0c0d466030881c2d8180035003803100c00b0090803114941c071007004100500d426281c200318420759403010000c07030311507100303561019a1502454800d2070000481841ca0150300b0400c40340a900034050812098403110b107070340006903180c104240c80d08032400c041080c50250240d16000c5c541040103220900046990310394041d035900c07808402c628a60000401528041641c0381d00081841110708007103003400909c0c0000902c03904e00300b6452070300c070400a1041c8006030707440340c00358400203952a10b2201e0b80801390380710f420505080c9a6071500d0b4000030b011103401480740303004007244070000300035510a4003110058403014120140880c20b90070000e00d2940116801c64505251510219031890a03482c802c0c150000c1070f601070b10641e66182034003c5074110540c5640c1510482 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 797728120 1250 797726870 797726899
    0x607030f0228140d020705090c090a260a0b01092a171005060d020f07050a0c18091101030b03120a0804050d0507020a150903060e06070305150102030414 67
    0x24000b840c6850014108506000254240428031545080c6081d11079071040c01e01c14200350f0080343c040100c50045524141c1681c40e8840e6410b503201d01d080c1c45a0200c0d04034008520002c1d140701c8100192426071408810404420034140e03100d10100c1c1c041c00c40340f101c2c0e0040100d81026049800ea01407501d00040b00340d80c0301049a1202c00c6400c400b03402240703400c20740740342004042c000c0e942c0c04081d201c05010441e140c900800c8091090305141544940c0005d0011a41680b090440d444550b002c807c840b0881d05a040c0b1415000340d030f006101d40100581040b8050b1240c03400b03525540c0d0b4001d078075450203407600030064004003081c580c941c0d00f601803495107102d483d25002c003405c818041c079190b000241c503040c6442420400c51085030020b10005000000240c0c860740034401c190390400885010b036aa40f0310703068451025a6000070502801c10019203030206020803a10b00500c540d440900c800c1e2500c09480c04c1c000200d503a4503005900510081080083c21003004451800140c00e003c04840340 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 797729370 1250 797728120 797728153
    0x30803040302100506011b0305030c040f08030c210a050306180a0c03140f011511030a09080607080411040c03060e0c09030f030901020a030e040b0d030e1305060607030f02 75
    0x100c0341074015030440e904100c140c9035640549a406082403920b1144800280c41e5003451040c1e4450103400c005000c00000e4050321002b0849000e007101d0b039004030000343e650185955950041003070810a0190a100c1e82802001500d00c000000114901d1030409030b01c0c1c074048415410040940d642301d00c02d5000078403580e00c607a003228040d03002c641d40401c034580301c07060107020fa404203d204040101d8020410000507060303040b260550b040c01c0510100e4401d240c0f804c0b6070b810408441c901c600c0c080010344c0c01c0600d811400c24811511144140c82240e40c3c0d18078140d400440865002d482880400007090f182e1425500880c080d451a0400140310303912015202e00c60a003c546840d4002c100090041031860104030001481c40c0c401c000790b1603c81c5620000391580d4092400906021801501e401c07980e80d90b4100b04404034000d803400b1280c42150900810000e070310b0050b40e000c0c00480c0d280a031401c0d81c1d0b01035244540c60151115280c400745e0395041314013a0001800304118007c1010a80e02d0300d80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 797730620 1250 797729370 797729377
    0xf1006140103091b3f02060703200607091d010308090d06020f0408070506030c090123070c140406030201140f07020603040f1703040f113007082808040308 68
    0x1301c2400310f0346001c500e00d911510f440d8050428004981150500326400171324040900c24241e05075005512890300389800d139080845900c000900c1c502e0904e00240030040041d00e0761040ca140e60b00c40b1300340c590720508000500b40343e86a0040714007902d00103002050010004000d5801d02600c4540202030b43d8403071758126040350700e07100840c1e100080c08212404c0e00f0171010000d04411542e5a245041134825400c071403150241080c1400145180c03014054407242c81c103c0003044801070241c0c3d6400c03919010108600e039006070b40e0b0b6030b04644441709150034a44920401c2c0d03941038440500b881c0300c003280c000040d0450074051841910400200005841d0080514003d0f84509119903200d5840d10741700c1c030f14200317900701042019414010000070401200b00000d40c9500130081c002000c2c211000720340455034403043d1044102e9005a80d0704440241031119800c000c141044c0e07840c42d9200d002950f25025032011400d410014800055444513100c9814041ea030700c84c5c421649002e40d030b42d0f1504440e80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 797731870 1250 797730620 797730629
    0xf19080318030d08010303030905010209060406120522080309210d05090a02010801140a0e090307140a030c1205070c090905060a15181503050f1006140103091b 70
    0x4102103100c14400808055010341e05000302c0240c1030000d41c1c5031004240050520002e0109a00d502c1c1c0a81806020360489014040282580b03a94585828000c1d06644048803c61022403401c80000d4550054a03041d4541e42216962040840000d442700c02e110741001c3c20396043c1d0700414148403104006210b07401581d503d2900c2090b100c102e0200b00c0070484500408544594025007002c0300180c1c0c0c880005810341d0610500c215525000001182054515400c40c5014084410901c00700d52000030240981521408440702d800017203815450712803100110080100d0507003010840000c9220721035003454101440e0050518172180c840f40c590070190391055035203c0c1d0b1195484284132090020b10360008440d01c09202100c0c0c4401100c041085034400c0c0804024802d8031500710351215001a01110a500702c5460300940702d0030500d494500102c020b60540c410000d05030054019400f401013140e11844c0b0f03080d0302481040040d0090941c04a040750b90500400600e1340c034140100d4000080c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 797733120 1250 797731870 797731873
    0x5091c11070806091006050f011b0f0b01080f150414120a2309030d0503070306121103072408060f090a0c1407020a030809040204120b0403021b0f0f1908 67
    0x1c0c18490646030801c2418845e42e41d1650501d4030a1065440d203c81c0b400d03030b0b07840078601130188540031540c000b15040e0000b0002c02c50341c00300061000748080074500c0303410381c1e907001e040e01c0081e4140341e1519903400000620581c40883d440004000c1030101114004050002c01601d240074502905070b08581d0141c0b22010200740313a854059240c1d40e140c20306103c40161984030600c0c1840000c0000c4c0d0f5a07504c640c6881c01c1010000010700d1440c400e80244008040740d00310030248442030710b420f540018290f074001c0e0003441460000200d001c051603144507a10708103d003c101c0c4a14058044840300c0004202a4224069240072030407078030b030030101e107208030180040007a1259100c40300130080300d42203d030705400c0308041c0302130400740c5e46071203844c0d080300d5210102c695101e40780400f2401a01540c0d111200e003a020724400c01c1405046030541e88030341e200c2d50a555601c03002e80890940052070f160f44d182c010405c40300300251800d01900419284034020040480d41c0142d01c0881c0e80030440e9000342d00f45 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 797734370 1250 797733120 797733133
    0x70f0f050615010c0b1801020403030203091002010b090f060409120c1406090709050a09081207020106050604030c060c030e0a080a03020c100e010f0309080d0605011205091c110708 79
    0x14440c00707000c0c1d640c000881d0301420902c4808040003c21140006001410001d60b40c404540c4600f0104d05c0480b142c41c00074025510f942c0d490402948075007220b54071a00450306814021b040030b10601c40c100c0503030402002e100301a2220b0b0b184215111004040a030455a50742c110b502080106020895040c3e95599102400c0c5842c07070006c1141c0204050000360b40d119506100346811f011860f10f094445000001a00b43da6005001d0041c02001501900002c800a02c14950011028441c1e20680741c5400070700c4020b50b184144501441a4400504842c2410702c050100510540d10300c1c40d81c1c3c1c020300d0412500000320000a80c00e480daa404200a58002124441003540510001040c5902103484203c140300d603044c0075100a02c0403d009040085520104444c2c41c044d0b444103c039160420a126100c01e640d040d60801010203010f0b4a011039107100c41196007002c18040c1502c81e482e800050140664069408400101c80c0903190080c00300da0051807511754030400c8401d004210a0005046 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 797735620 1250 797734370 797734373
    0x12070302152e0e070c4407150f021309052205070608040c03050a111302072a23010f17060f0d050d0807020c0321030903070f0f 56
    0x100b00c48070000840d2000c41d003a50410103030a0101c516540003110b403c08030b00140b4a0f2034110f0854401c0144003c140c0c0c5003801c0494000c200900d01d920305841c018080c3c0e2032031405121250f017405a01c1e402483d401c44211a401c1d4070200c1e41041041640480300503041c1039810a01420081c4950031035105150380e4030070000c0b4140c6403403500703140700030324007000c500d58200e40c0300c1a0701c842c4603010f01c0080c4421000804c2c100002142120011a044016a00388040c1c0b458108020718500c001584207852010145401400c244210390202e503001095040d1540c110303280b500d07840c4402998028150103508001010702440d9040598403880c1403042c020720b8952400501241c2c0c001d40d2600400001c560005210b081015005402c1001102c4102a0206480c001002000100750044c070030302912904084e1160840e00c420300410442c1c080e9540b9040d1002496540d0407004212850801001405150141c4110007181c101c4000c0003503138500710445d2200c50341343c02041341c100c8450510951000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 797736870 1250 797735620 797735671
    0x1b01050412030b06040f05060a05300601091512110a0207050a0b0f0a0518120c011707091206020f0304050604060e03072409060c1106010b0a021207030215 68
    0x80507040c0131a03040341000c0c108090000c420306035009950040000280342d510060292007642d0440203500031949840b1800c1ca008026000f4001d00341003503441c12808243c0541c0200300707040c180d91100b0f0091068240d40300c02222408062002c41e61616540c0c14002030005e503000040c8460002a00100105880c04062010f04c542ca035016103d0301d0800c0c414804e4130100c0400311807141d481d91802c40d4440260308141d02003207401b0440369900c1600404a03019a8801150030402980e0036200e4030306444e4000c030b510005100440711800004c1040f41c041c040e5240c0e141e0b140c03204e5400b501f001810071444030680001d03944151400d0322554010800c0004005890081109030b00c0f902c805103080000c1680e440c20300319604034102000384480541c01003087d545a010b06002504030500b40300811065030040c1c0f44900d40000e056283c01a0f50002c5080b00b010300c2181d4102505900130200014000201d0000790401c01088046004044a011804010158a83c0512183d9041a010340c0c0814040e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 797738120 1250 797736870 797736881
    0x14010e061005030a0209070e09151807020d030908040506040e0105130605061204030c050706080601110a020306040206030421032309150c040b0412060b090c0a051b0105041203 77
    0x1c0c42581189005119a03200803c06440c0c0700d07419541c2c00c4954580c0701080d14401104000d00781c000b05003404001241400500156582c0820745001075000d100c90441a5841d10494103400540e0116103411074a901c00e501c080b400d6030003922442c5c24a0749070300009000c1da025900122a82c20010014001482d0015241c00c1104111104010241c605004103000c0c0c000c1f00c1c5250f0704264001c2c000740c10305008182da0302c003180c1e0141c1550300b155201d400c05850b40c0401d4070a030380000e0740b10400d90020b4400142051846400400804d40c0756200d03420006c09902c020300441d81c1070308014480711600d400940c01156020740c1e13100411100d802018058400360540d008400b490940801c0c03140c440d0010031980241c1c000c1c1c490007803c0c0c3e901c609a8500510032507000d29041c003000180014541d6442c00180c0b445da2050741c080c00340c071000b0010400c0024081d10310809030340341080380989107030158004144403528108011100800c2000082c00c4541c01c90341a103510f042c5d000020043d5a052003071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 797739370 1250 797738120 797738131
    0x170c0606030703030f0e0a0b070b160c0b0a090204021b01050f1312030e011e2007050d0f12141b040b0a0c020d061104030b0105010203310314010e06 65
    0x201030062644c0c8004107844041103048060180d424982a2261201d61a020140180d0440140d03116002d181500e4042001c884140e00b42c41d4603460142e441348900e201d82100c42d040151a40e840c0c4030910004000c03c50f04800702d0f0b116a0070005005541075070002e5603079a061290001070300d031519040040d59980d00408455000c1201c01c50f8400140490500c02c000311524600002e60315076500c240c038018003003400301c40307100a141c1d8100c091a52140e0481c44240e403c0c0c6a040091214804202401e4003425200810f030381c10442090058a104050300140a401450445244280304003030008480302080c007081c00044407410044041c00c140f21880c240c4001e00c0003d440e0034507190601c06140a0248a0001c20001e0541c005c00d40d41e9000180e0050b5030449800c0010420880740300315198417900c003c0740c035559030000015240d070011042e10b030996625941c0301010b0080502e100c0c03850b1054038000c004001020b0010000c50503880c000440c442c21040001100c03445c0140080c5800783c010034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 797740620 1250 797739370 797739373
    0xc0e04050607080c19020a060e010204061e09182a02010b0a2d0b0f03071b0209040807020d060905010f0e010b0a090e0712060b18062b170c060603 64
    0x14010009984c004032849495507040c04c4c0c001c204c1c40c04c0200c2c145000c480c0080c0c950350800051748029041035000b042207526584494003540101e01c1104407000da10950000440c03900d40041040403048040d010320117006903000102e40f80342c3e1400241c1d801c00c24440c00845e000800d4031108803034091082c07401e0503030b0480702c68240d035146c03000084501c03543c0310740c940c51840046502d10380c040c0c4003110000034101e0800d40540717420b5000124001500101c0d800000510b22400302c4824081e0001c1344090640c0203170075504141d0300c0d9190a4015405014100d0700119a441e0003804601d42d84200848513110b407001003022100306000c4415110f00315024006c603494021b901c0440e64a140d141000c4031107200c00441c200e080805a00e0428030260700c01c0d014500e07024031070002c000d259402914042011222101c3d1080b02c040d05a9130303100d0446689401c040681d10381201a40d15100e8666620040010481c01864135607a07120700d02c003e8095829110f002080000811400b170041135800b1109a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 797741870 1250 797740620 797740637
    0x27060408250c120201081e06120a080409150e040b060105160515060f04270c03021203030a050a0204060503070e03010b030a060504061103190209010c0b04030804050d031e0e07030c0e04050607 84
    0x80078199200c0038200da441104003221520000d0000d1100100b100e4104021074cc9907940d03040080041c048511321040441c0e060200454543e03d2010124040c5802c401c03984010758590005451a500500e1544551014845d94a000450802107414000d1038038942c4100c07414001e0a21590404403007505100d6410100d18a89900e07054201c2d9001524403114105250350320b00f04140f044103503802c042c4d0041c6d03101381403a24407400000218021810403504011176501e200440080340501c0c0103000c0050020008100c03001d1061f408950750701d6008000041e01a50740b00043c0c0751501500c0100c13a03c540392070400c414071032a803280c0c4100c502c00310380040c60340c900781c4206840110181648211240e001c1901c000c00c0e4880c0c030444040d603034800c9800c05a407c19040c089c0420b00122000c0b0f03541d21405007101d54a901ca030040396143d4100c500d00b40e0312500e041050401402400c0a803081520035001d001000c00c000108441c010190222010460b0405007041801c04500034240420712a582 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 797743120 1250 797741870 797741911
    0x909010c02062802090f030105041a240f040f0f06030606080a03080c030c09040507052203080d0e01020f0a05040509010b0304170c0307050627060408250c12020108 72
    0x702e58428021803140c0c01071745c1c1d00c00703c80002c800d002c006042c0d5402d5860b00c3c0803c000c0000069148024080c0f07c4200d424a40d1441a11840c01c168400900d600310f403003010481e80c0741802014031441c0c1000501c0400c0220b2410314003001c68401c0b90a5030005a1580010001e010305c5205003006405024040c110b80e044545000d0400d010250409040c1000000000c0d40c0a2401c0d0030380f40300440c018424412405c00002c002d01c0764000c030000940c2107041610442c1019a000c42400c11207a01c84e04203800c00c2000d03100500148804810059555000c000d0041a00303000d0009044581003901c400b83c40e0b901340070500926007016040309448940400034040401c115100307103402c609245100341c0da50070742c80c050582140602072008043d807044005100e2403c220b442c0780a03c4040014000461844252200341c2d2440f0544024003100420406040c18510304800d904a1401d440d07441a0b0b140025a1200103d018650080001da85003120100c115a44a01c1c03083e040041e501031014000c911 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 797744370 1250 797743120 797743171
    0x190f0807150c03110f070306050c07030e01030b1801080a03031b0206010909110301150812090d02091302030d08160504260c041a15030f01120c050909010c0206 70
    0x1114200340285030b602e00003090f104ea14064402c500080680d1144034828080c503a8444e170500084960a0820001981c2d914804054840d020f0701a030700c2c45030550342d500c0150002c10000c2c0005030840b0000b4080002886000d041c180203000c0c0900a006102c40390a009044030504141522040d00c081b0340c0c0000342d50b00244441c19656140b200042807491494120241c401c1038401e42e4065080c030034030400034980103519100300c0790f280c3e00f0360b4100c4070320703240400301d900c82c1c0c400103a8085410300880001d810280301c1300c0da200010452043c8018003039000a80f8003440803035082e00084040080000c1d14110340050480c441b0749040042c00c0c14204840c03440d071514001c60b4400184c008051700b480441c001c000b58014000d0150003001414032111200884d40c508610321401903880389100038180940350201c07032184000d41054005d40e401c0004075186590247c206580040000e0300c0131469a50b51101d20307028481103000001c40380c01030079010f800c0078402002e1a5020b169060045500c804 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 797745620 1250 797744370 797744399
    0x10b0904080c03190806040e0106060f030b04111b19080301050d0c0b0d060e0c1614010915060602010c090501050f0c0f07060c05120301030f0b070e190f0807 69
    0x144114007a440d4100c03511120b00e140144240703419070655528075040d82c1600002c6082c0104000e54040c8080500341741134a00baa1000e10401001505900c5c1448403203209500c4900d031400010004121802c0d540c0303004c10b8507001800803140d14045005120000c21082080450700307505980c84800c41d05e0f40b502c1d005e038540414410280640c150078070080c100240e01c0c2198010b004d070f10314820784800441c0490790042956000d180d202d11f1000012410a0700003e041c0d80c50b5484001012402b544140d0701d02c00c190401e00f00701e88a40d1741754181d0000180c205030501001513050380740081c216191841c02400c1d0340c15081050203003c41140c05100c2d0b640c1c468210b030139080513001544ea03103008211040745000c055010000c90f03405164400314013a60710031460800c0d41c0c0183c08a81c2109201d000c050624442840300809006c10380030242c000601c0307039412a42c060554203080400c41000004666610001040468040300c03800c800c1c0505080700c80380c28050001c01d8001c200361414402c00d0b102654 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 797746870 1250 797745620 797745623
    0x120b0d060504052406010f021219050d1109040c0519030b1c0b07180f030b0c071e06051302091b0f07051b011706100e030706051902010b0904 62
    0x16280c10020b010f0000403c5101692801030724000150b07a010100c900301400b050702c3c203600107440188882040c5100103101c942d0030b21883c5440349040c01c1c070000308410b50448440d40051160a100d807120b84c014512589040310070001d01c040e9655000401c000485021007400f0052040521074903048502060411040d001d05050002c0c104107480000741d4511015082000c000aa0100071800c00c091110414082c1009403500a0312040d40e071281405046540200d480310105c0300300410220740049c0000b90400c1310f000300545012625242c0d03500001100b40032261104008210001304080b0703201d815400f1040c000e00b0b0345080440d43c00248504400b81009140840c00c43e108021034151a040303405619507410095604d600c1c0f460600e48850300c40240c1840d02d0480c0c007083d05254060001c81085003040780300c61840b941e60608006c0d103803c041407c0f104200c0340441205544d101000301201610310354030380c41c0d1640c81000100801035142c3d00100b0459040062510407616044000364005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 797748120 1250 797746870 797746883
    0x2010b090411091902220501020c09161b14101e0f0f090f03110307020a03140f0f160906030245090d0309080f090f090103060606120b0d 60
    0xd44421480e0f40c0d1229080004010045c030015205039202d45909a07080c1151171840b150b000c0c15038800059031525120745050760003050100011b13003100c42031070076124402c0d131a051102414208281d148408049040201d403104241083c08a000d4070400220801d01e02c140f101f030001202d49a02c91202020b58006459400c1e00c1d041c0880380c800c415000360703100c0714001104210082c40c0c1d04092903d08921802580402c114860348904c045021040705c82054015058003041851550342079141c42c410092000d260148210103090b5240500c84411603911001c002e01e1614648a40340815101962141c064549800806c0005071185080f0106140c000b0403a84120520007245a62020700605107294001d2083c12246030303e015549060f000d400c10328120b610f00398078a2811b400b00e4036002d81c0502690000d100100d441406500100f600150152583c11401c1002e404103810510a0b0000c0b41c1142c2c0300d00040c40750b16400160130680001d81d1300d050004c01d90f0318010a41c003203461007025001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 797749370 1250 797748120 797748139
    0x60305070e2a0f0a020705090f0619030515092508121305010e0a1707262d010e07240512060604180e0d030c080c0d27020102010b090411 60
    0x1021700a1207160024a805082031003185081c01c50030410910859229201d40215070760a10307a060b82400c4401035035403180c028038034002d129600d215110402003a4007285c1c41103c85600040d0034041812039a0f039904641d1400d0b080c1044d441c5800c1c18100070050220600c14082c4440420120b41d49508030749003800c0c45c06103c903046000c10121502c4e074121210b11400204608041e9000061078003c80310300084054a1403000b29030f40f0b4101680d140b5020303e40d03100640d2060b0b18200b040004514000e60908030103406111b000b190309550003618655165003212208200e050700f0003040b003100b01c026882d1402140020384015010303029840c091034803040c6060000350540c60b2002110040c050a5680403054503241104001030141ca40d15510680507042000c0201c80c040d0064010014032911f5a020380d03541c0b440e81030b5181d00846150f5030b00f203884007074032880321070389011605c954822003d8164600b580c500001e4255903900078518026400c100402012503d04100300f4501c480c101c0c1c40f082d6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 797750620 1250 797749370 797749387
    0x30609180a030203070c141807110a0b010312110318030106050418060b060408030a0309060b06070b070e090f07030906090b010f030318050607020607030201060305070e2a0f 76
    0x2824030915003046144584240c08003407580010107420a180b00d1050f0b2201151a84942e48211500c0d05010350014a9108001040400142c00075030203495440c10100400d180484145010003007101a6940c0310081b0040c07050110350388080100c90400d04186541c484101c10542e47e034841c03036211684100440074548607c0d6401c2d040b502c02040014020b111040c8081c0d2a09200f0309072180031600940b500700d04021504140050358201c2c0d00850107141002c0340008150041c0c100910101d8400c0d6840507480c1150f03135030070003074140716001e01e040e0340c0036261851b4082c1550090404503803003024000c0c05c0001080070014a6035020480d03150108030385030103244c4140688441c2c500104070015100000c540d900d4103140328801c681c0280e80d1500858000c01c6220400314160195582050007048400050b043c200d000304007951182c40001615079036034a585040460b42d80164060084a0081c042410154828491700e004244400302958000c064070880a200d880300c090300b80c3c440030404c0c03070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 797751870 1250 797750620 797750641
    0x3180b1f090e122d0c0f0f1b0a03060906021306050310060f0c02030105190f020408030304030e150f1b010b030606011b05010608060702010615050d18020d2411030609 73
    0x5800130844080e002c0b9202d40000328100c280c220f114890114450104910741154002500009980d0044080c0840903034036281c0039000300c3c050b4099a00b2400c2d101b80040001d1842c8586036a01c1d005501c01603e80040c540d40d4044680c16500004c100407062050008003407850030510b003121740c2410f16031107030503498000340d8401c0c10302500a50326528000c20030203106040003408130203c40d40c40f0b0401209981e65030150890142c0c2c041c030207044d4018800140040c0c0100b5410501c0300b0020014001054408041d0341d503a8010300380d80c0d0544401290410130078000b1150003c404090340000d011303200c004000300f03540325030042c00c0c0d50410042c4003c038940e02c42e03100e001d00c0b0000e81002c0280400742d219804c1d00c0d503510040c0c0780c5100540c43c1c00e0002902c2060b40c100145000050303540d040c0380603480c5103443c2c09000310100240000c500c100703404005950303e016818005100d6404503202c0e45006062801c4001ca04260110b4141230044282d00390742413000f1250702075400c4400c484c2545034210201d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 797753120 1250 797751870 797751907
    0x402010e04020703090305010c0203160803060a180b18090307061e090f1101090f14032a010905121005040c05090f10060306050604030303180b1f090e12 67
    0xc80d0803500c001000e0b0185507100b0910016640524000e1005122850049950f40301e1170203000b41302c88044200d080055080002142c002c03000030044070740d083c3c40b103030005008628080c0140c0c07110741c0d0700e10525613400c0c408010003520300054403d0405241c030100703054480c40344079001000f0580e2040041c0e1a00c503507000c0e030341811341081c3c01003108c03000c0391500840c0d603120703020103079640321581614425540c403c032007881c25182220480300b40d4600e000342c9054105298814194503004801e41450004002002c0000b042030318040000854000000504034003034a4100324069014005076502565002403201018103194000041503610303400c0040340102a600025030011850042c0f1000145803001320b8003440740c1614402034550b550100b0707422a0b81a1007034541000c8280810400b080c001c2c0d0052500c004180b0340c01b8400301c40c81c0d80356607000a04450300740a0b000d541601c0d01e00204511030b061f028007445c0000700190301001c00c841d070341e403008851005c0038580c1c0001d1458a070f21804928 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 797754370 1250 797753120 797753147
    0x90902010c20031203041a041e06060501030b040b03071505070206120f09010207020d081b0729040b04141201020c06222102011401090f0513030e09040201 68
    0xb0594480100242d541e008402045524803a00c03600c081031040c1c0200808803406503911100c1202d1620f2050801c07411315200a100f600d0f10700c0a40040b0380101000b110420107140300b0f1800180320740c2820b00140403100c541c48030074061494004070808a45002803c075007a98401c004003884510070f0700c0112414490244000e4019501080b110b030f13000c3e10344454900a80c0d40100c0f00800ea0f94040c1c0301c0d800c07400745a07400f96000d1402030000c00030600c40c0300204180a803c0209441160580c04031900e0602039501005200440425904044440425400e9284171442045140a1900184594501883c002e00044e00180402c0b090b550b550f404014011850380c2c0025903c40800280d410341320342c000c07250410b851400e4a02c00e6094201d400540c003105a104118044400c0c0b500d0000100d9103182c04460203642d80c5450035075913508128130081c024a4104804a03110011444040c143e5402a00305e44501800c0c220a50002c0e422101014014100740ca403030b0ba29580c2c9000403140310650340003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 797755620 1250 797754370 797754383
    0xb0406080703060203011a120c1c0c08040201020c0406030804050f061b0102180d0302031204060b030a0804080106090509100207030306030f081e0f0f1315171b04090902010c 76
    0x1c0001007080907005103040b0340035040c1800c0e0001c3c4000900c00716110307913503500c40e11100e070200107040c5200031405049001c80001c0d103400e03000345000000d421100d18000c180701040d022001c1204542c3d040006440d6010300b0703a010302c10a807440e40c8801d004d00450203940d00c10f0b030f01e13044101000d481b00b40a43c2e0000305502954014500040001070007503200c51110801d8225105012585007812455010a603030305074021840c100e5102d110314240b50001d0000c4a0190f19203002041d04e980c10041c44145a0113243c201c0e036510300c0c207100c2c2c0d4211551a407004005ca8142010004425804161552841c2105401503582d0a0a1600318020036064000900b000c54091492040c00300d201d006e41090002d0100ca2141d40791101036184d07050141c6c40c0b0701c1c0b60805040040005401400020380341c10380c005503854011540b15039031014102d000015260000d11120410664900400541908207082d0100c40711042080c1200c480f60b0312940c050b0403d0a84c65264031811640b190440c045819017050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 797756870 1250 797755620 797755633
    0x15070203060f09241f031202030c1c27080601090905012009010507050114160909090c05060333030c0906090112020a0b280c05060a0b040608 62
    0x282c0358100900954880860f44600c91880c3d0442200c10b42d5070101e80000c13020f801d5550f80c0e050126100c20500c00d458002c80c280d052000000550b6100001954804c0b60055030300d41c14107490b06480c1010103520202da007601401f0301241c03030390072201017070f0b880744c075000001210000c00e910342808070215480010f41d40b29840000610300040e5002058582c4602c0c0240a07540701149652640d50803400c2105001c0810000c0704074a601503001044080d01c10300c00840c070b0f41004d00e51a40d25802c203c030091071f030b01a021850360039664054604e40c0500080201006148541d44602c2c821112a026050003110000042110306001811039140303100b201401400e8031000d502c4d0075500d2071058130f116000340306e18100049640340007282c46126180207014522141e00c0d08004034501d01c00c0740400d0343c00002086012404480140051000000440c07105402402210003d401007100915203006c1040d03802080d0000390002c503c2c1508600119400306450510200142c000c1030158000c003040d12420307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 797758120 1250 797756870 797756881
    0x11061b060112032d1d0415050405060d0f061d1e010606170a02090411181809031204050118060501090f111e090402030a0e0d0e01020c1507020306 64
    0x7030b020944950302ca0743d94510a6a407010140f0001552580a8141081402c40c41e02185200d40c035485070b2103580e5480d0203000750084010601b00c0314446c2c110040c0d2452180148682d0030140503c90b000001502d0f004504025074581c840d991404482c01070640c2d440d4144200110020b91010381601450001e4500c00e03507581c1079000c4417040c94200c3d580d481d4203040001504500030060350201c00000404c0d0303403a170750396000d610009510009801d648240d4445841d0480c0c800800940300392a246080743c00740d030320707a941040400c0b41030000800400c2d00810070003645e07800100c1914403c001c0c0b441301d070704151242c0ca002400342598004001c03e080350780000c041131200c20380000781241c81480b0200090510741580c01d090b0b40081e155255142000c2145c070140c040300712200046510004000760038401c3c0500040c080c4d91041c0d42501002d510398011444105041c041591148080d0401005603100d500001c3d40710081c42c40c2807840382507003aa001351000c03011812a10f2595008007a46d1180c90036 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 797759370 1250 797758120 797758139
    0x50f04060201020c150105010e150408010203010e1b03040c0e041703070e041b08060d0804090f0b010e010f090909110d0305190804080d0e1e0303011503060311061b0601 74
    0xa041304110502c04d40f95001040c103410408181030792410313500c0003941030642d0148459482c842510019034041040001491082880036501030310029110085a0500101582c8405410115071712510700c208184400074104c4080041114070003d02c00031142e82d0b606144007072040a00c58540e41450000030000c41943c00301031000d184404550070090b4041206804500a5502130442d010500c1c080c0450340078901049103482a6204605842c6056140c074908000c0da1180050705120940300e40c0040c0b420741e040307291031045642c2882c102d5480303940750000a002c070919100d40358100743d481d11010180164440000131001016010320320400c0d6900d0014859841080d0044007500500c103980c00452059a0481c05540c0001c0f4003410b0010200540000b04841642c140b0684509500310840b500012160060340c0040f1010756100d41c075151018070440c40e160354040030140b60030400c1c0000f50144c001003032014401c0e01d125489080300201c3c850246541240c9400c81d1040b003000082543c0c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 797760620 1250 797759370 797759377
    0x3020c060c0a09080714150c0a0f020a080105070c1b080a0b0402031204030305030c160f030c12090f12050c0a0305010510061110054201020d050403060203040201050f0406020102 78
    0xc2ca9694005425510b503185502c1e044107025100e00d180700710024103000e18226a16100a00440750020720b098004040c6915155103003204a501c41c155142c46015440c102c46507000411700d080081c011498071040082081d078455000800c1e101305006050602190b0b4003024010346409400c440072800c450500d45095017040301d0483c0b00c1d100344031512120756003403010799040702d1781a140c650031340d02c42d9201c2c1c1c0310640000645c2e240544000740242c003c203001900030b40d0130900130b031500c48014006041600868122180500c240000c8110400c030a22641e404002101c1c000084c0b20220050351401504000a044000c0d52007803501c81702205209040d03106500404005a0407424180c0c3c40c081074078001c4070084681115000100300c201c080e091500a00d81c0083e0b0150f5000b4101c5071403220344044240070354080034008075280103030a5002802d208001c1c2c00000d0004100a00c494034000701140318600004000c6134010010038210790254081d111203221f20101e254607640c036200000d00030f40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 797761870 1250 797760620 797760637
    0x12040902030109060510020a1412040e04060606030501080d030f0f020c070e0901110304080703031b020703113f07030b240f01140f1206280909020103020c060c 70
    0x14908440040e05d8a03010090141c1080d4640140c0000807080e00d6107244480300303030300415080c010007650581021209000f000034003042140011241010300b0201d0864029400c0714092520304801441403180c00502c01c40480b1032807030041744600c00e42000b00041d0681c0d154042070240045545c45020f4000304500d800e54904050782d940c0341d591048001d003030f0f070031a51304600d00d0710080020a020500e01f030002d0043d01d0003400d02003018103010340a01040403e1940b1000107030030485042c0100440761036a02500740088804044c40d10002e03901080000e4450100080c540704007001d0b28600071108418500d86d0342010603039440a641c0d08107044009821074400e8036006002440111403841000c07008040c01c005008425520f00e48001540c01c600c5c22400d07500c400c8428807417000c041c24408018110490000100300e024100b680074060a0100070203480b003210222805250380c8541c800c0103c0c11226840310115a803490341c0016802031140c048400300c18042c400802180c2c81d9540c1c01402c115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 797763120 1250 797761870 797761889
    0xf0504030c0b091f180203070f09180203030d090f08070515010803190806041d0c030f12030a091e03030b030d09030b0f04080405060408101401080a0b09120409020301 73
    0x5540b02c2031140c1d194022004505200e4013940d80008413180d050388008035042c034030680a14680d07016000286400301c250301404040544240a000c41780c0035004121810702a068040c507040361030f900290b103900908510102d00c682c0e0740d1003a020322103210980810940c004221580c0e0303805a041180d101c0d100240c2c0710107015140c0c0300018914034008212103803d92035207194069400c4640c002c6680c01c00251040754415101e400d25409807200031011500c05881c840201031482804003854148000800441032542000c9440c10780c0718801c4085940c0131002c207500141420751032402d402002144c50f0400d000e95074055562041542640c800c440b240400c800b143c000701b100c024101c58070303406404010725661490300400c04d000340103018650414802c1143c54140740e1685e01203413140d000750340940c0749079000c0d18200074600305030700c600d20b005200c0f20140001c41d81040c041980d01d1210f0351005104ad02d087c000281a2003091201c1c4040321038501c60070395140d80e60400b20020790028040e9032182c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 797764370 1250 797763120 797763143
    0x4050a090c030617150a061715011418090109061a04242102060f040603060f1401050307111e060604050403080c0f04031a15040c02060c090102010f0504030c 69
    0x8410744090400700c00d01100000c1480f009075420044240303501034110341846e0b403117040c0821221180e1a071040050f03400c00060803c1d05000407021103000c1d06a0280004444c8200e41413155290350300e00b07641c5a9100e183c40c032010780b0744002c207500410140300e000e00a28605452820000742c8100d0a941421048405004a01e410004503820b00c008074801c0c0c0f81100c1502007004400c0350009944504130907150401c03a0311444c0c3c1c010607140d50010100b60b000c8080003e081c03102d950144520809403101c4000c005c1c4042c00c01402e4200700d03081d0b03070540381404004800070759100d2040c40f0f403074040b00d165802d0b1689400342854505a04000200707004860181e04000303000d0741000d1240900c95505580c511700c282d124003440d5005944122200c16000e18200008404141081c1007000d200c0348a00d034034070031441e00603400400003001441d218405d07424021400601e6900103509500900282e804e581e5030b40021006170f005000400c50014117a040074204414540c10000c2c512140380510a0100d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 797765620 1250 797764370 797764379
    0x30403170705061b030a0c031e02040e010905070210021813020a0207050301090b040f050f010c180602010b0a060e01051b0a030201050c04080d081b0d05010303110c0901030f050304050a090c0306 85
    0x10010310f00c2c0055044c2003040c000250302e1200f94110014910b46d6040000c1d5214189510303082000e0a182c0b070f070300056000a02009881c000080140c01040301e02e1081042d0309010300000e403108075003001131078510b4001c21813810301e040d055202d4030700703110082c1614000c0381c00341071542c0690004040400175019040001485040601500d980954040501d8034183e0341d540d0b90051100311401d0039a4140700c0d04000b8001414244192644804103071218040800070130030315002442ea5402100869051a01186554540c00403000980741c0c5800d00d181d6032141100101c440d401038000d03407500d40c0a10528040f0389440825807059590080c0e000b4025981c502000c6c100311b10076482290b40582c408182a03001a01c5503003400d03005520151400310342d41c4020b090302c1a5800071410346151039510001002015009100314000c04850310140030f505c1e0300c200000d040d0030383c140700c003801320303941c090202c0c1c1000014002c5502401d0300412024000b902c0d003101ca0010f01c4e2810380c890100340f4044006c0b0303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 797766870 1250 797765620 797765641
    0x9010906060903060f020c0a1109011401120b0f100815090103120c020d020402031e0a0606020d230a0203180406030b06040c110f1015050108130503040317070506 71
    0x605440303960b1030703202001c0d10310307540c4c0001001024040018994240181d5078030030000e01203000440d01032420404a80d0701310007048035602c0180d01000d021032540c4400302050742c01001d0360b0916640300000241005622020506640842c10a1a4400701401611b010507402250850080104910b040d80a61007a81408040c00081c00090078600941000c1c131905403240402c0c031f04481c030280440031817a466034046001d0707030400c3e02c032201c034001e0300801d55040b84c415250069000c5103070301e03003030000340d2034210007a44600c1864145001c02c16880c0511142c409103c81101c442501020001ea0b2002154402501d0b030f0010340740b0351400082c841e5010011300d0503028940c2507a4004012243d551074140400000703208000c0038600b03015034060300e07400340f0358280b00348035104d1405005043c0308010000e02d18115600414041c03180c0c0b105a00500c100e9a00071000780d0301101c040c485241070030090a200d40740d4001e540c001040d5081e0b075120254140702c0407020342101c912420403600300351281140302 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 797768120 1250 797766870 797766881
    0x3060512160e0c0909220f0501051f052803050105010e01082b1101050f0604240e06061905090f09240616050c01020c100e0409062405090109 62
    0xc0030984060103004c91524081c21590340000e5002800581000c8600c0c5906140555020a031440207010001600f481800e000784c07a80000a803003118240501503a420880c01007038051603014905036000f4225000f0340c1800d00780c601c02c0584900c8100c0d036032071410358042c0009001d10569180c03080d00001d0070507030010380c41c420552444801c55070964400e07940140343d0142d02e6030108001d03110820154240c42885624000c400850440101b841d0007800e00095034280400700985442030845090100d0742c100c0e8280075a940700c4501e81e003613200c00d0000780282c000c0b080048450058100c05c1c180070b54001d00242843c41c400d69070001080303100c40402c440014111048440302118484c1b0400c05640703840000d01d2140c1c000c0110b07003000003d0360002807807640e05400b00c410b5403054003c00348640c1c04126083c91100c04a517607081c0340604d480d0040c265403400301a40e0240b5125542c03a01080a260045225030540c0e0400c4d04004180416554426a0038030038a40520004000031a40a0440c001d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 797769370 1250 797768120 797768131
    0x60c0d11120a03020a05160b060f15030402090604141e060603010303120f1d060f0606030402062b05040822080c060903010e071206060605090d080a03060512160e 71
    0x41802c000c9090b506078007a51054144c64200b02041110100d902c0e00d00c51300760704660003103280c002a8980300c005d100f45c4402114101344110b81d50310021503803003a40c80c1165482035055542801d1a103948010070b014020344a0301ea404c5174010810806a4800360818480100815142020544a000a100151000b07002c003070002040510081194159a00941308142249400141180300c2d04502d640c2c0503840d40301d817007068002c0f1091010012103030340d055405c44403c56402d03180d4209680020b503039204402c504101085000f180607582c04810760440f20341070010f030041c4411300c1c0070700c1c140d0310036800042500c1c3e4070550341c504108a01400c150304804d440954006048080040701000708903008082c07003583c50740d210f0001c5400c810003441804011f000d14004006000b8075880e100e002d8602641102c000c01c00203020b00c504542d5048144440c2d642c210021a6483c4452401103000c0e0140c0d42080760010303201301444c20307c520009030441c3d9110709c0f50080310000da10788603840085a4140c45 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 797770620 1250 797769370 797769403
    0xa0906180c0e102607020c09060f010c031b0c03061b030501060801171c0309020a090c050702011d0a0803091905032512050309010801091808030c0405060c0d11 70
    0x14503d1540c0603210f144000e5000c2c0e580b0640c0c02036071482c44031070700904840c9000141c000f00d480b48164180300c042c4981005085441040e28021b1900081c0b48044c011009002c2061032a04050b03110314044001c0c4000740c100a15140d016100e060200c00362003a03041d01c40c6010107490034007094070f1080c49500d05032800713a660140740ba4030f40754064040028865200c0d240f40204804084400c41e03030708104440c0c94047d100895501014010801c42c140d96511603031616003481e601441c0346a11508a5038410f80c2400c091a5480100200c1181441c404205542040a21501096041000029112201d000c0b9594242c00f0354510011002816910540790180d20031548403c480c48010b200070002c248001d0304800c000e03503400381201018103800058840750400181c0824650380310107000d01400742c41c5801e00c428032901d9018808010072480140842e0b0010020510070b107081c000311801031400502c01d9403202d4130001c15039146e90360b00000f2000b040f8480f150308203c031004150031502d04013145 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 797771870 1250 797770620 797770639
    0x80403051b040e0709020f0c0f1c0203120f0a0219080402040e030406090e0618010e04050111120402040902120709021201051503041b170102071703010f03020105090a0906180c0e 78
    0x2600300d17000c0c0d0040c050100c14140c00b130007244588142003144000303060304c69004000101c0001c10441205200c00c4031070045420420401000c1d8642d1040d40750030074040d0b02c00c0a043e0740c461000304001d001d180a80500d80514611080507164800b01c030a001d1402224100900c00e91000c6030340c1e0741d100f148a8500440c08a001c1003004000b148ca4003070f48040003500f81c0d021400250088280e5100903041000c656101d20244024400244104400100712241c454500145d02e0803031204080c0080c0300074481d0f07840d200d10b40110340712118400034082204040740d203e035803509000d1000e0340041e01c1c9e0304100c139810800082c0b5443d007150514140000001424030f951501d465500824481d902d42c4c40450155000011300c603400d4003003160000a02c00d00058680215180503030741c4501c0a02c900101c1c00c01440140f00c03504e005080c00080b43c0d4242800e5075114004c0e00840c3c00c0f4101944110100c5282c50310019907100302c1c0c0764441d10342e03044e504d040042d208110303810f80c0c50084081c091900712940702d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 797773120 1250 797771870 797771879
    0x602031e09040603020919110310172b110a0206160f02130203160206010b09060c07080f160602011109270a02091801080307060216080403051b040e07 66
    0x10030040820440280c00843da01d516500840e00b000380c140c03a4800c80c54a01501041055074602c5880c4420341220603441c51414500441507500e541800b0707800e0b615a600710440c07042841084032042c08d08850300900390403514072665081821240c4100f401140b031100380b0401c410b00129107540e09503070041c9043d040c40008064240c140402220841d00040b208035490056903910841d107040d0f1000c0c03200513a60b0b113002010f010301204d101e0240020f640c00140103224150409003031310000c20041e984591200031202e00f0a00e0300b14143c2c094960382c041d4502e030346c000b0000416503c040c0002800c02000c103e42e81c0c84c00f28201c40800d0032001045000340b150011034503010f10020661311440120902d4000024524882100261082680d507640025070200505240603035943c001c60a221646196160204c07231764503445281c10042c041c80c0d000407580d0354100020828400c81341c229000355201c94276494134669031022160340c0c00304200c02181c0c0d01460b2400b40100b0400c0c400c04c90250411030301c1d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 797774370 1250 797773120 797773177
    0x20604172203120e03010e1e07030f0507090501170a120c05031812010c0c020d0303061a03041506050d020103090302100f06090e061311030a06050a0209040501060203 73
    0x20095401d0301a0514101800c880c0240711200003840c018a86440701244050300a400000d0340320300a4040e0741461800040943c02099100300300000d0400c0d0042c0102d241402420550341b90030013041200303540524014045c2c00030f19041520380810040060341d03282c1005080b0075940c0468040c2607440f9518600000b600d28a03180041c444a061800c10910300341e851609540080c00303020b81c148584250708226162840800307068940d0710000f0802d8901554006081d050381207030207405a102480c1950805220303601c91001003482c5a504c1e402d6002072880c103e016482030f0303015074045120041405030707200103104120440e0b00082c03114010f9811136005402034a02c510090b0154001d070f07441100c40c010240074a4103104003001300095003070301702003a038000c41d0b0000207500c03d980d0083d010001070002c1c2507102c10301184c00c90005520741003003000003480d007510000c1c000d148038102001d0000d01801a0090300110100b00c4090001380e0701e031b22003240e0324004d142140c60101074641c0d0b054251011f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 797775620 1250 797774370 797774377
    0x30f03090b03160f1b03050927090705100c0219050402030a060303080f070516080903010c05030103050d0e011d01030b1507031209020603160516140d02060417 70
    0x42030030300c1082150380310018080c540080b500140c0f8540039000c44040c042c1e021800e2090001c6500340081800b040c1c0c94a048034a07031200b002002d110000840824a47d50b40e05034070310b4400d80050000820030300c6000b032000b0301020f440401291190110214051a2001700d01f0303a410b0b0141e941c0c407484140c0d9000c1003c80d480710700d40c010744204140c03000b1600303843e2030000351b102d038844000100e03580d407652800a24070b98004084a010851200a2210b50b560220444441100c00700340380803e42818100340c0e20a2080b420042d2b81903203000c4083c0325040d0007401440c122030040e8203991b0344039424841a00c540b01c40c180881c3c0050004900c101c00203810b1902d1001c0a0818500018501c4443e030110302302c640d28200140900101260b034400301a030007005204d00c08540c50092004107125400726003d40400f41080c010000b00d008507500b003034450300030380d40195182024001c01640341e0500c1510703004200d4904405024070081031041038000070b05075004071303032000c50880f888868805440c510340 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 797776870 1250 797775620 797775623
    0x7180219081e090f1524011103070c240e04051003080f0325051c092a06031401050d0f050f100510050d0b15060c0c1309050601030f 58
    0x1e5101072804006450340720914810103c10005145440500441504c0c10040b1a44400311a4041c01040710301c40030140750001c4c070b601000c040c00c01140080016900980d4245c2d12020a10000c5542801c0c404261810340484080c09a040c04442ca500c805140610102020801061a00070000c0c1d8508255004507480b8468003007401c0095200ea590300702c50344c0100c100e1250f01401100b030000584101e20300c3c00c45103e0712080c101e0380e50078450001d0514010b612405940001d50055a0f2181045410503402c1e00d034019008142d03c2a039050502421501943d40d16903402140030100d03a40f07009103d0044400640880c43c5a903178607207801c0080d540500c0b5021140700e003108171b1200004400f082480d0200070410007a00040049140e500300b181d100604061405403030f040704100640711380d0590192150003004030492aa1040d86c40580c01c40034041440c2c000074001022000380d100803884010708070049034000c0500c0301020f20941070f140700000c0603146810440040001aa001d610483c080d07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 797778120 1250 797776870 797776891
    0x1090504060e042d06020c060f040308180309130c0e042d061d0108010506010e182509030201120e03090603282309031e070501020406020718021908 65
    0x1c4c03080f114440c000050020803100b80c3c1e00031842d2881a10140042944514200c00a141c00e18158800404a110161118103041221148220301d640140100c0d950114090a00740e4002c090040130401084180740e03d400150444400e40c2c1d00746043d02074410600d464100307060b502c12507503850070041c04001e2481104950390f6640029903290b420301d0301a10300880203264106600d8120b030309003501c0700203001c5810003e51501400342541d5000340c0e000c101d098040c0390040e5030344203c01c13006003801c59130540010131011510308084035404180303603052b00d10030781c1c400c290070184c14884000e4803440c4200c401c0d07580003440204003070708000c0e01540e8032101c1e0560980c07074840520041d00d8050000d29008201075190710350708002c032910014450588001041c1c045e52860018509500e0307001e8241d00320307400c3d10081c02410b112440001512052034102c00215651503685070065039404051050041c3c040d444c5841200d0b6800d24420f4481094950309001c5d40102c0d480411038040d0381c003c1104124 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 797779370 1250 797778120 797778173
    0x7030c121a0319020904062c010606141303030503131b2d030308070224160203131a0c0a05060411060702241e030601090504060e04 58
    0x6144500030a5081c0300905010300456620006040c1894a0303c000c0e400d224400c40050401610742d00c40031680079401400001d9070160382010420118410404150314a81003500456019010740c0702c032044841c3c5807a01c5074014614107080c280c1340101100780300c48040b5081c2c20030101e4042c0c002190311025201c8040001740e2981d460003050383d0400b000814101c034414082c041c003141004d20745c05407616084002c030107000101c0f56090380202c5000050400201c5400300e40418004c03c600100d44044071034114802c100383c04642078a101c22104000815120f0003c0c008003400401207880c0950001c54035046141411100c9d64050001c480900d6410003c00950104ca0f80a00291002d640300d040642202c1c1002d003450100d40e40003011088c86404100b00600c01a0350312003424013001c001d402d1010880350801003c005c54041e03111781118859180d20710049589403040214401c0400b600c0c3d103440b0340c0d04d46042c001114400e0081925540d000f50106d40490041040e02480e520500804c0c142c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 797780620 1250 797779370 797779397
    0x7080303070210060b0301230103060902120a1a01020304270c05090406050a0b120405030d02070b010305120a05120a0603020310021213021507080903010510030614090607030c 77
    0x1540c0d0044880d807005030004010032050407183e01a95000300414049141594180080407080d11818801100c3c5039050506259080c2d000c4d0700800c004003046042151170f1305618410280b607110403201d42203407d182010300e0003441000d1419106c4000d06a00031402c141c1010410484604223504d09041000302e02c1400d182d000c01d9001e1004c0390905c1c2d960719038941d4074003001d010554510350840c42c400d0941c12410300c0045a007809454031541c3c003050b544225100c90501c1c90540c401c601c80040340382d000042600501400a10141c12244240101c035134020958154800c5409040003000000d00e080140c2800088d2613450303e074104525100021701306580c0e40c00070386440c024408480707481d50082003062100b01c030501919840341d030000c0c912074100343d0355001034020208030404107030010001c12080248a462415680c4805014008110909002c00901406402403100301c0b00b60f801c2c00020452220822001c40c06001d07003400030041601d03801c106501a101d0300f08203408000524601c01c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 797781870 1250 797780620 797780623
    0x140a08030322050c092e241407080c06070305040b041112010e07090c0306030b0402010819090602041715061c050726060c0a1d0603042d1509050708 65
    0x280034003c1b100c0d11800485201e0110010740c0300c1500e004600c0c0d0038004042180308001c10b01d50121802d5800e2004e0324180c0442d0540301c80996850412840d0030101e02030b01004080300040c07140717a800c1001c440c0c00d50340c1d04408030140d94003158001d02000408001c2800503408074040c259144000b4240c20203040241000c60840d0801400031245030310643d400c03c0700304501c0c400e803500345030306280500582d401c42d10b0303103031500c030020704002d04202001000900982c0b441d030800388440d05401d024030180645041401c080e4115014034840030000b14400b2414840000d0048404080004a9002d07951108104440c40c0406104004c594028000b0500060001e0194101070040301403981030611502d82c0200c08128910b0300c0800e80c1c1e101c10140b000b180c1c03800301a240007004c2407a1070b8842c035090804040d90b0380c10303030038071250001c0c03000c010f0204000f046010100307109800100d112204203100c1003d0400c00300c5220281854244001ca801c0407800da4000d070580c5c0340100c1c1140c003403a507601c0546 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 797783120 1250 797781870 797781889
    0x1509040c020a110d03050415110d080103030216050d061a0a120b010512030301140a03020901120b0901051e100f0f030507140f04150801020301140a08030322050c 71
    0x40140c0009003000104211100300c0c440403c8252604c1d00000300035a4058010303c21402091880c1951a030315951551090501c100440703001429600e0700940c404020f007820001307000403000750066400007a142c40345080d03418200c2e0b07802400440c1d0002942c44013002003d504803101440340020a140160751500c114000090910b0a41007070380b030f1a1420400958041030300003e01c5070031180104946402c000003564155551842c084009441483c000748480b030080e44005d410400d6000000b510121081030b40f24184c2c003070180540f284c3e4402c01040c0c221442181d44850400c0c0300d0002c1c400e050b0448420941c080080d0a0184c6c00c517898003003c20503180282e10148403c0c1030750741c0510030400d0a0040c03800825a002e440246002c089001030010913080000d18001c655071450011540c007415841d2006290034402195296103441408040b107100c600104d0040000510020700000c0010440384a0410701c1d8072080c3d0701740c01072007004943d00711403410b40e15881100321070001e60b5100040b5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 797784370 1250 797783120 797783141
    0xc010f05040e1f0821030c07030807110d030608190206180d06180201020d02010b01080606090d21030e0c24070501050f0a0b03060912130e0108010b090105030d050702150904 76
    0x1d0060b001042540108010b0300c119005402c0170074001d00400c4442e09055030fa540760b060038101501d5079403900459184007003074072140c00c2c2d08c9450b5406850a81551080b4140d81c01e140c2900c1307150102c40d45440314000c030140300030b40081003080a8400311558440c1d10700d8841d401440e060703454049898480940356804610251000d02101410456030104112215204540004d02083c05000c00207000c4400c0102464007604d0000356180007030303139211045425035034061b5200c20710360b620030302c9100d02c2911044060f011a24040b484610f00d8000a80c550b1054001040c440072401c0c0d034101090100411001002089802e120205c00100c0c00e00980340316640380c00e0140b003e1301e042e034a01016900f60344d2072607000e90091000d0001c0c85001040100c00050000300e030b555a900040100c849100b2640d03c40100e0f42d5800780007142c11039040d0410407091a040300d0718842662174400b010744a01c8203055540100b0030800c199401414141c090080b10341c1c05103505400c2c00303900f4000c41c0584030340180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 797785620 1250 797784370 797784373
    0xf210608061008060c03060607060507021e07242c0f09010803160813060509040f0203161110090b0405010c110c010e030a0f0c080c010f05040e1f08 65
    0x2814030000c0420084550701001c60024520030501e000000c5031100e6029060b000c640d400040010180d407184821202e0b002d038016410411441c000034029164500c09000d03040800103c0800b00100c80c00080c2c0c042510f03072042d8406c0401041480c00142e15410101c44010300c140c41c16030a0703040750080c0303501c0ca070034130490484040748074410104025014017107002c505c140c1d6420014400d02c1c0000043e035003c404443e0400ca0080c07840c4c01c0000702d134051503d00202c05640342d030000c0360303041c1d000019002841c0180c9090081e058014801d100341d0000f12100039143e000c004414402510030202d000180820b00705403407503016100920016107500c0c11082d9060403060090008001c0700348a2403042040d58a003100c40c0d0408450f800e611a66074150070b0341002461101c2c401c072a0780c180800612182c1c00100d4161030302c014500004509000c0c03195404500441444100c039500441038040c51400603600c0a140c80c4c1001c0c104548504081c1a030041e00c041d0654201ca842004650345024001400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 797786870 1250 797785620 797785631
    0x40603080a0f03020f1c14010906081c210f1815050f0703020d0e031b0f0d051c020c0607091a070c0e1305010c030b041103060307060f21 60
    0x101d0207000015109410002c1602c10400e010154174540181d9954200caa0381000c502040344500e80041c11150446200d0707031003040000142d0fa140343d40050100c1d101d203c20f0f540c5204424200e00d0810310720140c60404140400302c0180300799400d4140c10301019081c140000d115411a9002d41121684880c82a0000e55807500e04240050307440514035903020f46030140070500c0c01c2201c901c140c07600031f8404000c0c5600450040254006500490781d06c0207080100e0380c0301d24800ca0a038042450190040c2e1b440c0c002c0171009010721001060142c80011561603070340c6048858003050984600c3c503034090802c5682403061003a203103400e0000c54002c044da60b40e854102414412400049030790002c4004680c40c0400c4020000f0f0211051a4101c444114003100070760b581b401c92000a042407135005015510b00300b280e20b40d0305d4069210040020040d1801c214524026035012880d00c02524490340c50342c04031104100300d40c0b00d00c0c28281c60208a141c032801030a4038803600f000183ca2614140215034540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 797788120 1250 797786870 797786887
    0x30a0206040221070902090a030501020f03010518040b04080711030a050601091a0904081303080406050d06060c031b0c05030316060e07061b03020114040f02120d1b020a0504060308 79
    0x41c0610714080c4060321401c600c2e000f4201c589584011070721801000c3d94000ca00940c1c1569200b00070001190003000965942d080a6541501c5500c24001e0354429091107214000c000900000b1301d202d103a10030410b17140c40e1030b507450f045001c3d04004402c0310300200c0c1d100d254401c4d450502100c041c0c544200000c02603035040008150a40d10400012081c1c0304142d00050070a554252402e0307049600100d605589402440070f03280425015000034041d5030300010001343e02a07220000702003828032020f04101c0c464a41d6011580b5101c1c1c5c030390140029a480e5490010302c8559034640d039803a0320451301078880d29510f00101e130958009500e0880701603841da4201d018840140140c40e6a0319941c40603000007418560b02420844982d45482c403500c2c01c11101d00105030007580040f8440c4050700f0000b603589010f24202d1050240408120301070108a01c01c66451140007640d2920304a8a8449641142103001040b1030110802e00a9a0080d80208006899110340c45810061030103021843d6035942034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 797789370 1250 797788120 797788129
    0x5070201030f05130f02040213122f010e04150603020c0c09100b0f04180605010e180a0b210a12050f031504091203060f090b03030406030c020f030a02060402 69
    0x4000d400b03004142820100112540313138525004040d035000c00000c0300310000e400418020f000341140c00d9030080c0101c0010404800502d0400391244c0715480d0703200d26261402040c5525400e180b00704007030066070354841c0c20329800340c0d05842200401401c0002d40e00d840c8201400d200305d4991002c4080795002031280a099400c0c170205400c100242c4244a807418a184c01c2d00d94103c00344502d00a586000c81d44040407072405c000c0b140140064000b824405141c100282c005142c0e40c45034a01044000c4e140c020f071030400e81d54500c90302c0107100d5500f400e50b03205000b00024105401d0050791050031145d991055240c0080018280c0d0441c1c001401e44a2140c540303844481e03003c00801c0d0900c241270000c4546600078400700c9902545071030891980e5000c600100f0042d06801800810040b0095032400d099603060380240103c6240c2a80700c91100c0d0b5504210040703039010f840560f010b4004000610055001e600100c003a240903104507841000860b00f030a065411959909005030408010301c0b055180 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 797790620 1250 797789370 797789381
    0xc06120b04090c170309180402011b051507030b0a03121202210c040803090f0406170a0c050a03150c1713120e09071404080a1103060721050c0403120507020103 70
    0x104c1d180154a0100d842002814040e042d021602c00c40c103240f0000760843e4491052541081503e039401400e81c441487c05c540c4440303240130000341c4c1d501007400240110b8170a01503140b0302603000d0701030680b40381151a91901030f0030310f5068505014142004102c8241c40c0d1000701180e4100581c482078a0688104490b17000c00d02504000c05d17030300d0a100600013803c01008030b81c000e1004440d2200c685118a001c64042e100e10b603ca072a00c0e03500b808800b161010040f0300314086500c90b040c0720140c18dc0720810410000f419000281880f500c01c008055124650b130f00105510049060608496861402e160320a1030300702d41001500186e01c50700d0b41080105410304030030f07a0341420f00d42d440c0c25811001c14040d400041241003002100e01c034a00c10120070000301c0c1c0107450054140c03400c51041d420921030b10340361811883d019100714000101440c2c41001c2e64080c010401103541c1c5901c01180008018200150aa60b19408100300000000e084a68016052f00c2030b5102c276a25924240000750032501e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 797791870 1250 797790620 797790659
    0xf050c250c0f0609081006180216150c1205070c03260c12062205061f0203040501143604020409050603061e0a0216150905190c06120b04090c 62
    0x2800c10300e05000c02070701c023040700c080c0f540c1d5494016151701203011400340651402d14064503880c810a9009001c400c160004554000240c988500311000108040101c41c000c4880c040090a02c03079046001174402c8004003840b10201c101404100c40b614010320003150309981022402d4000190000c4291003c1070709540b0010465601c1c05c4040d12b45816840412055140c3d1200c0d41e40c0c6000035442e682d44205042da081c0e54a070f81441d6a841210b0181d500e40c0940282e03408a40300c8625005040900c800715002d0085502c400900c440d501c02104406180c14200c1c2001001700c0100c40c41640c0b198809480105407903140400d05061050505041c0310020b0207086500804800501c00240c01e08806908030304c04400050351802080d40641055107030402c0141f0b200424681100c042d0187c1d0060304000780600140c603d20002260025440d01e04640020440e1200220070800c1c103010300c02c1c121002038103900c00300341003181c480003e04865891380b040b075105044002c180000c12252880346c2240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 797793120 1250 797791870 797791903
    0x4051e010215070507031103071a010504060e0c07141e0a031d0114030a09020409050106090506061204022407031e0f05070609030903150f050c250c0f060908 69
    0x41c1003da000a00fa445502c80c09814040608840248444100100d8449a402500411004207803125001c1007507000c1c415030740700b50308000c000300381c584a14142c24000c88031a90260311301031550b80d0b500e9190643d02d02c440303010700803206006040c00701e401c010b107400d484040151005034814a800343c0b1480c131100b49240a40143e03659040c480c2d8010b4010485249414846038403a910304000f5000742159a20007500309080405074000c20605411a07815140500c0b010310080d40c0d00014401d0b14001d502c4d4080307002031041c01040c00760400c01070342d0000c030072401d0910542c0c5a038002c901480350b2051034214000380c0161954042c5c0501c0c2014031050304000d142ca60709021313425400510b18021050080c10a5550304201400c240c00f0340180360003154000c10345180741407003062440c01400c40c1441c1295450420300040c1b0480b009000f19107200c40e845458200d56100402d441e40400a0b10504844158a21001041001303450700040c00034829603a4684100e070a02104505001c482000328440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 797794370 1250 797793120 797793163
    0x80a12050c0901110c04180c0801020702012703020d21080c071728030b04021207081305030d230f070c0c030623100608130302010204051e0102 63
    0xc159001102c07004142440c020901c944002c2420f400d21700c030203000f20384c020700d01415040040c040746074102c1c03084e0154501484032551024040e0a07482107040c0280041c5241c00107e8503408000060300c402040d40d51449290740e01c0c0d5000c06c0100c00142c10548882d5188041e403070501241d4012800600c0040c50300c030200e41860030144595016034500280002042010342c0c0201e1040c00c01c0c1c6103820522107414a00680303c00710003810800c503100e0707500001c1c00d00841c40ca0300d040500031170f0542d040c4500e081c442540e84600440301041c000c0c3c030794000000201100804101c00704058002c13a1034146d0002001440d10700c00f90903e8441000f240c000072035030010030031000301c0694030310381c031001c9410040149890f6180842c6410140e4000a04d558600311088003101148500f03a405200400c000a110b5100c0040000141d1451700c00c01c80051040e40010740c510000c82801124241710b40005800c064440d80001c000f002c5010305500084071901a1100304d680c10000c7c5415170302400c030701414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 797795620 1250 797794370 797794381
    0x20316050c18090c0307051e03160e01060207090608030a030e030d0e030a110109230708030301030501050105210c04020a030908072108011208070213050906090706050f03010513020412080a1205 85
    0x106410448000001c018040740c0901d0191014007104e40f43c0040801d03580c500642f1408640070082013805480c00601c1103c2c80820b20070313028401c0d4016100003000440c10100d80d680d0440c050048480340200c1c6010501c034000c030f52481405041510140c14000e10348603145442c0c002c10600540c60ba0291036810480c00c4004101c2840d031301c4c10210a004444401001071091980c941a65a0302904c0148000000041440010341c0f15074142c0e0b40c101d40307558046640103d001509880c6402d050b4440d0030140c0600d50924080d4018404204a400c1c00b207000713481c1b92142100360b0000310003503a20002004a94001d04410250254510307841d00b0800c3d072550500024040c500c10101c00204503120001d100030039580c444e1602840c40781e00701c07424000d5103001036456448040076180c8882a115208010804a0158042c0d50281580081031411a0320307140410101c81d0b08401224503599003003101080980d05002a42e260b14021060b203030b541c0d0f00c0250001c0040700c40000c1c1a803090301d40801d01c44d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 797796870 1250 797795620 797795629
    0x10030c09090b01020109020907020616080f0f071806050403060c0c0804230418020333150d050d0810061b0606090c0f02070801020307020316050c18090c030705 70
    0x14181c071030801c8002044202c940042c2d0040110402c040e6021030440e04000308145c0c0000d44a10809400303280440540421100780c0d08068207650080400c001c00001401c1d5a21800c00c1c45d500411900e0311410703201400641880f00c2800380c201c2c0c00041d4001406000703020040c058409450824503140d40418420340b6400228056800b980c6000c40081c1016480742d84030301c95201d503001000704100f040d0003029000f24040104200104d00074020344055501949400c040281c002e0105001c400c4420380840c003802d1400c9000384061088403004080790010307103079804058803c2c1d1280c8018101060072080240424000404c20300c03002a4041090100300c0d40304002c191a0140880c005030311803201c0c90510007a29846d040311110902e40003071048541c0d4040d16105860100c0e80070394550380d49a13031541d1b00380c2c072040b41e00c00b015078401c1240e4855103000010504069002d442503620303400801000078555680850300f034540701c00410600c04c03c0501440840344180049004180b000e15180205 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 797798120 1250 797796870 797796887
    0x1006020c09130c0f051804021309050f0303010f0509010803040312080c070b090c1009051c020a030c1211040504050607140d0504140d08280209030607020c10030c 71
    0x56014441c0300d0045045480215501c281c100e80c03190b951000c0b00e48400341d400000b00244901403241d00c0c0000f484500e401c1c802c1c00180a50b802500c00711545241524648c0a0205c25904481e9071050f00d024034415041400558060540c942c0400a0140b40408210300b852042c3c002000503081004100001001c484902585900900713040100b0794540d0140f030a05d000b00d4101400c1044501c0402120900104e0f1500c9110b1040341c000e00b0450800740d08640c501c0242c003504d9007220540103006000c0f8140c240036600144000d0940c00015100e07903420300c0c541c0d0705a20440d540d0110002c00f000700006203515210080041c1d800302720501d41600e43c2c9a441314040c00381c030107101c24103d0716403040e4440000c6428400014a0034405410140b604a8850780c00c2003542005020301d407460349030340e03109001c0c1e98051036584400d810924206400d0701000300c11a11014409542040b030069107440c1400740758801c142e5900a0034000d80c0e04401d00030b92141010342d540803d4902224590b0150f00440710 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 797799370 1250 797798120 797798143
    0x705030c04060e010509030f0a02130b09040602090325050a24081909050703020a080a261b030909150a1214060c033c1e1e100602 57
    0x34003900343c02000586540c0321707122016406025010704a205024002034000c0007620030b441c0440c401c0c3d540d01151003203030407900c5000d42c4103040501003030200d1000e03006480501402001e542c80c030b44074101102c0d14001445090401c698400404119070301d4101c102000900040e03140440200407100600380071003628018000f403155100c00704090500812098a515084420030840031089090960ba0b8103007a1004901c80c1c010110007003990b180105041c01c4031981306445208007001601c1042c0c04514070348010469030000e000c501800e03c880c00300c1c4100450200042c580d070709000401d10082140c0104600542003004003668101c0c2c0314040c1070030484007800b1040c00c2c00707a03492400484500525000301541c0c0314100511108098020003140a419008503a018046554030320600c4074041032410b88d07038140344a01d284071148480020540c0008001c440c181016916240108007000a0b80d404540420201038240d134000d00626031900070351030341c000c542000c2c5403600082d038807500c0039038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 797800620 1250 797799370 797799377
    0x20f1501170c060a030609050903130b0d11070c080d1815090b1b070906050a05060f0c070816050901030f060c02030c01060b45060d180501050705030c0406 68
    0x4030010341007400e01c604802d0b260000c004a0f41d543e0219401000f61944d4020307910000c2c80d100100341030740000801c4a0303550804103260514585003402003a2603401045103a2175182d03c85d00b401824034007460080c581648650a1240c08900b4824040c0ca8011610100381c203120f600e01c6146c1440d10740d040a0300032200c1d21b10075904a9000490304071248100c2d507000441c48072010800382019224030f400809001042c1c2c04940700d19a80388188000d8070180e1285540000000340203100608003840100103803140d03803080300e00d45000c04d8a000d107040c100780d12640113600a04141e940e43d500480d40ca100400c0d040350100099411503c64164013600000c00914031a80d60520002c0c0900a005503410724095a0081008954035031078085664842040c640c415207060000049a140c0b0303800b846612403998461400000095502002d64015124000d0b030000060060201620b80c1d4010b0b040c0005141652802d04103a9141082c00d444010b080c120a1020501c00c00080044a405440c11140c4516 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 797801870 1250 797800620 797800649
    0x608010b030f150f041a010e090f0c1e0304050a0c05041109040c030902030609030c010c030e0316020109120f110102071a1e120f0a0b010c0b0a0f090b0403020f1501 72
    0x3000900203160541c10380d410078201b40c042da44040422007150501c03a07007a210084a00301b41001c01228480445443c0b1111410300046142d500c14100a411414051020a84040c4c420150302107250421601111164040d1011008204008940304000d24098505100354015020803400c940109030440380144e5641c21203440281c4243c0010316829006000d80f401030801d00016903c03a8001040c14025608085042c4241c610902c1040c101020a201450034114240603101508000340b00036030411a44003404281c400348922440d502302d2040110a0b12a401c924100c000070901014041c1035401082e000c006030981c500041c82442c000021903940c07404480340e61000f00c4014928140c0401003c60044480c503d02c003200d80c0105100d1428410690760380c1000019200500301490008036400100400191350814640d00178282c0c50011815501480300380c012200010340c180d44803200941440b050507010300c10f000e100d1403141d02801c2c8031145401d4150302c9150621030003103202c0008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 797803120 1250 797801870 797801911
    0xf0414040b121c0c122d090303170c0702060c070b0403080a08180d050d06090c030b01090602190b04031b03020606030d110607110f0a05070608010b030f 67
    0x5911440c0d041c0d100600020402c19042d5800c2d684007104699008100f1149011a071468000c00d0f2104400b544003a00d09003154041c1000c079148041406011981c50154001d0303c0c0417164010b0b0052040c000343d490b0030a182c69070400511030322803440e0040030059882d090090342940e2204691000f0340503103403c1d0f500c0c00c1811425282035115803010551440104020080011710310062280035040c1d9250551602ca507010085c004c00c1d6800782c640150300c110702000e00f090040024040045900c42d0000740a40e40d0824041641e9580c040d03600000d5858008001c40d681140d0039602500e91440145561801c0345a482d9031b860002c14003038402c82c8194000b0381090301c02d0114107001204210070394000b0540b403501079a110340c1543d0081c828020340c1d81030f4440500c0f54800450000202004207066110903009858080406c81046550300824510081500082050000320740c4160010081245407070303001060410180c2042c00c0907001001417007500a2080341e8543c01c8110343d4000f002c0e07203008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 797804370 1250 797803120 797803129
    0x60305040c0b030f0a0e0f0a03081003020312070302011d0607050708360105160602070c1212090e01031101031518020403050105010e0702150618090607020c04020f0414 74
    0x5030751020b4464000001004035010705044407074000c034080c44c000e00545290088868490000d4200712a144d031080900c00c002c20720822103290441d800180220728540c4070303000300e420b00d080300c203401c800d80200044d28000c141c2d0902c86c2083c0030810962040c4030300d218440e5a521752102900103800c2010110707208050040070000c03559201d8401104841c038651aa45042d40c14201c050481040210f40e498040c995000c2c00441d007008103040c500c40001c10f0307982e5076200203403c01c5a007038502c2e000d8104042902e110801d41d020f081c90041c01c030156580c614042c0185140c10070340001d0b4503400f11400400000d0060b55090240c00800d09020403443c10007000f004c40c0642c241c4c00a4903000c801700c800070720003410b40e000b80207507801030009020036a02c8a54580c0b00d030030241d0302c5a00685c003c5420f240c0004904c04500e800004c001d00f003094622803c070603410002c03070569911102d50800303414007c0481c0c042111324060b40301074400303608010085003c04118003c0784030b09400c1174a050020300c0c19954 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 797805620 1250 797804370 797804393
    0x10317040302011b08190f03150f03030c06060302030d0815030c01050d0507030f1529041701060905070921020102121303061b0f09050310020702030c210d051306030504 74
    0x46e07001000e014900440002425040e01c05450004246441d0f2a8000c52555080c041e05446022030041c1100e440c5603800c81d43d040806405a5069545040201c0140c1d0140100201d10340582e9500a00341003030300745011203050000683e40320b87d00008589040b03076000b1042d150443c0103030030300141b59030f28168240c01510001c0040c4d800146001d0b0703485242c07826000105c2c25030b1100500980a1005804c076442c4da4070306426a82c54150703040c002040010342c10f4440d07503038060350369002080390b5550388401402e88900355006004100e8402c801d0220321a03429442500144015100c504044540c0000c0e4460702d080b9070950b000240090707062032030aa0410b101006540c4000c00b00409004000306564459102c02403034002020004050405840768031a03000b5900d005001d081c40313281c0301d44800029405030320704036014018002d202103d07540d08250042c90000d001c0c011041c1d5010203c4180c1000c03c80301161051140a0004041c00c2c484c2c2c60001c81600c4145c24002002e44a03801c100e48030300c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 797806870 1250 797805620 797805637
    0x20a06050a09061b170c180102030c01020d0603060f0c08070f170103050609060c0319050415150303020d0f05121b03310b07030c120204090203010317040302011b08 72
    0x4c2c04d0502da800c0f5180c2c0401042c148a506940b10a42007036070b42e080504484040d54001003984d018081000600d403581c058400e032100500482e841c021452a01e1402c2e03030000c040a1800b160350381401c0050040d50300801c668001d00041c100144008904007030612907016004c10200a60480034005190050007204242421100040c5540d030b524035005581d100300b1120f440f914058040403d182a005200b038a010b450b503040a00e400c14001d2541070000c1030000c00a60f5001620f100100c1000c0e0b551040010786928641920340f55425070a002e0f2070650050601d400300861003c41e40b94150380201503c00201c0c441ca40000e40307444809551940101404400864510001c00c0c480d10421102c0741090903140b5440300c50743c0711100312410404090400002c0c140340503220020b124039100758444110398410f4104a00622140f4200104036000742d0088400c2550000052080c4645245120f42c101f110100651030b050866000810083c3d8503282d03602920381e454608010015040180c030106c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 797808120 1250 797806870 797806883
    0x1060512010e070f0501050d090314160605010506090a050409020310021c0501050307150e0d050714040b04051314031603170a090c05061b030307020c090115020a06050a09 75
    0xc6411010078000c1c40e9040040500d4030505000162005405040d02d00704c0d84c0c140c43d8541042140134121000d400701c41e030210108424204021034040355803018050000c010340300000c2d008001e03e8280e0031910180c10440c803c0605000c205800c0c0d0300c8040400544500303640104006032188042843c3c904084440044103001140a01400441f2001c0d0010405550030910041e6038590600d0f880300564001c01e103443c1d0410440b801d4160051400011a50740070f03014140c0310800b5200da6090045079040300d6004103640c1030300901032a103800f070649888000c40e410002d43c102449414214940c00340010910028840c04a500083c02e01c1541e0350091440702040c241c9485160082001ca0750b04540f441401404003c5081c031003542c819100700390780c0003071081401820312081000075007003030007074110200d5150340301c0d02038403010300186010307c089800070800c5070103039000c100102c4c0d016040742130007843c01d82c000340465038006461034199400001c0002e2580b100d24412000c1d00c810840540507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 797809370 1250 797808120 797808139
    0x40503070905060307060e0f0405041a0c0406020d1d1903080c0a020a08030901020a021905040912031119080c070204020a170c040614030709030b0f060f0604080618010605 75
    0x100744140d003249104071001c40070358000300c0d21000103072001e13600c901034682c10010210900d10700342829071269400600034600d0210030103510749078800b0b5410880b42040e1000e00410100b003420740402c04091004440d003000080c1c0b0b90850b0901c103074528550300491040510301c420311110440c4006100140d07401c1b192040e56039030104107042c1c0d0740c591003008a00a4240700c400044117500441620001c4c041603016104881d150307002c0094104281840341250001460002503a07079441c85040f4240d84240400008101030282c06822903050804848003480d0411648a010700c17038941c10300c1c40200904022a1700d48412203084024050150000c0d0428400240c07050907a4119080401d0781028403520b090703039510342920854074003c600c159404900ca54804505c03022070840510381c44401442c06005159580d15105d0380c480d0141d035410880c44201c3e040c0710080c20702e94000e000c4081c040d14540d1030140b810302120754544004140c50741d400041c0c4180301b40f203002904032200401005060b04038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 797810620 1250 797809370 797809379
    0xd1704032006071a0604021c0f230a021305062701090b0f091816141206041e1109040608070506041e0806010f031406160f030204050307 60
    0x1520070944800c01540004051581c00c14076080d011202c01992200d072014000e0b00703800503980c50346005011641c0c82a02030052030080090b002d5501d80c1d204407001c02289001c1e0001c103090480d00c0214501c004140e4803541d101343c4800f0502100e400140268006a94500032071b5040c03404d80359030300500e6101c80c0c000b501104075044840b654250740c064100541851001274015160442c0d20b1080040c905002d20810000ca610203000d4a5200c1c4060701103116510321800c001e010701c00071507900b0201c0c1c045400344070341c407a440400c015109441a910705e1408064102c8500c01200007840188180e848001c0c4000810300c50540f003600410380c54041c414907103038461050090700103686207801640361250005007040c000230340500300c4802903d018034082c11300d6032007c0e140d41070f10b00020a4000d003038030004009104200c000d00070241980c13081000b5041d86401040d21140100c165400c1c0c0c0284284101004c2e014160071400a21703042603e600c0f00e00200a4004e4011907000c594540140c180014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 797811870 1250 797810620 797810633
    0x303070810030b040c060e030615040c02030f04081e03091c0f050604080a0e011e030203070528111c0f020f06011e0506030714070204062103030e0d0c020d170403 71
    0xc1580c1c1b09807134002035404020f080c15a1194100c0384a081300381410a4202d8070b00f0250701c0702e803002c8603a00c10f030f07450000e000340e0030502035100b540004407541c890201d050302c00c0c06c0c004044e446c0c895403802851402a1b40c50020364407803001c86030303030421901c40c2103114204805804081070050b4003105071126440c5c07506002d925a0458a000004a200b890350000998445c0c1b032142d6181084041002a02000040803002500014a55000e0103c00c01c102142014031540200c2a144024100340150301a08401081004903403a000702d2544130505030241c002401c4549080002c462600c2c03000d000340041c0c100d243c2181881c2c0c403116802403000106044804414903d00811035a54101881e90f0360024003642d44011102500000c0b014601242d011585d0707401400314030b000402c0855115260401010f4071150350310100400302c0e0320440300b000c041e0580101c0c1c030b50980035005016078544854014140c040580380091141500804a100700200b04500043d4000465000c5072501d41381d14091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 797813120 1250 797811870 797811893
    0x109181407140304080d0b0307030c03050d08041101121e1b0f0203180f13090b010b03060109141c0b010303230904020d090602030712050c0c0303070810030b04 70
    0x100145034440d000111440d0089210311030201c003400c407a92959490791208102c40c0c1106154140c00c40c0c0320030903000199004c000c1c550146008600e035103000d5103185051842d012107110541f05001c500d90030040403690a0300703405070707041007801c02800800e015500d480c000d1258110043e1010440c000880700c0001942c00107048009100c40c0e0084d03184900d0080c3c84c00500544060300603401000b640e2101d4000c041810340d40030f0040c048929202c69040058a0b61244907a0341d43c40b10b0703442c0a001c0030b0142d0b1135417090050120004d41850760418000080001c55035010f013140d00c0e001c405c030007030003a01e64206480280e48040400a80c2d000189004440c4240c00c1c0b000b500041c0384010040c3d40104910002a054020b006c9440c0c6040c0303203103085c000690842d4060a1b606070b41e42c0000400b180032400118420f03c0b1680d1030061010b118502d9904483c3d0181c501215004c0c10320021000c0180003003100d40080c1d407418519055a5940610781d240e82454200401d0fa500c10414002040580c0414 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 797814370 1250 797813120 797813141
    0x50f0702031f090201021b060a2001051816080c010318020d06022808011a19020105060114040806040201080405031920010b030a0303020c030f03090a0501051b0f0306010918 76
    0xda9011000e401401040700b111074602c2d40c1d008004110081107140214440d5800310301d0800070000030713a032b0038560a00310b030803c550004962049145240300d84034284580e40f01d40005071414180345050410380f940d100c0020010b9414540d49a00c512481c140d601e5440c00c2041e4010300030400803070740e07150000c0030350410340d07944002c100c84101d48141d0648100f0700700d1507a0169991980c081c2c0c07a044060040b0300588042c00e0f2908070420545e01045080e6000d03a4194496800104240c140480010b0171103800d082d500f4000708003032105004d2a0f40c00f24002e0340240e02403804e00055210760401034110300c1400d61507078204c00750011100350329400c0308031310794540c00074101c2d0008424060017141c00d844050359407680c1034021081540000e80254090001144090202e9090001101c8001e00c0b903802074412440300e81c0000140b4080003000d00503680c1c0119101c2803907a0213440014184414000e0041154601c10080700144513a403003000700d1402421074a03000141d10b500c1c40b030500f0040c441c0d81e40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 797815620 1250 797814370 797814373
    0x109050f010506180703020a030e250b0708180a1502060106030b120a02040c021c2f0304032607030309021806060d150305030310140103090201050f0702031f09020102 73
    0x1070560b1400781e40440c0b400c404d10b081c0030115501e08004030001d42c000003865040c1a511500c0006040c0100541c2001c5840142d003000102e01e104101c1c051400c0990050b070010700c00f0488140003c0760101030311440504c40803200f8006040600203101c01c10320b80c200002f03154203c0710002e04280e001a03654104c031465242004048190018403104000d186103c001d5940b184441100605041d8801c40204a03280f050750842c104c207992250300c44103030320040000907240ca04500140703940308001a00707070b800d4400607400c1c0310300c55652941c0303a009d50710001d4103011104001150140c5010040b0300300301c50003024987d0b50762242c038024008106241e0141c2c040c040704101902c1108a220318035006080080685d4141144600c0200240c40c1c41d000c1c0500302c0913800d800000089081000d1802441943d10b07001c0690b05118180b8421448221142c0c10107003411002d00160743c02400721500ca003401c002c51559807403207001180c034010785c21185e00e078214200c45030000141615404481074610036070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 797816870 1250 797815620 797815631
    0xa081b0f030a0c09030c050118030b10031103060103030f0c0f0b01060c1209030b1305010f0608011d0606010801030803090c100e010f090b030f061c0c05040605030d091a0c0109050f01 80
    0xf9000c80c1c541d201400018081c04105409002c20f6014a60996034007600144202020751030355503021540038140d4000c4d6003449505400d10810045494040c0007003015401007004e03600d161801461146c50182c20360030f22518441460a000c00250401e03680e541083c4000600c1d40d5030741e4020881c442c00c80095440070814145040c996100301c0d500d00407290414601e044503114000418800d18034a1012511590380741d19001002035280a4100140f001100000d00da84172940c40c00a4091281c0034080306410402c00c100e0503a8000040381c4c15607400c51911a200c3c0d962101f9589000c0250108580c002111500e4044840d446070031785603261000c0c1ea039a412880420b600340e41c81d507542d00404464080900009240307030726005030039030f0200300280241c0d8007003a00030064081543d00345042e41c90200d500c1d030074040c1d4213203405040010401540141009210810001c1000c500d50160f180c0060010000742561028141519400140c003c0200f02a494500d040303a41d036014280301c0703c090750801 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 797818120 1250 797816870 797816891
    0x160303080f090a050705010e03070509011d010f0b19030209031b040c02030a020c15070206070b010f120f0f030908030c01060905100614030c0d14042102030a081b0f030a 74
    0x3240420a103a0704c03200034040d003820040151060641805c600b5014464081d000a20fa078860070710600034003c521846514807000c80c3c60030a0820160061807084614000030004821014112036021401d144c54502d003584004084000e44a0162025818418010404441c81c000b43c0140081007084800300844048040b043e83c407030141084040241c0c028030f40014007030030704200004540b0700200c0c010b490f000143d800554543c01144040c0d0b84c1c0c0d41e08030018040400c0e10019000a071025400e4003400f080e0a941d00e62700a0300300580102302c40c4065151404042c0a0b2140d1000b501902c001c5c1e9443c0d45450f00400d00900b180d2241d0074807281040c01249440398104010000daa25907a0f91560991400f01c1000e141d60001e408004c841030100030b4504520150b2050b02040c00da2210115042c0c00c0901301074965102c00e507041c40955071058100110250000304881d61107600b4240002c140c3e44000700e01c0c00704454601002c1a8036000a401e80f180e00c0c020004611980030301c0030400965406 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 797819370 1250 797818120 797818123
    0x203070b18010204090b030c24070f1211010e012c070f081006090b060d020d0e0712020a0512060601210203010f030b0a0b21070b03042102160e06030a05011a0301140c04060f02160303080f09 83
    0x207440000261080708047200c00e810300035640c00000c4108500031500e01956640108460f0215035101d0603068001e88603002c0c17040300b14010345000b0300010400f400a00c3c100e4000590354420000b41e0050590700041441c00c238101d941202c04a07100c0541504c03d075681e5191101d292016040e0101d10804100a01042c1454034150283e540c1c0c0c20640184190380d260001502d04000c01c2c0320080d041c04601c1071503d41a074690000307501800c80a02c034059110300d1442c1c880a404406403188114600b4034001c02036507100e514a51000d0000e032410070303507024040400070381001d02c5600206400c0c0070000800c800d1000c0c514100400c00c034495000000299140380898a640c400d080d0701c3c96090f003100b42000104803600404e500144001c05903401e03078600d03a580c81d08640da85640080035501805032006249820702c00d003c0c01155841184010b0b15000e038000c05a44035a0040005010000c050084007a20803c08040444d1800500a480340e80300d0501400040c41211051007080180b4006503c4820 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 797820620 1250 797819370 797819381
    0x100b03281e0e0c01080402060706050403050706050c160206210408130609060c0201053a050105220f020403080301030b010807090c0203070b18010204090b030c24070f1211010e01 78
    0x1040c80c080d020f040004001102c0484000d001a64406401e0000d40c003c83c00902c10140500d2294403810b682d150146000c2080e00e17001480300f20414004d1020040222044044825259048462940d18002e040071204410b421468001400440c8420041001036140061448105800c40640c10179034400c13003110302000d14015100029212601c41005500420141250910030107960034a40b210f030505c2c010000605c00c41d002d40f04510030717520348440c1c0c840c03050034054032054410010380102c050b1404030803a640b0032203c00c8d0aa481c2681c3d43c2c88521b81d81510041c0da40000211f07600d50b0f503400c00401060b070a000700082d0b40103005000413109000d2203285030b000e802c2d8004d1401d10140c0d4980c000c0c100c0004020001e485513500303004160035030a03c010400b40c81d000d0800503c401c1140300303042c945000008a0750081200890b028106d182580c4c95180c10031200c8901c0f903603510107182202651405c100300a1400040c6a02149016000342c01007024a460000801c8820740b0405524240d52 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 797821870 1250 797820620 797820641
    0x603013c06270207021206070908060c0f0309120f040906080a0f02041a060d06080c03060103030819180b01030b1b25020d0b040b090303100b03281e 65
    0x20300c100c40140841082240b01c1128031151035006007005110307000300380d44040c0e02001c0d8816401c0300040081c10341c0c10201410103000721400078a154907004290102c0c9100c4c26442107201440030000600c07255040103682191410883e44646410840407280540e0f00640600c0ca04da506060010803038440018000e00500d40092180c034075154580c0900008104880403e20055402c0b0986420f0307488103001010b070920f10040001e41c0e1860514810f050040a0b40210f1080d0402d400400c04039900058160b00052039120414100c4002c0a031913006107107a90740e40b020541e0a4021000b402801d4800a04030303409410b41c2c1c81e4580d10040c504003a01d50451280d9903031b1030b05118240b004a40810350202100394480901032010302500000c07144400d83c00b00b26100381000c0c0c204410004264811900000c00500643c10b50800e4130901312000400d004c0c00e09090710100c0080d058000303001d444c0880c003143c0d5400f1403603120b202000d0030140c035070820314000300550b0303245c51581d03810f0300e02c158910710303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 797823120 1250 797821870 797821889
    0xa1a011a0904090201030b04090803010914040b0a0c2d0305010803070f03080c0702130b0a060c0b1f05042f040b040e13050f010e0c0d0b0402090603013c06 68
    0x1c0c1044010030030104207904160b0341c4c40c40c1a03007946075441416417213030107009410348039854000a003044c0c60f10410103028461340401404002110803104613002090b8407004581c2214802088400329060841540000c4c070003101100d0f111075280810a65500a903018070403070380c0b1009091340d648030300d540083c059040e054580c0d0110348070364000b6411200910110b460200759400040d0000580a84000c03c01d070784020641c418030781010f596008089a0400e041c208603180c48901c030721040206151f4091401d0403410302d40812401c00c03540500801401040b41c810441c1c5024010045e81e84003076440301034008903084d0345c814002070314200e803080c11003a4078003414030081002091000e0f0581d3300103d0400c1d0000c0005005201800c81020708a0002807070342400b80e0503901d00300e54003001b00e018140e84c14440c0041098001642c0d440f58040d1f0f85c1085548840b0040303401880841030900e09900b0000703002164540c442003000b0703031075003a0104101c4c0300d400d84c505000b114001e204080c1e15 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 797824370 1250 797823120 797823127
    0x813050c010f0504050d2a050105040314070308070308060118080a2301021603020613080412020316090b0910060f12020c10050a0f09050d1d030a1a011a 67
    0xd56120700e03501030390080c180c50228100b0380d540012440c005042403003110103403041c2d40340c002901107981c46001042024511003203250b1034540040d00d507214038000900307500c107281c42c07414800d40c040180d60021903000e5a4560b69880c0303810000c1121109840c1c150010740040d00300c042002c0765459181c10b44030b000f4040c01030304005070340310348070000b600c4161549402c92000111b0784074030a101a00e200031048159510035005494000e00301140101200119906102164042100d401c180c82c2990485650b1002c0180c482c000245440120110348040c03c1d1401404501d10050b03410803a8620000d585056007500e4190aa80310b126860081c4400545081220385940d40308460609564034100c8005150400328031049003000407103202903810a8880044c08042541da1280110100500f0340400420b03a181c0da40d81e445212000c410340400c44030445286109000c00d080800c1440300408864802c1d50b9440c1c03081111030383d2082d0551320950b4070300014968110001c20b21203240141003030781c40c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 797825620 1250 797824370 797824393
    0x3020f010302071b1509080610090e0a02090a06150215130812151309240b0607060b0319171b010c080603010b06120c032a0a081305 58
    0x94025900507943c1000f01000300013551240c081c41c4001d008641c00742c410200d05000d01404445440e48000a40d0307014a0802600388103401c1340740180d0f076580102054003d0122a01460114080400b952152945007842903c41e0158001c400329801382101c0082c40443c7da505a0300c8040303081030200c0e0b8000301d000050403940c9041a01805c3c4c0d1040201e6420011414001041882c00310303101c12001c403c2c144103001d18584070340b02038280c1000300c02c18024543c80e650380304500480602410f100c409002410b04100c8195000742102c4500170300266104c20082c202600034110500304503001e03000c1c030b0304c0c10301c000e440b01400c1d111580d80254560200c0c1c0c000300d024400540c0b020070f0402840030000560b025100702805900a000c80e240d40b50b14142c00c2100405003100c1900704580d210b60300802200314404698038403180e11188540d107003901c944c0c0384500c03a5001e5441d00680301c0800100c0d41407100107200e440c00703058940c0035640d800e1403d684030502c200a1080c41840540180e2204007000c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 797826870 1250 797825620 797825627
    0x50918040314070308060306160512070908030705160b09030706110a0f051608031e03061207030c0e090318210607020d02060a15030f050c03060709180603020f01 71
    0x503002482464450700504181201610b40d401c00e860840c00030300f1080a006151500300581900420551080200d00c940d6420103441e5128061401d60940d41004c0020701d0700303025030103601c010007500d01034991758249494900d4031080007542d644c100810550b8042000e8954505450b080705001d0000c1510034240712068540c0001c0d8101003201c1d11419045600140341c40140031141841380300144222142c0740e110885200c640e400102d9154024031000002d9521400307451513110130007004582e81c0d111103010890a43d440200d0139694840e1340c400000308500e985125007101c5a00c0403401054840c01030203074491146154061008076294007403a018034140c0300e0b9100e1401c003003000b41c01c9032200d4480182000000c13500f480250304040811004180c0504c591540318008040070410411004403440300441240030190000014041d090708025040007400c0203450001c2c2142c0f0280b030007850040c01c1c08624050749140c80d0b0310040030035078a0040d0141c0740640e540140060b2000380ca140044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 797828120 1250 797826870 797826919
    0x9060e06010c03051c1e050f0c04051c1b0611120d020d091a070e0d02101b150914010b090103060b0a05060d05100e0708071d210105070509 61
    0x201148136240c1a4141408506c1100c803050106803101800c0302a0a03504011120014442c0400040050411000d00b0b882800c031002d41e00d044600d10390780580d5520b007a50060b07212000810001d01c4041041131000d8030440c0e203040718180d9448080d039404400980d6215a04101840002c490503c46040c0010084d0040d10000c03090000000f0519000e48600070101c01c540e0202c40501450400c0c44426513124072910a41c1d102030b244041034031215400f040c4844c4612007048100b010400f1194a00040c0100140440341c20051010144030340524540082000703501c12150b6500702000c0d01503132a0103000d129480c40300280f09484070380c40c50300c0e56005840c40c03500e196405403014502090036540d40d0040c01c107084001100182528000c01150304d424495007100f20100d4000042088030355126511940c407080d980741c401040016128840c0000d03000c050420b5200018140c9205171084104040c158039801900a00440e101c07092b0135103091041e041c44641100030080035024103ca0310300f12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 797829370 1250 797828120 797828137
    0x6050c030301150e130902090106141c02090a080f060f010815060109120f0204060b0f0a052808060922020f0325090c0f17060d0c0801020409060e06010c0305 69
    0xc4c0901d04c0c000740008240503040e824924495603a80c0d074031029420500724203409003290b03052003034100314050104ca0b05401694405030b6100b006002406c0340800c1c580540d100314102520900081d40c455440a881d03d0943e00c40c10454411400042c104001003000b6038103d84039000600480703404801c042c07501e460021300107814003840b40e600180030f4615071590040c1d00d00545100d080000284104426a84541c1c40303034511107403d209414002304064201e030300d1428507051542e91100303400340e40054428a440a007441c03034040c454241038190884145440b0700000c880f05e10440c3d4a00c2c0842d1508050b2515014844454001c01d10050030403031440081844020308441d08411101f400c40700001c05c00d9000400711025400030002d074400c900503d2080052801e02c203106108003c03000340030181c9122140100302507100803c195407074282e4644919a00810034448403901d85034140d01030b5126200300054549021000170f0049035040301107000d442e0584d0390b04072220040e2022100c0e9040f8030403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 797830620 1250 797829370 797829377
    0x1b0906040b03150c09090c131806050a03030c05010e010614060904111612090b0d050c0c01050103080c151603050405030d06120c05060307200102070b0c0c060106050c03030115 77
    0x20058a035156020b042841071354030035005a581d00d40f560900c010200d002e0400c0720080c8042c0211240e0745101c00710300080e90102d064058005001c0150714000d040c80c0e80c080c82d046060302002109040e40030482c445158000e5000f030060000d00148103003220300e2031259107603418000b0700792a81c502d010030041100c884018000b064005241492160795800b020301000d003040c4001c425020010500307040980700071103040240146241c44410075281c4510100d400c2161b9407840002c02420742e01c0d00b65060003400390020017541d078617841c3c101526071215201001c03520070404044401a880c0301d06c00e03c10028640c4019500040400a50140034064411a1240424414801c4889080c03240e00c00510300c101401240c10002d080c400c52a601382c0d08010700808081080001480d00402503c86042e407011500341c070b0a040c405010300a002d801002440100014140081250800060124810a40292415640d13030700e41c140e41c0c1c2e10480b410702840e504140010041451141c200a40324112800c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 797831870 1250 797830620 797830633
    0x9030d050a02160e040b100303090e070302071a06010305060301060609050603060609030613030f030204060f0c050705041107020f0301060302030d030228020d0e01020606010516080706021b1b0906040b03 89
    0xf0482d81008096000b00c0136240c15802000305002d41e481010707402545100c94084d000f429605d00030b2030302c3c06074000c3c02c0401e4404808035000342c1c4254121200ca41c2c02000700320b000b1f40d11161120010301f098070711500090034130004c14900d00d0180721b4141141c1c03041d214122014a400d06000344c54100070001c2d944681b082c080c002c030b2500d05125803031290345040700d0b03000c15842d02d2502034008aa050b002030109441440705220103034200401d079606c403445003080d100c250560f141081c94400c4640085420900f4801e41c1020081048060007040e803080390300d454040e4518003498201e80c040d10000e503050b408440031800c030a01a40c011700742c52060b07030324981d0a481c003d0914546c04154419000040c3d1096210a40c081c0d88140207041c0e8000910240c9040c1c1402c3c0d000816a02a0b9941c85505403488a484010003040c2401c98011a078401c1065495280034219400e407080b522071380c12001d00507207181e10b9071100b50703004c490f84001e0700074800c1e05e00361070b9841400010801210402e4240c070800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 797833120 1250 797831870 797831893
    0x105160c05100207030303180f0221190212011814030705030714011a101d21071d040b04030516121d03030708032d01031709030d050a02 60
    0x400621482d002950001d0030714a00c2c6180c000c00b110030011401d2280c030740080c49200010800c0c0e1003514144c1c0c04551040e071510054080320110202202801414420f00c0b94902090b00c0409d050582e1a0080724411000038003000e0103800e03107031140e5101e01807503a0b40003401c00017034008841c41200e403170701000c803410910350341d0741e45295611078a003c0e200100c84400e51842400c00740111a102516520300342c10710003114000c00d00d04040003012009010150316080c101d04c6040f13402c1e08100000410300d44840442c1070740b944180203881a406643d0040440c0800d1440703602d203e400240b14030150007115581e03a515480300c03c200c0034204504200c1d041001d041c0d000641c50700c0e004801d01801d00899260540d04c0041d101801e08100030b0802c401e41100f02c8207580e40801603035401c0750000d10313166a0380d64006598084c2c0300c601c442c01a00590241c1e0a03019124211030140c1030b83e101e101241242c05441c25001460300404c40c0055040d40903280c40002d0a00c0355010b031000200302c0c0101c95911016 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 797834370 1250 797833120 797833129
    0x3031605131215020a080a05060102010b1503062106150a0b180306010503151303030b0d0506010f0501052a190b24030d0f02031c0c030501060e0105160c05 68
    0x403076210b0064008480b50820910210743c9104030b090890103021072402c1c00454000c2c081480c01441514141d07601e01c0003071040e900039000070340d00d10310050018002c4d90145a00d51481e410560f2807034000e000200d44401c0549024094841e1080040001c0c840c41d5034401243c84a04003d100e119045200701c1c60004810003990060940c0c80b440001030f109060401051502d800700580c0050f200340e214100c0740904a00082c5d006030006800d400c100101401c0703040c241c025000050311290400c1000340c000c0709014011941e541030341e0000f01d4030014603648000440d401c0c0a80c00031560314140410001229603034424604c0400202007003901c5603902110400c060b413007070a0701c05540c030740b8243d02001800e040304050701d1000f55503040425104104000882c0d502c0d0894a4008140800c0c01d540084450080040c3c0f40803e503240303008410845e003400c040b40608200050000071904000c00403454034020405040140c006030750780f605050b0241e442442c8441854410745d8000440c04000c155900d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 797835620 1250 797834370 797834407
    0x60f061f050d110306100513030f140a03080406050610080a0e0f120a12110301030f030e09100611060402012322050310061a0307051c0608070801090503031605 70
    0x114103411a1245005021b00400d426005881070800104003c04550241c040301e11105507504041e1f288002d001611741444000c1c8d840c0c83d510341c50b00c244103402007003551169046100c1c0384204070a10007070311000c082c009608a42c1000304013089041001401580300b0780d11034080341da0726404484440d010b0040090600b4590200ca42d1540c070b0000c0c03038100f4150410b0703000302402c2e0516810032400c85800d400070000d010602008000440c404450428103105015007864810000c6c204411030411246058800c0300504c500b1012079006180c03501d00d8000403560380d1044c0e806071541d18180c1044114041c241c1e0240c081d10038503900c1403019a40e802c2c10a0b600b06050001c1d11304010719181007400301480c00d42502904030203503080000500c51100d840300348101540c0717000300007078803929410015201d9000720307800fa268440000720240340f945a1a00b064044520310b0080d42d412580341c2c60407030f003642c00034800a4025802000400c04030410b00301150001c2070180b80c030a0030188585601c110b80720 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 797836870 1250 797835620 797835641
    0x1200604120513141914060c0f01050f01030b0708040209070e0406031502070302060615090f01050904020d20250507230103050c09010e10030204080a03050309060f061f050d 76
    0x102d43d04404e1349039003009802821441d8410300320301c01c45407a14000d8030540c0c45011842e802a0004595450800e00402080701281e4180c1c0c024080d500d8022202c5c0d1035200700740300503501e04a9140102e000107004103a400c0c00380e9006402104181c0d204102541c081e83c0d4001d1441e0041e40c1e500b00080400e600110100304010410070160fa154040c2c04c00a00e0060f0160605106519400e207103e01c00b20f51800b1a03025a6050742c040c0ca41011100040e1024014844e80f01c2c0c20500000c0c1404000c03402d6444440d5a84108001c1c48100d071070004002a980600c00105c02584100088a0700402b810b200707004850744182e0850301c0035070f1103800c07130054168075050510b20441c1c0c000c20b50449613014010702da4001c2c100d54240b0304107a04100000d001e0b144601007940552000000250031501c07030340407100904580c0c4204c4111120314030303008115900858076031985004d60000f0401c400c050304840743c011440145042c082d100b80c46914942508000ba010b424010100105015691207010300b6003443d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 797838120 1250 797836870 797836889
    0x4060314010504060b0301030303051b0c1011160605041e05060a05090c09190912050a120504050a020603130c260a05030a120204030209011401200604120513 69
    0xd90103510803403403110103070003052082d400e012040c0007150074101a24112909864085040e0320341000d207650b2244144204080d80c040005c43d01c1420400082c02d041031900350200300480140710800384458000d007510f03480360144000310075000c11066006190045d0049400014400e50f066050b2501c200b00072080f00c0c907421080802c46611b42a12466600803a904094010808100001114642c005281c0050103a91141f4082040d9080d0701540015174402c0e5088020380711010040c16507001200aa40000c150202840c208081405140d001e50b90140c000c10155801358200a219000241a274501c1c0c11131144103070204d00030f0142c8000034003c07490b886a88090403510342c0384022901d211041c943c0c0c00034008038000755000089400200043c03605102000d0800c51240203441141c0c800f039848035041002040510034a1101c0112010980302c00b02c4112021210480e0301000071091034654000d4400180400d05000f410f450a92841c9011071610808803030010108101c1c2d04451503c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 797839370 1250 797838120 797838131
    0x18050103140c1503041a0901060f0b13060507150216020405131a060f0301090503030601031d0a08070206280e01020f06182b091d040620040603 63
    0x41c440c0700341204041c0703440480a400b051a5040200e0308080340300ca00e040f6807030800000501440603981b100070f00b800040b01c60070150304200c00a9406030400d8090305103071081c1d031000001c0c000b01c102d04407070202420078422040b441c9007000035140d61708448010741700240703040b0940a00000c244000d040d9400481c0c16400600c3c00f0780140130445070000c11106840800f01003050104a20580d00002510361981003941542d812001c2681c950150074601c2c2c1540c00c0482036420440048042d510841c070a9074100b01c070081d469400c0c40c290442010312600d60b0012440300011624190041c41c5850020b030515203885c90070304140102d407071915014408140a00c900e8643c0d943e01c48030800c02d10302c00b44000d101c440308210003d51500d1025015910f80240c0909803410b8041c1809442c00a06072030444100c003a010740e80060315498002040780004810000108421560710798146004040d0f041070350590740d0701c2daa144010308217120b1504c100c6d1070a00a04284101d4400100064850344c2d801040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 797840620 1250 797839370 797839373
    0x140a050c280f030b0705030402012c0d06021801080601091401020c150a020d11030405010c06140906010f05180f0405070308131a2107111605011706101818050103 71
    0xc0641e4003400045c01c002d0104184805170783e210100b214800340c542548003144c41000420310255042444054203c0010703440740c014480c0d654080d10380302c60310b00040e81588098000445040030201c4069000c600009014440c1c030046850040400d00180115290f0b04071440c00501d020751200100f10228000044400387c00c0e505118180b4030360594200f0289090505003007984901075030040304d04115003620b1f5241409001e804c0845030140c820310b44446400d11020103030300c6103024000c0e41c450380c40f500307000200c50910700c4003007005042c40c0d03d140300079840f0029510030b00e01002c2c02c10746080c4a102000710208070300c24020005903007241c03480d42302c840c9442070500030815003a0070382000220602c4a0f0b00d03000c803505290000b00300010000c0c070040c0d451130b0060306c141e440f642440c0054480d001c402d00c5045c0740d444006050341c0d4240c0380d000c0030540c8c017002200e1380a81240d982e90041000b88031214120b0148000303510400311032254401c442e480340440d21218403140700c1c202d9004c0e00e5000400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 797841726 1106 797840620 797840633
    0x5120307080c0703020108011205030403020d05031c05060f01030b090705130801060609062a080904060e0a0207061409060c090402190804140a050c280f03 68
    0x42d142d080c241e01c1a42e40b8402800200c0c04180d02c0c00000c18090250310038801100c1e407002c002d52801382141d0901c4088a542401102ca6103c01d20104d060000000d02d00c1110440f030000000d558034101c41003186200748129490b042c10302d0b080044202e83c54030600f403503106005007081982c03000409069055641c0940c403030b6000b9443d0002c04991a98814406003c8907a5551800c880d1b510030303001c1110005c17840080d209903402e00341802000a070308801130070700c04400a00000f04190342d51421b040041c4100d4200280035800942c0780304018091003041800401d00c00c0b40901460000c0c01c0a5498002400c80c400400d00401c1d800041d590b05d40469500000d00100440300d544100c102600d1040165422070b2001c9842c0402903e1020000e0258403a94009006204000c1c1e00402e200c002e1440e0002d0742400c24803842200c4e009072503000124014030620140058061039401c144 = true := by decide +kernel

theorem cover : BRFrame.Cov 797661870 797841726 := by
  have h0 := BRFrame.cov_init 797661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 797661870 ≤ n) (h2 : n < 797841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
