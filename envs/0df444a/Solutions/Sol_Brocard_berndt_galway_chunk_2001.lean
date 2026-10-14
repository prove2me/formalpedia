-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2001
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:16.88422+00:00
-- url     : https://prove2.me/submissions/25f9e390-9376-415e-ae0e-8c7dd016cd02

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 359712230 ≤ n < 359892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 359713480 1250 359712230 359712239
    0x5031f060305010c170f0105090a02090d05071d010e040c0b0901050d0c090609080f030a05210f06011d0a0306020a181205010e07030b19140403020a0308091f0e0304 72
    0x1c1c0113454460015807180d240d090910810190562001000c40d02c01075a01703801408640d40b95407483e03412103800e59000d40c403616504002582041d940000070440e1148000004034a0440001c0042c1c0c40002c2d081464143c0ea18044105403400885e401407440260503c02e0100080c0c0c8800341498003010324000d414910340500d000122200c02c0e82c0c0d4004645035145c02c00285078400c0014014000b004081c1160140e0082d40c0c2c4c0e606c0c0245c1c074400c024040040369010305055803945505840020011078103541c104400100d8a2540a640300360010b0a9820504945071b00d03070b41078003011400500700682042c40e580b070701002034001803e4481041403440c0b00341c1c0c80400a44205024028900d440001d8401038508a800c40380002c404d56200e8002c0c080400100700f0360840203600060392520080e60010b6200500001c1440010009001400c6000c0c0001e140c0d0000e0383d000c8062081e10f03040100c0d10f50303120813070b80c40411015029609102c1d0307101900c82d17040398001142c02c400e0002201d003020340f035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 359714730 1250 359713480 359713483
    0x3130302220920060a05090409030509060415020c060a0e0d140106080102090406050a060f0c020a031203140105120c12101806050a0213030204390e0a05031f060305 72
    0x40041c156841800f6114880c1c248050140c400c1009400711110b92800c0f410000140041c0501c4028900c61956001503005046c050710440352a0035008080e00d40e20764841d0007038210b040f0300381d01c1f2100600c07c509040f649824aa8121164600342da12000501140b0804006070319005e20300485094030046511008201e0902884020f00421800540c684902e174052004841060380064402c140d80401000007d400c1907c51030b802e01d0620f0201d15003c06800404c5542e000ca610081c02d801d0122500c803c1d440c0d0690080d01284904408104243d82c0c5204102c022114510340084507005074600c030303110745014a4000c882504003400c2c0c440207000d031050b0000300c82c02101c00b03408031580010540100111489004c0e800382c42d0810440c100b0108209a6605045d04c4c04000d0082d582c5918045164802404413164a44141d03141d43d64000c905000c0220300c8132504106c00803401266a44901d4a091703446034017030718400b4004222040c500c2e6400d121141d070002c408a50b4507550440030007c0b920 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 359715980 1250 359714730 359714741
    0xb0d09020307120b0c12061005070803010308030f150609210601080307030f020105090d030c03021c020c100b0915010903080d1a19030b060303040509010e060406080313030222 77
    0x840303a100780d280f0706280c01c12940300313040180340c0901c030743d004c0198882e82c170801075074150480020761305505401c500300340644040c801d011015100503800b100010400c0070b071030000d511980035481461182d40382c686c0780b01c02c03c0b178081e04c02d143c2c0b000b02481211140c2c2840a0f9400b411900305030070002c80800b000d48181014400c0e0480180394100142c100700b40754120042d07010107400381c402086103141c9141c40980b07940300612410105070701c4080309003d862081d0140c801100c20590601191140d03000808020f52240200c0c0c259030083c1d0100d02c8502c3c4591144100c00719010b405038050740d42e40d196102410511400c0e490601005902c040301090400019000742d028400e0002024665441850504110a0704182c411300d0030000043c200320080c1d40303513811030743e20400140c2d0301c0e2030f06000a801d5014640060f500075141100018114149040b038502071071050301e0801c9402d480307291941e1240302d0050210000001d030f580810040c18840280a40d60f02c141001e100300540c0710410300c00b5200b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 359717230 1250 359715980 359715989
    0x604090504230307050d1808011514010c053f2d0d0f0e0a0812070e01140304150c1e0f0c080f0c01090c0f05010305040b010b0d09020307 60
    0x10702c4140d44500c141c03602c00000c1692000c2c4021400d11180e6612a9a610a00c40382d0408200c2400408282c5207107400c425005403010380000d03c0321240908502d03079408494860b40086941110005116502846002c0303040c13034004020b0005014071091401002c1c2c0c5040180300c0c084801200c40001440f0250300001c10b44460310710590b02c0141010350200c0341c0e0302906c1144140c480780d115115000d5070104445400210800101e1050042c50f282d8009085403201c0c03c1480c020380340d17440c2c1007002c1c1000904401201e01c007801d001d5101c5890403608950b0000c1e64901007281041c490555a03440000b4507400340c81821500c0350f451154180005561207011000c020072003e041a00d02c2400d200c0c0046050201c0785000701110a00e518000c005110075000545014000500385550b1401082260b4610031010300038031242125284c2540c0103880340c070a064910300740c900003203407641c440d0013041d00403608400c0c0441241d007001e0051241340d208490002c0015a1428140c0c010385040c04400d0061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 359718480 1250 359717230 359717243
    0x12060609230d1b0503192a181a01020705061c020a030504050105060d0210050a35010905040f1e1515060302391f0e0c0a060e0604090504 60
    0x800c09841d88001050542010f80b1071b40040d90032601c141294188495069082031845a200c14644841500036071400c1c0c50080105500d0404600039201804e80342011110110800c000c541c030076001c1c041c4070021b0380d2550040e0003a1200704841d02e418009041c81c0041c161012a540c10400c1503041280e01641104002c44e03220010001800028819194001c0040e19040c00c030020301c0d400212401600345102050080200d046d8441d00e00c41c03d17001e21803030131640184903100d02402058808006281c40203c000c2c803000c001048084d03580c0100780c0240c1d4002145a040161070366080e4020003c3c0a80c20044ea10544c0c1e040041030782c2000401c80200001000618210b10403100e11030b6450b950008814580100603205070214503040000100701000c20f02691480101047d0001241001088050784a02d8106111f002c6070034800945440c079418040150804500241d920344080c05005036100d40c9a01c0108080d07405076001503074140009010f207140c591980c401c102100c0054400b5501c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 359719730 1250 359718480 359718503
    0x1e071d0601050f0307120b0f0307090e01060e091b01110307020402030403030f0f0c03060f051f0203091f0305010e01080d0e01020f0d030203010f0e04020a150c02120d12060609230d 79
    0x251b21443c42890a00e4109541d40034a021290001c81c0c1e03201c25034858240d05554170503c10026003800e5000784003134640000c81d10028200690320a43c0c4d036451403240c808101118031041520b42c013501c0b02e811400c403c80050f41c1044a190200030083d00004c109034249500c5469a0101c800107205010403030080e40f000046241413900024101c3c0d540c2c0d0001036981c0007d107000e10a40d9030310100c1070421002d07241c842c82c8100c100c2c0c034224218060001c03002d40065a2240c240c08002a60321300c21101d007416034007002146c0c3d0307591a00b0039000083c892150150080411070000510640103158540c02c10b0040328140c00004a40e640360000f0f140c0f2560020354084010301802c16030203068130061290b0003000318907003000d400142030b1100b00c1c07041202804c1425180344580f0701a011340c550160700105840ca41030309500d400b0381c442e050760200d10000380083d5081d501380c28107446080706031001950303071801c003505200a201001c0502d004080c0b1813544064400410f5990400307003440c5070b21490240c0030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 359720980 1250 359719730 359719757
    0x130e090f150c040302061309050c220308030705160c0f170d0e10022806051609060c0201090306050903040503060907060206060d231e071d0601050f0307 67
    0x5120381c00030381d5a65551540103108040b80088250303030949804403200d65071405001030108103c0c40c20351003108054201820080016180301c046c20b18803010154109020250b401c1c80410746c002c60000404c108420300104480605c6000513003d1405441e124000c0c0c4104c0703403030b1000446102d90001c041d0301c02046042c00692601000e510ba101d412000134003803c843d103c005004000c0e40541c0d940100f00c030718a9503203010300c01c012110010201040c03056140e448502090a1000b05a20503220f181c1810301082c0030040002c3c10300c1508003079540380d05c0e0203410b080301180d00d14080e41707040e4108039162030080f000c90501c0c45454001c4414000a5584620704400d140c10100010000d0039550491034041001940200b80755610280440b03078000700d1700031131610200882c43c6021392082c8200c03000030351214420000d0402c46540714031801703482422a9480490f0340310760a00660400b030b03442c11410903142c8200416581c1003c014108142451218803030200150021039600c40042d805000204 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 359722230 1250 359720980 359720983
    0xb0f040e0f0d0e0a0303081e04120813020d080d0204030b0c130b0a120b130f05060a12050a06020f0903100510050409030512090705040e06040213140408130e090f 71
    0x800902d180d0900b125421036000014035840110320018040c4012100010f41c04144050041c1d00785855508807111030405003405412a00d070b54451a0200b81ca801c0030810300e9481e0b4202d18182c6600a0861107000c20700d40d16590a41c11040e086003042380c0a100100000742c014040b681716040d203034405601c0b0285000c04007100360141c3c0c00340c42c512608008420406500c8800398507418400307000425102491004503444e0781d0003040140d86546072240d0380c940195250032840c05800c003121107101d8207880318601403144005d00d8009103258884008a000101c60303802818802c640c0540003410300e0000002709041051103900700440c1344d951010020780d0184801c507000600425101041b40311103aa4002d0114800d0110125041c500031703000690801c820000c48001d00006003041c00402c44c1c680e0341c0340d035449003070703804900ca0300c422005a00c0000035440395801c84052002c0301c0769542c0300c1d901e40f4081740c2c4c0490000b01010640355000f082c4500d0801c03c85004450031070080600850504119 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 359723480 1250 359722230 359722243
    0x30c0606171504020a05120a050c030d0512090304030c0f080106090c080727180609020a0e0622170607022e0f0e0d090e040503030106030b0f040e0f 65
    0x10904644807104030840080005500d90441d9090001425940710f0f4000620040c02c10340c04a640703d94032580311422543c001c99503000680c80b400c112440c82c2000d10800d900c0e4001c1805990020b5824005036418010880c1d0a41d0806a43d0341900e203407549a845214868000c4e40044400d900a80320030080d81800344274030030007000241401c00c5501c60007000242042d4014000d072007001000c10840b60b0540e10f00c44101010301880b501b0440d41907440203c10700001900505075801c2d450107c0002c0e04500238003c840314501c20380d0b298454041c001041001d1508101104114000c030b03071264032841c1600402c6034000d000f0407145101204494045507181003002023045017190804044540e0b05400c0100760b40c03480304082c07540c240d101092140740e0000d0910003002c402450514066529441002c98401101007140d5a08451191902820000c0070b00a071070052180c1e0041004001040c4660300141d15540002c045201050b80d101c00102030b64101c4c141040c9039040060609800758042002c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 359724730 1250 359723480 359723489
    0x2030607141b031b0601091a10080c0415020604020f011e030e01090602030a0522080313020a0306020d1a040e03090f0612100f0b040b3103030c0606 65
    0xc8034010800745240c00601810070303540403084101c03032040461803092054070740d01459424820501240024103036502c030401e1142404080c41d07d01c40e031024800a0f40b030744a00e043c0c050f00684c400007040e0380444140c0c00052514403205d41c24000400e246400080300c05402003198010484c50401c1d004100d14260200c440d5810b0149181e810380e5607280c51004800500030508000031541240c2c00b40074050034400302e00410b824800410016201655408a0301034000a240707944203400d4a035040e440c1c0c0d000020040c09079102400003401000300079086085c001d01c00340c441803075156280d85101c00d82c0c10000e4088800307519440c00b40030780c540f10301c010040b5002c00c03101031141400d40828162244110074a03c0d000e1511605808072079207603041180c24218940307000c3c0680e460600c2c10b022030304a840c05507403060b0004401c0001d00503159401d0350280e8200403201850484d4101c180422280010040103a0003010385042c103c0c031582c003d080c00114044d498034442481c0750700d031a40440303406800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 359725980 1250 359724730 359724737
    0xd080703020c0c010c0312060305030c0601090e19020613060809060a0b1c060902030304060801091a1507020123180a03050624040f020705150402090c25030c02030607 73
    0x90b0950203030005040c03c2407082800d01c2c0c0c030000362604044881c19200d00702c3c01d1003207040440000801000000034028401810182d4400d81d0f00d846a09040e564911204003155201d0b65100d640c4101e4440c1402c2c1451001306050710f441c0402c04441e0161040b5808680070440100c20000455418020541d1010341c2607010400e54902c1c0c030000743e2111038440707815441944030f08140c0c00c01c003030341c3c0c405103c26400404494640c0e5842c100200075a100b4041d00301401d092040c8003100011260325071454110040c040d01c84d042041495080075001404107130f0402c0070841e440c00350034207080010610405280c040c42e0782c1d4107000d80a20302c20f40707680b0111402004400c00406c00724801042c0d0b1034001640191225111942201c4c80c0030a09809007c0c5038400e140c0f483d41c0500100303690090040740e20900c1035a132440007081030724150074000c80d000703504101c00b0b80000e540095084003c2034800c40c114082003407540d40c4451031041c41c40e03c80084004c500300640d0401580340c10030526601c0b420030b25 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 359727230 1250 359725980 359725987
    0x506010f0c03050a0f020c180402190e0c03060103140103061b02030c030d0513080a080105040b03010c02060601030b030f0105010b0703110f0304050418020301020310090c052701110607020d08070302 87
    0x390010403610944a40804203c844d00c02840c1c1e10344207104121f510b079402030807209074201c446402201500150b40403407107000c0c00c10b4403028074001654014111011050320b01c0c0c941e42c4404039111141e01c0201401d04056a81e803c200a4114608006020b10302480c000160140190011404456102580411741d80103010740d0b0481c031000000c80315a01c2403000046030030340b214040703039014600a040040903150f01140c0090300c40d60101c1b4060485008403428043c5661043c1450b08840c6c01d85c4656005070003141c0061500e50085c4c000710300070f407000740485007c0015042c02d10708580080e040b6544c1e00100081203070074581d00c910203e0a00c14000c1c09800d240e95102e05003a603030703c55441885e02441d02c0791000c0f035000d040019400007032500075000307556900e441407003040d80c4180d45c02082c50061410029100c024407840594480c40e141040e2804804121007002c4446105030b10300c20b040000d9010180410f210a11010b07000f031181740c000744030b00100000040e0800f04020140801c151060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 359728480 1250 359727230 359727233
    0xb221409011418031303060b0316121b050301060e0f060604120308090307080a111c05070209060607050706021b030d0e040203100b1308010f060f0e0a1e0506010f0c 72
    0x41c10142d00042c2c140804074095050030f80c0c0710305601032043d04880242c0d1402c00041030040c030b50007503800d944c0300720150f030210454458600390000720781c0603501924511180c04000030342e0030900c2e046071014031800e00c0c1c1c140c0c1d0340d40002420f40f14250009558a01280107010100c45d02850150f0882c0c01107906604007400c040403481420030700200a420401c00e1404951041c00600c111400c5070707042080c450741c4609512000e4040400e42024007640d11820070740500c0c1642d001d1f001110803880340e881d1403a2900d146c081000400000e0702040d403108081192000180d0200105001010305801410500d0080c1660700805004144668040c3d0490500d0054507070f4480100703c07110f50b040f20010303181c2c1c80e4038513000070811a81d00031201b81c02001581e00128507120390b02c603045840100092118804158031139096a40b030f445203607088204d038041031181c213131603c039035a80c00a100540007c0e449404045520080d0400100d40e41d0541d456041c050103507441440080844c689041c90010f00d6290b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 359729730 1250 359728480 359728511
    0x15090e0f09061303210c0f02010e060105040f0f020a0309021207050303040603091e140f011802010c1b0f050906010e010f030b0f1302131203120b22140901 68
    0x80400c1018a02c07448110201170161110081e010384104894242d030800c00c044600500058258401081688402d80440361050286180006101020740600d92901051001501c40d010101200545820307160303402221602c040d00045410703a401003a2040720340180315620603d000c8400b101e4101001c1400f05032000400c0b01e00311402171070b0000ea0040a801c250880c0e00c14032540540301d414010b01c0b0000d210007208481c08421492042c2c0f52200140f040d0242240e080101e80039504240306901c0c40550300480300c0c3d0500703900031541e40103100c1c1080701c41c000c40d00300c54200c1c21403641e000000b0300c05403c00e1030310350386e00100030700b040b11111003154006000815100340e00c00415890782c003d150b031521131300d81844041d80041c0556840c041c140c8c07a404086d4001083d03648110342480400034144c0f6000c5c00001c1c074550951540d00012142c500d03507130041c01c039007000160070101c00c5c0140c440c1c440156100211414058200084d4810504c1b070b4403044034000380c20380350240e0400240e0b0445810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 359730980 1250 359729730 359729743
    0x150909110406051f0c020d1a01080d030e07140a0308030106020a1a0103050a0f1112010f0c0e01050307030f110712030c141204020301060306090b0f0c04060f110715090e0f09 76
    0x42824003c0e070301a486e04c0081c2004c15810801070110740b00b584581108070030750a0040c165a4020706840320201d0410046003100ca9110203050703a85d1003c41c00700300e2607501104408494601910b00044603480c0c0e202e03080c50743d0084c1c0c070480042e403000030f014041c0202141c80764038a42482002c040a0352544d1a450f40c1c40c0c008000c080c200782e0529031180100010011414074001d4003501c805d0035294071315030040c001c111680100807001e0809034600c06030343c0300f542c8100005205031600d9046072607141c02100181101d10304440d4096070740340009000803580e405410058459004000b40c50319000009040e00c031038080403800d001c80034403020443d404038410740c0c500540804d9080c0b1541c1d21400041d01510640c1c1c4090f0005150821000074405ca0700c821a11603048150048115190b8042210b0180b249104003000220440921004a0700c03a18540440d203205204650040e0744034600d4004042c02c001c14074000ca00344260422038048480c500a500c203000c001c8003032141c503000d00e44c80e4540a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 359732230 1250 359730980 359731039
    0x609030c05040e100501080703030e040203010f2715081c050d0b010c020409030329090402060313140d02010b032b020a1407061d010f0315090911040605 67
    0xc0d2644800311902104200804201307080100502181d69038000042d02e4202900050f030000e6034002548110f41001d00071a03040f00d031420741c000c5500d0b2420b0900300b0500c0c0d080b10303c58aa1600c1481d40c110740b00c4507000e428008081c040e2515001440c1007412850181e416050000c0a04405a99a03030030ba0000241d036080800c01c00007007070980c1d100004840c800c5a006000b9800391501142c07000340355240d4429030201740c007800d8521000c0c881202d42034100001403041d9500080c44c00028006051000166401c03c10000c81450301980c2651140821240c070400740312030b60700c044006000c40b54240100103c020f400c0d0f0250910055810100f040b40f03040d1010254100d00c07900007074001d40d2007005128aa540c010261a0b2040c3d0024642c0703440c0c564038440c050010b8440c03003030541d082c2ca18001d2b103010424161220b241300b220140003500070788040c01000507010700e030740d80c00940c5003001d005100e20107106110760400c005039501007001321002508103500602c0040300c0034070000d034031400028510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 359733480 1250 359732230 359732239
    0x2031504180314040e0a0203070905031501030611040803120402030613050c060703180303170f190b27090f06100303030b0409020a0308070c0515040b0309280c0609030c05 75
    0x34410140e480491081d1742c007032416600c4c54800c10a00c502c11b41d0103103005a20950b035094006607220308040d40c424510311042c01900c44a0f00400010b203680d0b00c1070030202e8807580800e0070980c0d24940c0504680200b181018144400d0b4100700c214a018007440d40d0004840281c100c1c1d10b4140d89030306903600003420520f400703500c00280003400d02d40600c1d100458054410002044181c603881c000f0701401c40b181c00c4584c8464010081040b0041e041d0724103204d000400401102c000c01414403202500010103030541100805464540c0c3d08207201802c560401c121101341e40031300f0982221450300004500f110104d820010621003820014140002140c2c1c06140100d055074012002030700034400b48034000c2d400654848000f080000d00009000440c3c001c002522241c2d9603001030101e2100c4c00603851182440801040c000ba42d9103801840c0c2207e8420708a8002c40b6611203941d01050310449804402c80c150301488040008560740d0f80054040b503d040c8091924582d14a50988949e01645108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 359734730 1250 359733480 359733497
    0x11b0c0c0f0602121b060403121a150702040609051f082113270c0e0307090c090506370806091306060e01090b030309030309090c040b0d020315041803 66
    0x2503068001103013208104501c04d541b0541054038001e815201d040070303a00f0301c0320305013082142444c0e81702158012050014101d0f23600c0c007075083c1c2914450791000320100d0380a41c0e12640070070b16210b2031161612840d03011440f83d03c0c0100c51364100780040724942c4003d90300e038840c1c0120310f41c0f180340b0b03d440010821007000090300e81745044400b0095044c150002e070f004040e441c0e2400c10030194071551541060520310204100301d8451001ca07001000340d64141e80640c8170b00c1003000050030340c1d8001e03403030082c0900c1c0008010341ca0f4400184154020540c51824603400300c2d440301c040c0c4008601c1410a0700100000e074054624100241241000410040c07042c07800c6070020700084518039030707008866805602040850380342c200c00050445d00380141c1e00340501c3c001d0303030100c035080000031900c02c100010021401e080302081000707111500100000c03580c44060100103004be0150020301500d43c04008050b86a107003101c5407640c030f00011403110b80329505002c000b50551300348100a0082c6070701361801000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 359735980 1250 359734730 359734747
    0x2090603030d1a040501081504170f070503070c080303071b0f05030c062a0d050c07140303010806240d020613030605060f0102030f1b011b0c0c0f060212 67
    0x7075006550309a04681d0a0070710716051802c21a00358a0294012602001070b030f41c035019403541e0f40c00c54200e820340401506002c030340800c080380c058512074218100410b01d000c003011141000d82d00002e80032030700c550000c20410704020781082548003800290000f1030452030a4107005024007061481c0c0318070141401c1b041410f100c00340400b4420241c000741101c2e600c00c10f84015513641c08048900303102054481c1080340d1007021008511001c0004410313124185041c12210900401001c0e1101e0a800005c20141c400540080d00014028544001071030b01d0390302d0090028248900144091303a02c001104845442500c024108204803409036410b0012907107074030110300030307104500d10030310951240e034030010410800d500041c0c807490702503811524050740c0c48016aa00d001d0750b40380e080d00311000c1c002426001001034410b042009844d0001c40d010006a01c400c80e03164030b0481c1107002035944022982440680c040c4c00d4024044480c4d03228440d45091802500c3e584564852400d6400c001038441 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 359737230 1250 359735980 359735983
    0x10c0807020a270e030c03070305090a0e0f010306181a0712050903090112180b130206040b0c0d1403070f0309140105060306091605090c0d1518050408040302090603 72
    0x80140c001000c00050396036450180d40301070107801000425160400001c03441001c2c010051b2515071741c10100647c10104540d4080d00d0b46c1e001003030216000623080400050601c6075444680c007840042201580350350540c01c1c188107542c0d00090203c801d0123051845400a0300503030b90031002c81c40103000440d1540394100b04880a801120320510354908100c02d0242030100030004101c10303902600c5505d5103510400301c54081e90134a10402075401070000005011808050b91160b0080d81807a1001055140d54001140d90f002600318612424001c1840c3d81c40c9041008415190301c014149600845942420115541f00007801ca0040005a500c0e10074210f00079000b1108450307020011000b10301070031484a0007004101c031000d200c2d105400c0414a030540110751841900a080c1c142c0901e1800c1c1070070300c940d80030081c100c1c40c1ca4450402417010f42000358802c00194450800c071040800d46070142d00e00d407145c0201f5219005607e80418040017901e904100d408403075064450780307031b6541c1c0d960009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 359738480 1250 359737230 359737249
    0x1905060714160303022808030a020f040905070302030103060b1807051b011a04060e01210218070c0c08070807180e120409060b0705150a06261209010c080702 69
    0x2803541072401c100110030140c006c5000c2051780b6558902a500c61844038400403005250280684144010004184549016001807030482c6801c41d003140381c80d40e111a4042101d200315140c100082d4040010304c1000480d0082d845c0310402282e0184210303c4040c2107419017000540814240074001a0090003100a54600055696080000c0101a904c1203011603452500800148100e14001c00440ca000a9104140c162410f660050040221001140e0b0104a6001c0183c0e400184807010303145d06124010b4861054071103540349105804180340c508000c035007682003a03c481e0460201803111401c009086c00403110102d0424081c90b000c030400f0340040c01121800c030018000d40300610b08240c040b60091088640414007041880d9445203c100180502d143c0203003990044602c848400f0380300c060301c07a00b001c11120001020b40d5103100c080e150380040504184a82c20030351401e0001032061200c01f5040000c080c19034074052215000a00c500c50340d4000602d400c030302003000e4055403180700c01f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 359739730 1250 359738480 359738503
    0xa0e040902011103131505040b0d050403090b071208010e060d020d0809090c0a020601120206090118090f1e050f0601082a071101090305100e010902060a0e1905060714 73
    0xd0341d03569951241c481740025841e0003104c050022034420101400d00c20012181129041038207182403400c910081c5e4050030307002d00150100010800c1c08116000d06078003c24003584290501007502c13041c6500540140e105900048284090104008003511030102c482043c55045807480303181c880607d42640a0b019100000350400c07001c80401052502400050503410303c942c00700c2d00103a90300e0b202085d107802c1109000350080b2050040009950085c5140d48802101c1d410b030b00c10450b12a09004200c801828507150a40c0e2142442d0036286444c50341c400b0401d01003002807140380350140526030310b8403024002c1410000d1030400148948018603202c1505030300407640404d00c40003140c10340c083e40c001250039905d0300c030508030004042d0700818452046a0340720024012040749082d00100400710009440850f5407202e2540c40184e6655000b441c10492940b1100408600281403103035081200356400c006034501078040c0900d658007000d6404040d40300c2c2d00e005030400c144a8640c1411100d482d0b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 359740980 1250 359739730 359739733
    0x60b03130c0918050601080f1c050d0e101d06061512011d01050d1101030e07091e05011a0f16050d020f060c0405010c11030106030c061707050a0e0409020111 69
    0x1000d540c190f00c02404410a10f001c0d80031501941d03200c40c03030702d6101c1364408031400140e4060610b2200d030b00e2800703030750960f0b8945c00c4c00c0c00c3d410201952142010b80301260000842078104400c14449000f46d841001c46c98131803100750f00790350000c550240d40d940c1c5010f03000d0b0744076512181c000b0301040300040446040e040a0100010f681d40c0d1090100d60002c85298040c1c0541910070011409090640b04034800982100321450180c1c01c650040d1300801c0728941d201c3d1309015859001c0f4205a00c0d000b412a10244040d02d0b400d10700b0000c0c218011954103030001d00000d5035010780401154640d40075102c0d980b9070900740b03a607924131203080c4184812540400402034000c906100d001550046100340300c442c404003e0720b4641c0c0d1810f42d03601c0107100718007071503000c11440b184040100f50700322200d006541c4083e0001801c00c2c1c50741c031018001c0b1015030103600010340070702c1010b0303035040c640e61041e03004001c3e070030300c00d00317003c0407034005130031581003a2020740210782e02c203d00e03015a0310400d0482001c2c080d080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 359742230 1250 359740980 359740991
    0x60406030f05060604061403060f180d0806030601090b0303033105060402191a0904020706020427020306011d03010b040203010603020702030616051909082e060b03130c09 75
    0x90b100752103800484200b4452440d150b000070320032540c4500c0810481c030080241065903110f601c1c903102803034050510000380900280f8114403040401003030780e0f400c035a51107a0040c4d1401204140c6080c0c0160040c1d90403038101070402c0c0c030503200042500c2d00b050045c0c0001010201c28801c0c01c8a581842036288403c40135101d486041c440c01003581d80c040c5000317803110101000050120940c0340100c2c49025140740b4140c106280d088428400303002035070002080580381c00d1581e100c603410703a00300790450000d0b541c0400c40380203040d09101031036208002010040d415850282c1c0042d00d5400140f0302d09026113000d000907580b0303580a61000b20501d000420454032943c56050040c025005600128040d1044102040c910882000c10405000042d078400f072a02e182001c500340303204440380e141424000b84040206420009101d2100124010001c000010450011154a98914020307810200b8075043c401d0045030502c0080740c0d0702018125100c00c0c010b140c0d241100300b83c8019484656500e1401c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 359743480 1250 359742230 359742233
    0xc010e031b01050a0902060d0c021f0b01020f0f03090103022a160b18100c24052203050a0e0307180e060702030304110f030f010c020607180e060406030f 67
    0x940d01c8000071801030300204200c3d902c030580041100c900c0704e030196015006011480007807003d500b203103004058a10540355086010322484030914001c1c1502e420030741e100d00d146141c42d68100136030700300d600d24600100801200c0701c80c655101c1c421001450304054001801070a051081002c294160160258440141d100d146841d80c07180041e6841c1401400c0b030440c0080d540c0c403a1015541004140d983d8040d090a01004205002c044010352070300748080040ba07034003c00ca41080070281f0f501c01d80d00d00810803032001005801c6920081c84402d42d010301c4500401c8207403001325189903c1d030381410034a0751690034072811741704248000003040e450b100320040454120000400107090810800092004030408404152500e03400c981c540e00690040c80010080303003040304484c1071048090000312500c07540d040464107055109103034a1803a91207031b0b05900640c1e410462540e1000d4a450140007204461445801c1c01845128620306000c0590104105548a078451401075034090100f00081c12103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 359744730 1250 359743480 359743507
    0x604080304260706051602120904091419060b1008130302010e01061e08070608040f0f0b010915140105070f081911060702010b0f10031b03090611040b040b0c010e03 72
    0x407940f001114030b00600d110f40c01c90000a201030081255070b41d0314227200c402024030000f00450401a21420001c0144a90150007407015223088032011005c0c0040e0407003418910140c410141c2101d005d40042034031045815030050318280c20903061a11545aa01c1c0c034101280940441400101694030300744c40054401d440f03040b450702d10341c0100c1c0048a03442d96030007803680350055442111702040c9254009000140036101443c44079104500301e442045250301c4140f0801c5098001220f00d694a00440c1c020408000010b030013084c1c2036031383d600d40d0b101904c002001405180e0008010b43c943c008000100075007002034038680700c1796460604401c4040d10700140740c180c0c0002041c190f4040c60001c0f501007072040c05400b50891024140c0200348000c0f20034030640011456080080558a04503551520000d0f040460100300594012440d01820304004d011111815889040c00e4003c200c1048802d40800680d4100c0d103030f00c0d140d6601c0342c030001015409043e2012803220640000241c01001550 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 359745980 1250 359744730 359744741
    0x21e0a05061003050d08041704060e122a0604080a050c10020706080601050d0b090406020c07060801050904260a081009050709030809032406120604080304260706 71
    0x1441100e4103602e480e6030720b04504440740400303400c2e900440d084100140c052094507821500c00c04100306442d0002020321007035081904100300040d03009000e80d4640c684144045149250400600602070107401410809040d00d020b241910345503881d505078039500c8009079001801e40740141c5800603418584a62145880030726644070768040e1458891152000900c41d0544a031500d038502e03691541360041d9482d400c254100b10045031190b083c0b1901c0e84401e82d2541c06188240c00250700c0380d04201901d8200510751700b008003044040801004155101460f45030030035040026448a03081040c7c58580504070a1621207400200103a01d8030910386c0640c86900c540804001104410b464410726400e40704c0076100d05000a42e0034034140b000c0740580c2c0081012200050882e0741c4c2c0041400050003104c40c480080d0410360407501081b18904083e40718020194004010f0031740c2c1e00d0140d480341c000f80001f0b040a0820304400c4c0c039a00c4501d1048807810380ca021160150740c0c840c5203e00d0448051705 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 359747230 1250 359745980 359745983
    0x50f01111c08090607140d110a0905010201060909050705060f09150304050d0c080a030c030e0d0309050d080f0a0504060b061207021c050730050403060b0603100e07021e0a 75
    0xd242c00006034140502240641c041c02c1d5694a004100300c414005a0083d0084015440c1c01980d884038010031401c000b00900b900461900c1e1203160394178020000e42120070944c40040c0c6242001001000903e010401d5020341e41e0499001c1e40f078501854032500b15000710400c4a42050b171a00420040829920141d441180b14101f1180101d00c0b401c001c8507039403d202002000040c0a105400380300d8020f402c410040c1c0121302d0001041e011403804186007040d00400c101c01309075120581001c0c8603003404031103400a1503040c001000e04001c00c1c1411888401020740811070781e00e0000c05c0c200700031038212480c0341c4c0c8010250398541140c20000e4a0022040c3d6810015101d2181c3c444504034050040e4440c1d100c464071342504001c101c2d21800341c40008007a6610010080070041e07000300f01d00080741500085150f0b90180c07950f0651400c40103e07640f500480d441a1010700c10880b5213a000100d001c01d6030b0034000c50216603180d0502c01d80c5011520b000700006d1a40000350700c600e0803000a810454039 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 359748480 1250 359747230 359747237
    0x100503070305030d0e0a0236190e010203010b040b07080d050103030509091b030c1308120703110303060d060b0102010209150a0f050306060406080405070312020105061e0901050f01111c 81
    0x1900d40385c0c86583c3c07601654002500030050156a10511310341c5001c030700c400d0414203140c1120040c04080b40c4d013804012a941031040215442c0c250745006039200e0300c520705d03144c2c1c0c0013140365505019548045004034403e4601701080011031808010b6007509a80070f81e00b100e0710601c41c1e56120f01c1c02a0150b002581c01d103004486810001d00012510004010400c6415500f1881c648944000d00030036841541000100700990400244411003080629a10500d10394201e1300c818261078001c0c80d010114030000f04961040c030a001c06580d5082c40048843e41c840000114624160010703030180c0104202240e1252124960683e0b04d50280b00074110541f46a48101d0002602d10f02074405000941c0c02c030b9000031040c001800054001c42d10190440d0041c4200ea528550f26922134118480c0d01ca54003006075100c40a00c502824070340c124045991038210310b0040340004401044904d481442020b102c2c4d00c02c03100b420131a900485041e8144a155800d88200c0582c0300111040703c1d500401c80d0000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 359749730 1250 359748480 359748491
    0x182d04150c090b03090f0703050f010c0f1b1a0a09020102122d040b0304030c05070509070c200607050609070608040203060708040320160602031809100503070305030d 73
    0x1003060358401e00c000c084035500d5601c4002d0400c1d02040d0710340c10041c40c140c014824030503403449032107080086400540c840d02c010100e002c2c20340340e442d0a54410300c100c00c060010300d480f54040203400000050603025070303455402c41c0c090f40381441c03c00314920704103c1d0b000340c0e0030000703000c050511038110381800c40c000e03022501250010005107115115210940c1d103c0d40c071525840d42502410041e100c81404614501d03030a00b03481d1142c6100650060f03c0840c0482e041c556507400708401404034600800080310300320880c0c42c0808020344490304140c170042141c0880103440e01e8036042004514122407004d03100a131120554030380582e0740c11040e501c2c2040c0d41b151060004590344070300f442c5d911403640540507001503100c8210544a260000d0421402d20401030000302c0740c228603120303d1501c1c1d0008802045501039080f050315031042d0a4108104540080286028001c161299030b201e2640136500705016a6030300d88120300185264200750760600507810000107203c0004041c0c0140040c04904208 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 359750980 1250 359749730 359749763
    0xf03060611030a120603050706050712050a0f030e0a05060106020106171b09070903150203072033070302040609080705010c0f060b0d06020d0b0a05182d04 68
    0x900e4081100a2003041d0310400c030f802c140b14420501041807803a0303500045020741d166603480d414610f60b03421410000310041404401d00c8003011603038810301d1817400c1251600c0001e0030001d2203d985048564280741e02c414005006200402400c100fa50f088000d4070a2541c4941c0028080c00303152242075054559083ca0038480e5002194240388035101810580c002c440c59001d02107051001022032041c80700f20a400408281480345039145076107903100069076860300b03510160090422912102100c001542c012450700000501110340c020b01d840703942c50f81c030240324110a0541072001d00d00140d60b000030501c2500340d01600503005503440d0361a44001241c45a0f5000d681d29000d100703480c001004125400c02040c201e041040949004950104141e45140e020a01c40d40c0c070480105c4115600080b02204141c0b02c1c031030701c074071207000701e031404041e615200001c0d02d4510070090281e008849407010030b02e43e8404252090550000e00d4200c158101141c43c0700403013200803581607540200e04450502e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 359752230 1250 359750980 359750987
    0x5150403080a200405101107090c080f060904020402090a0b190f021501090f09080c06060f06071a0a180c0f1d070c0201020c1203041412100b0a0909030f030606 70
    0x301c1c03c010f80790707020b0b040600d00010000740a41c000505014040c0320080d03039002c01c5045c80810090416514003066070b90442200400c4840e00424101c05001403000703005190f502d01c43c1e001e800c150110340c096140c941880004000c00310540c03101446480c0040c45081400b00c0f510b44a0000302c00e515043d00b544158601680c45510511602c5002c00108005204414540c8d200411604060900056842e660f5440d15590303803003e101040030b54400710401009103000d150b003c8410030160383c41820700189945103d42680c0311410315500414070000500d00030800d5105000c403c40d0610f034503003020001d043c804110b00395400341035145201084081092413940090580b000004840440e0b03594461500710341c081171680041381180111010860b060791003401000d010510040a99601ca1a01840740400780349000503d0180e245850203c60015000c91541c200a4044802081881c12100000e1b84101a50041c11030145008588402d055101c48034a0414400f0346080018030b45912050303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 359753480 1250 359752230 359752271
    0x170409061d07080703050907050d21180b03090312010b030108010b22091a090d0e03010908030115050706050a0606020d0e0306011206140f04050d030e030f030405150403080a 76
    0x84042032010f400318951600c20f501880d4014104030507100c40d00e848100040484000032070503290b4180d11110502d070760820f42460b103400380c66810070309895450b90400c0302c00f80085208840394107800cc00010141001070007140c840404107103540c0c4856850b01c910503000d400038028490203610740b0030b00341c070715051116155030a22a800f50340000c000580754a80054500e00404a402024010286180c0a07088040c00e01400107080a82060b5100031401002d10f0f83d42c0900511030384c1402540404144100c0449043d1600c80264480440d00f08c034050740e10340f1035880d008083da0318000422100380710503400601514115030980b0f40c4000c60130f0f8110743c0502d00085681d0f05030808001004040c140101d160b400781d01c500004915991045904104c3c0307401101c038144a900c4c90000c010030040240586034009006007410403030a60902c10260b580e004601e907102e4480000408075081c0002000201c01201c9401c4540c002850640b90081600e1000d03611410000d0504c540941a1141c18201 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 359754730 1250 359753480 359753491
    0x10f15020106030f0210020a1202012708071202030c07091b050c070b0a141201060e031b06070c0305030d06030303050105040b0d06050703021b0d020610050319170409061d 75
    0x420042c2d501c01e40030811200781b41240071095100b80d85117000080d4158015050042c0503070000507e01d0400b580109494402d5046d4400d80c00340c2d03018402c00200c010b001c0e0b44a10b40c01c25258000c460310000b00364918821442e6250b001d01c0348500003d0304030b1540d00a42c200100b40202d0072459624003a0070b075000e02425001c0c01054000c64001c0c4400c1242601610b4550401c0c17804c0303048901d601a001c81d0715440088101c0c4510310751001804800d400c07481c6008a50700a40081040380008440b080001e140145d2840c0b14141c0050303000103204445503268042c0d034101003903e40e521104582c01c001802d0a102c103d01090801c4d000150742d140c07a10910151002c00b60403020201d0039503907544000d01d0014004d006050b420700c043d212440d0035146200f103c541c4900100500c0c0c7d01c040c1c02900d0480010810300041078144000c0c0300780d44010417050b81c21103c84989248250903842d04158401d4200068117403801d0120700022110700941140080396107407440707028000c2401d583c108081504403507 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 359755980 1250 359754730 359754743
    0x405030702090c1b161a0a0804050a060e01020d05160c020d060608060403080405120301140108100902031017060c030609040602072001080a09050601060f0e0306010f1502010603 78
    0x2192015061000405512008008020b031420318000c0325680103007400300c210507043c0d00c5180d10086008a013110100a00000117940c0c0b159588000d40e00014031640c141c08040023441c02c0071400b008070400402d201c441e4002824400e840d07295519034001e400400402c4c10082c146004140220762059001040c11820b81e1180d085990b0368083c000648076100e0101c40381941c0e07210010b2200414003245004074800e50740c2c0d120307600340b90505a1400810880410603850100010800c400b0b4a04501c4c100d0402030a02c068241c4c1c0b0300c40711032651203059014109a5000004202000702c601c45024180c440181e0440c40c02604801c0d4a03a8550003203034003000c4003c04001041740b611300014402da01901c640000f51074007103141d44080d80101148000641403042e10808441c0c0d42e0840c090b66030186208101304081c01c4031b5104c0c40d5440b031061150409000030001c0c010300d01c40c40303101c5112064034042c01716401560b40d005540d4442526214126500c0f207e0409032030618410700a0700212a08580d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 359757230 1250 359755980 359755987
    0xb0601080601090b0f130f032d060b0102010b100207061106040b01120c0801060303120f0c0f142205091b0306040b0103020c3a120203131a100e040503 66
    0x5190f81d850b502c68088003403100360030b00c405c2000451800c44030007d00800d042a283d004e15501e4427000040c004020410520b0201210b940f00d02401d5120400329500081c0100c1c0c41074400005274018461017412075041034043c030750046996000038602c001c94440396140b030301d4551044c0520340c44c1c85050301c3c002d08145103500108942034960038014022400786448031402c50340d90441c10b0841d81a68011804689094146402c0604c0c038802e904040e4402e203000d00c010011507900030006a010302089041c004690307202d14104501c10295440424072514000c010740d0103001c0c458240b1240e1143c1032080660360b00040e4a120440f503003040540c0742e000354a095031507250030000070700240ca034154100b50f400c0c0601c0310110810000e2100e00300c004080140700070064140065500c0d11544091200007943d031080c4205980b0a46030700e140c0c04a044e0040e2641c48024161440301d5043c074000d000c6400c40307031504105c00303c007800c6107009280015265015650711070130042459002c9801070b2007a0001d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 359758480 1250 359757230 359757239
    0x1503230a120e060a030c1404080a03080c04090c0201021b0c03190f060c180e010506180607050d11070603050717090c030106140301060b090f10110a03030203040b060108060109 77
    0xa900780802240142000d400d0140c5001c0030510301c0e0011248240080c2d11210796404050b0041a01e1444024450380149441d05104815582d206007520041c1000700901c0081da00d041404161805440000302c1402603040420009000c1c1d00010401a01102601c0c100c01200000141c0b9803600c10300600686034000c01007450f015440d41a81043c3c800b03d43ca15a080005021441417110552103034580785000b0581201e110031158003034005401400d220b40041c8400d580b840141d4003408000013a201c039211038540490014014480024218400d281c40002240e80014556826951120413102200c1c2c1c1c0b4401181501c00c1910203002103428000071603040d14100380380c2d69202d01c1600c221034003141c40401180c01c403640307640b14154504c1002410300581c0340a00407100240303402c82c102810105550002070750111404511881809e40b94040d5800e68099481c3d6820190b0100079945102104e060140c040d5100300c40441e4903d0b010030002c2e5043d809040d03404d00505040c1d603402c403e181030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 359759730 1250 359758480 359758493
    0x30c120d0f0c050706080415050f0a0e03070c030303060618030c030803060f150a0207140906060a090e0f161106160c080318010b06160303020d020d1503230a 69
    0x81024030400c102c25a11030089842044840020001581c801883d8a01400c202810800c1094804841800c14003800b05a840030040d0030341106c0c15100018a00002010311851413103030120042c6001c9081c1c00010605070103a0105048902548981c41c01d0415454040100442404000c0220080040c2030001c940707003030302a5a102c1e00c0503002c244100310b040300040e80800020489089013030002610589280d051007680002c107980030020319040d6100001a605200c0182481d000b5000420001d000070710501c82d050041041c0e040080c80d904142c00900140d101c125066140c9214414160040d02d00c05c15000c5040700320307078014029a8960b2003c043c64200026428000c000000102101082d080f0b8000d42c007549401d84002c980c0340341c4d200c205007921000d0000c47c2c407604090044100c1720045045a0b0036141d4140b4006a607000301045810080c0603c62010f80601e2900c0d69002a011031542c1e00b00a80e4001d42000302c46446141d0000d010b599004d40301c4c48180c01030341105000452 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 359760980 1250 359759730 359759747
    0x307050a1716050a06110a080402093d12020906130209041a0906030d0912151b020609060709051c06050412090605090607080d0e0f010605030c120d 65
    0x2081d24040c0c2c9059503501c1c1d40350150498107825110fa41020000c041003200c00c0c030850383d902ca010b410785e6017040d20000b00644a5180244047e004a03070420006000ca4080700d01c00b0301840c100c075181580742d04181100860969148000d2061408500307012600030366402c904200941e009006a690b80c1d035200900c031400401441845c036140c0c00b400340012a5840b0301500b180e881050902c040c0201c0024100300e16442d0251500d0301a400280e01c400303a0b40d5000540800f990b0303801045500b5414145044400b400809000b44800c5140c000c40180c0002410741d100480140d607800c84c3d03102e48400c06019162101a1580d90118070b51071000c0026081c00103040c020420380d000500501c00c01c0351206000c0e1007080317400300c90010031581c401d000c003900b01001e00c001e0203071442d0280c180700b0400b001c15a82d10400c50050400c0380c020826921816498111082c00003416054841c82d001c9100680c2c040d00c86030103941d00c28001c2500400c0c403400d1519803102c0e80c0b01664020544003488400a40384683d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 359762230 1250 359760980 359761013
    0x10150f0306030b01080d23030106051b0d0c03122706020d020f09031009020f0904111906020d030b0d0308130b15010e01020d0215070c0b0406020901110307050a 70
    0x141c4519001001c80c00d502ca446000346800d00103080480000038008201080100c00b18100314229024001d4042140d4152410f445080c280316580d4a100c900c6031954049150012590344146007500301c85a1f804008690302c18865103442d60314528924608040c1e0b40b1291104607210500466058110f03151128203801d140504801071508081303a068900f6a0b00a8080c0c400d16000040c0380001420304100c10040080359010821140c012640060481a00c10182c0d52081001101150500c0402f0700c15890101005040314066100441e400092500b54802d80d005409041071001002d40030b4066004071110052206d4480c1ea61a1390946807010041c2c041c629540300310744c0c4580050b00303c1d4080c50052142d14036080b07a04060200050403261044292411504040300055a1a4000608200455001071480303040d9031000c50448032020b000a029140c0b29881083c813052003002e40c000c180c401e038280c2c0c82f40908200a840241d4901c01c4d13031070080240c0d001c02c0e8a0404150403800180201c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 359763480 1250 359762230 359762237
    0x2091311151209010e0c120a03050306040b030d030f050a09031b0c170c15040b070f060b03120c0106080d090902030a020702120f10050603030405011b08040602070e10150f 75
    0x100185041c040582c804551031491617540306001c0c03000d2001040b1884060b00201c0300c04428000b40c0480302e45502145500070700f80800800480e4195642e50003124010a0140890705040315249008020301010126942c0007407402000c91182c3da9580694042c081c2c160b101c0c29841d80f06a0601c0703500c050351044c01d660307040101c1408148030004100e09040301c5c0b482001040d1600c07040c000c00c038801d0800c5240c581c40700c00400c000c002c1250054161144103420811286800c442400c1c1000078200c4070400b654540034900003170900140802c0030b08491107000008000b41512421456500c080c0c14401c030f00882c60080003003180d6515500115408803038241c3c0941000c640d540401c42c00584140c9906154200c14204001c00134200b10012001003260f00900007401c083d00881e480303206078090207040107003021001c4c1c83d01039280c002c50511a40038406a540b560381e0240251140c099001d000041100a0003240c06101f0002c0d14a00381c131b200c0a2303c8a2852031421042d14070164040a44090 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 359764730 1250 359763480 359763487
    0x60813021f030f060510031e052406041d090f0627120a03090206090a08030301031202030a0215041505010b0901020c01020712021c0c120209131115 65
    0x40e2a030a12001d4114940300300390304182800c1201600b900d0807941006030310392409400b00500d03038076201d6100411210741800503410700880541e4058010442850601c4e90a01c020b00200741c070020b1101350080400c2040304851100b501c20018203120310f1084801102d034449001e43d41d01d08160103241c114a9800443d41d0240c1041f01c0a4200f03e03088405882d03840d0011248800070400040c041f03101b0079030710050324001020004810706800340030b01040c00c269030f4004032011510b40b03804403800f140004041d500c0403980c80700c0540e03484e88240022140012010001801c150001050f100c103a82c0360380141600740d00d103007244008010020403d60714a580c0708103a240a1005101d00e9000c0c00c00019050341d01e03440c040c00a0702d01541c01000e181150710401d0200944244c8200c181c81980d811180070034076042021007031101d1000796101505074510b2250003d08200c40e0f100002403d07200f900d4024495541d2034101511007507040d0050400100420301c07540700d00e03080c40160014402a4040ca0a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 359765980 1250 359764730 359764733
    0xf050f340206041104090201021e0f07121209030809040b011422051207031401020f130f0501050405060a080705161a0622020906091e0406051207060813 67
    0x11208840440340540c026409101c203001290001440541090300e040c014500c0e40d6000135500e880e00c010403150201141460002000d00780440740c0c1d081410805c5803402a00c41c003020b411040c5190040f03070324103408180814900d000b414482c080701e400520241c00c2c201807005000262801c02d5030141041920a021401180100040c0ca000c400c01d140d0328500c0c05c80c520303114401c0d066076006a403007505215040610702c1c0d80003c500702540e92041981d40501580003881d0702a02501c0725442000030086a0860075a5000038482c0446080d140c0c200d088944d580c00550745440344c0c0c0203180d080041009054000f82c02445141e41000c5d0380e02c1c11a18141d03034000c00c1414a85807407021034440030007414540b000c044001a0b2504407100f1605140401500c0040c01405190702d014080e00315008200030381c25070340d06415943c404001600321110250007100c4204003c806040f001d214a14009000c03405060a510002582c0c00010040c00e0060230b10f4020340e90818010300190000a0410f0300c0d90 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 359767230 1250 359765980 359766061
    0x402030c0304060c090b091306150c05060a061a13031e110411040e07050405060a030b10020c01080c1b01020d020a1b020108060f19060509040f050f 65
    0x18400d18110300c11030384a0520b0303d004019549200d508a08200d9105400e0104000c0c400403941222021214581c1440b50300f8007800c054121544a481c06120214007801c02e5600000389000b8540710b5011f8800030750b100c2c3d6070b41c0101e4a89000d03010201c00341c0039480005840c0d15000302415040390300300308402c9075260307116100c0303e41c09807959500c1454804000100070011990501541040f038041c07008101105254005002e00e01c20b03105140025408500d840d405002181c028200142c60140d6a0030340c10b0014002c1c24a121074580240c42428103505441c1c804140d0b2408400d050b9130740031903500e40180c400c400307400001c0100400001032484040c400c0092004001c0a0b908407009a01c594031501c002d4035912222200c0307908104c4034000c0d440141c2c0c1c400c03406030780400c0031502c8104003070b081800308004404915a8129038181d0300740204045401c00064015031404a9052000c4d550344000201074903c1034414080d280383d400040341d20040c04107110040740002c8aa01480e2036268280700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 359768480 1250 359767230 359767237
    0x2011409010e0d0201020f0d0929040c0510140a03230603060609040c03031b02060a09051203040b040e2805010513050114040e0f070e0603060708010e010b0c07050402 73
    0x852282c2d03603051000d416180030300c007804540c00f1078002141003d0f20307410414180c1c0301d58650341010315944d84612007044001e2569640d11001608040c0c0c2610070012250304414081d201030740c0c81c030301c0420001101d240081c00300b0360205550b071780d030600c5809035a040380072a007109843e10203240e1181d004c004c1c404024035070a8140c1a8600c048070316814a217051500744403010300380c24002d1440c01d040101203000c0d0180c40c0e0442e6810303d81407171603644420380c0c8004481b101400030b50044e00000d20031045a44039540800b6900103c8200448001d0b91842959a10951007039503c0d8001c00c0c88108a120a06a0080c0c0e00201d0388061050380c02e070414a8900c2c020601c1090141c2564900050180e8101000586035000c801d80003000654100f4191490307204603d0b1400b4862601d440802d80c1b0b0501c03d00c00351051029180855010301d441d491612480e0f141126800e00038456240000e0400e80b192414034129942001007244590070300c07070440c16990044000e85c1891241c050000786685651008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 359769730 1250 359768480 359768491
    0xe040507090b07210801030201050f0f041a09040b010305130219080111040905062b020a0302040606031a181801022106030c031c0c11091602060a0e0303070f020114 72
    0x1076842d903103409a81c8050720710b02d0504c9030382000300030001880140d800004480052140100c0c580c0c44040b04900107400788641d40001d407888104161441040200c4400350164244c1107400b4080500034000440c2107440c1140d04003000c2d1fa40107980c0c0054200601c0f95010009003c582d108119200c0410500b907030618032050114400000e81044084a2407290a0b00715204650201c012814003207a8201203194928040040c00603c03614030841d43d4090f4594029035015005000c200c0da45d0a0140051503030841c40f6801124440d400c5041d8500540fa002d800700c0c1707400c54403202e80c0310b444642d0103803000359100e08803a640c02c0003a0b08016181300215101e1844039842d07103c2c6440c100040c1420701d689403000c58000d50003441000c8450ba0303080c03654428248680b400c1c080307805050401403d1617440802e0300d9003040320340c01486205000211120006145902140c400352034004940c0c007140e10307001e6040c0035600144041003156100310590f0884110720710001c030320304040322001c00080c1c005580 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 359770980 1250 359769730 359769743
    0x20a05070b090c15070c030803091009051606111b1201061511210901030b041509110f0d050601030905060709060914010c0f0614280b010e040507090b07 67
    0x221241510b03007900800300701300000030366030f0500419982c2c03a02104518000100004070100014810000410035124004001c01040c03083ca03046090a0f622030118546000000078104808581d00c2e00481c0989007066594005008505420301405013840820084507800b1b4255090200221001d001e110701515104070b81c04000f10001401920101200c000c604454008000403c035820017254209441c1302007610541c0e83c1d000e0000124010000140132070b40c494948161500b1040000341c8a000b555a526410406c00382c0703400460340b0900502c445000d00b10000c02c142c004050740fa0300140c1d0409810b040104003005c0f43e9582c00d00784001120b0000c00a8102c000402009902202c050300901200c11103144050b01800000c0025034030180260604100c4540d000070401254040b00003003814843c804501d0520070310a8007807541c205402024581000d990440d800890b100c1c0c591201c40584881c4d011150b981d00380000351000801800c18031261140010310411000300a0680c18442e24 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 359772230 1250 359770980 359770993
    0xb070201020102130b0a030f1413050c0a060206180a240b0603010b0903010c181a0c0d1e09060e010c1403030c090405010e04021809030408030a0c1505040312020a05070b09 75
    0x51b001f003c840210f4000090142815016103c400910907582d4214208040120030100e02c0e0410310726044070400444d81140040200088441e400b00c1e0b101e0042d01c4000d41c024490b102c00e00300b15600d411240c0058409c5501d442c100441d4120049491440a0801c1000c0303070780c0007070000240035500240e002c102c543d0000038103004d541c0750038802c401d46101c0d42e0506010b80704038031042c110320782d07458060305610010030003429000c02121402d580e04019840112a44405031583c020180c001e540000800c02c0c002d8022802407501034100030055030295560034100362501c000441e482002400113680c158803c1860f042203400500003180319090315032540755101100c40511040b02e50581c003000c100228442400300503074403810b1403100c40807050388a48040e219001d50505611503580300d10428480021390254050f041015200c0b6240078280d52a03120507104007100590b141281e0050009940c0c0c1071410740456240e014140d010f060303291180c1080140d039540c0070028010b17988442d00e903200c80c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 359773480 1250 359772230 359772247
    0x90b070b0618150f0d020d03031e060305030a08130f080306120303090a0206070309090603111f0c021323010306050709030f02040522060c0905040608070b070201020102130b 76
    0x409002c0d0140e5003255840326803400b00c034907496505521854511071801c0c1510ba0102d543e0f00a05048402c2d00146140c2c0415410f00d00940184442070200e48007441080044521030701d240f02c0d10080340d410101940c0f030512900380c02c590b00b610081c0300500045501e00d06001103526842d01c000c5181c0700f0b2440c5c0350350703050010800061840e01b64031903e40390704c1007041190141e400300307002c041c8542c181e60301c5444030710038074040c0c44010181e080901040d240c40000800d00080b4144001c02000130b03500405020601168005040c0c440c121120100740d0049500300107080500c80d05201c1e4070300740c000145070820024503d01c0c07a01902217040000c1201001072043c440c2922441d9000395040c2041403125103150391b0001e0312515550040e10440c2c0d20400540e01114400000d400c02c03140705030b000092540c5140c5080104160701c022000034030510800b0032181492f00c203100a485e8034900a003c01846c1040d008402e0380900000ca04554081c0305100d13a4100300916000030300310385008c441e01d40c4c401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 359774730 1250 359773480 359773489
    0x120f010b0a050a030507030605060d0f1505100302011d0307170a05010e0d1202090d080a03051812042903040305190e1e01020f0f1014060108010b0a090b070b06 70
    0x140c001c0c52040410f44800c2000030800545a0102c0340c0c4003e000c640750790307601c000406004141001500030400c6509030310402101030340035002d0a5015000f0051922039803442c4800050703a00009012440748554540314a031600087c603c1d0440007011945103545400404c40071004002483c40c5c607512040c01c03501045800c1c0651134451750300500420324621f408400804001c8210840b40002c0d5002407032600d5510f030342d1130307048071070340c01c001c140d541c4001054009001b01405c4401c1030501d001282d0718554303204045200c86001c04a010301d6800d007420840102104400e0302140d9085009c0b170350502c0c0c04c0310308181c06188264080e8660748c1d03c504c0007415540c4412203540c8403504205402c0c200845c6a5140300825540c42d00400f94030089681d07200050b80b8058604101d07050912506c02100e03500540000e80f6805005e1917001481501c0c0303584102c2030041d00c103036100e9000c601c0c030500600c40c5858402c00b410010b4541d2a100303940035921407100741141d0052400b1b44920a240f4104005400c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 359775980 1250 359774730 359774749
    0xb04021809060402120705070c09060f090e010606020303270712170307050301030305070f0c03081306020604080712021507030204030b010501080915070e09010b1806070b04030e120f010b 82
    0x1002d980540c60f00100511a480f41710f0002c02030b8003404808142a0700784194000070002409031000c0c10030900307895000c002200d240303600c034507861b403828052814804981805444225042d980040d415070301c448039078008612040c0010301d5203040050451204000c20003c0b84002e03c3d05110b082c40c1c00c03109080cc0c00c0b039039804503c500d000b503104006010b0000e80c44012241125050b18203a0f407100150f1409030030741d001c0480f020305403c100350004010f02007030800800c14203a486401d94039841c2c0c3c1d05010798958804440280002c2014003000000c525200b80001904105205542d03100c0c070180002c01e5048002d940707243c00a64003140c06e00400076000111400b51400f402d092246240409405a84a101004800c46000e4201c080355040f40900c0700e0810703a40008040070310568641d0180f0150b03400c80544040b61140029a806481c106031084500d015040b004c0519203a40740e8a00b640d00a4501500320307001071302ca000c2d051400c0414402c08200900c40400814500c040404200861a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 359777230 1250 359775980 359775991
    0x50111040801240308090a0305010203090c03100b010c0f020f0901080c030d031a010f18270537020706090201080c040501020d030b04060f0b1e041412010b04021809 72
    0x500201000183e001c0c00484008690780180b60341c1d034808a200120b240c6c01c031980d000400640c004018000c0328000400c41d60a00007081d0110345800c20050002c005a4541d90384441c003040d8042c11140100c1c00c0004400401c0740050400200d00e180303203000c01c9100000f68071039285a004441071000500c2c0600c000e00552003685010b10070240324035010009042c04d040707014184500e040049500b03a000d1000c1c0350380420b074100c400d800c99944081d10103502c2032022b21040a2100c22150100485441c82802e025146030f07905081894421070550070404400110325000448659082075003920742d00052005038468800031420000501c000360580780003410f03900c0d1070b00007800300303000907680010414403894a41c90007240304400c00c004103004000c26005403249241c04800800d2894040005110407541c1c5145040e081072821000351141c000d500482440014403507658440e440c0030308a400181c41d400c0b0002490514400c0020226031201c038403180e105080d00100d81891401e5102298800c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 359778480 1250 359777230 359777261
    0x3080f01030c050d0c150c0b010e0c0304030c0c090903110c1e0f040b090703020a23040312021e070612090203072711030609010914010509060607050111040801 70
    0x1541140c0d0b5490000c2c459000d03403402248580719140038046054004802000c005000c4228224030420081480070303961404c0d980741445a0001501c408849001c0d4826469001d40b0307400c5884540c1c0c2101c180d40600002c0d00c00e921060808a92002c842c8640ca880c00d12a80750a01c015003d03541d01400c2001010390740b889802010a08a1014214a101807848004a401050013078410380090020f01104070103d03040b4031507408016580e40c041d8000d104840cac040d2100d115090100050040707803010402c16801d0050140300c108001101c0700040100d50342c2a0050f500c8000405503920301034803013100301c0303000d591214000304107258000c0c014668525031600240207240c01a0042652034859104e000084148542020000c90715a4007143c142e0080d103005100060703815902c000d4903081905d40a10078658080005610281132088030b1321242d40460300c07589a032915040200d204001803405820031810020000000c400b84500d150408917030038215166410031740d206084910006000010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 359779730 1250 359778480 359778511
    0xd0207060f09020d110402070b0f0a0b1c150b1e040b0a210303140f010f060f0f03050603030d140a0f061a09031903020606120319030e0a0b130308 64
    0x25840b250034032042d4176007002800544a22030800303e40244101c2c000905101c0c000420300240c0700d00542d100b40500314600c001d2000c0000e0104102d0b0750320001d584410841d03d2004810300050440d500406401020b50001030b2a01d03e84022444900f407101c107581180541c03104050091074140700c2c17072110a5007504c101e0b80d0b013401d0182510345400d401045909448119070200c04040c82900902148511182c00c001c0c903003007007500c4100002080c02440003840c005900070134400c0c0311314a039861026080d0340340540c9401e08082500200b0000e0300190300341c0020010722080007454091002ca00324600c02c045018603107080c44408032106803240d1100316040c0101000702c419503000102241034441040c07641ca100310700c0080d18280310304108c0f02001c0c8120500100b410740100380d052050b40c003900e42082441800e01c40c10b0b2030f482541c0d20700040a220070070072144c03d403080d800110890340e20000c469401403c0d07107901542d007034100d900c02c8018207011900000c040d8880511504603a512402061 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 359780980 1250 359779730 359779733
    0x50702060a200403060b0a260d05030c0702010516050718051f033503070f02010e101104030f081b03090904060903050d0e010c1b02090414030f0d0207060f09 69
    0x74801c03840050851070300c41c0140751240c0c0d01c601f80c0c0030082c9440003212031f1951075582015580d80c2c0c400c0440c4198090707821262a843d0241086070311a000720b00b2885d02d0400c40d82c0c010f4895030401e0300e00a00e20a031b4502d045000501c20488040540034500111210303000a40e1490290b55000341142c0b807103a007111040b001401101004d500740c9500541000a52030f090080d040f00c01d0f00321002d400d03425403c0e4410756002c208000118000c03641030b1f4400ca03c00345209026801d07281060085032440d030000e0382003d0401e589521440200c1540039a03540380c90350300c0d06c0d8452801e038810350546881800007040080054032105120180102901450404043e180020b640703210052000d402c5c1d94490366140105841130b41141c111100c110800c00040800d10700450003003110004020102d1018400c00350318540501c4c1400711580e0040106500340e40b10340d1000b195450b005030f4071286100501282c0c2c200d1003600040e2001188020700141c641c500c4e42494029990340410310040149003429400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 359782230 1250 359780980 359781041
    0x10507180602070e0f18010f06030c0e13080c0109021509030105011e090209011e020c1e03120d180b071808250b04090203010509150108150d06050702060a 68
    0x3c3c0c5c031200d54100841c0760f54410801c80442401104066455440d24001e10084055581b0a105607401a242c0d1442d4603166848031101c914280c60700c2da01490041100700001e01c24000403c07200c108200045404501039010400e815202c02c00d440305101c01280c01185c60400b48289130050010804000007826004041c004803000ca00031400359a03000211581c044c2d0081003030243d44c15007902c0c02801c082d80c4400082d111808840750a1150a040076034481c90280010f04942445004028041c0d0b0200701002c54480e40c06074203e801c2682d22400d0352202c100c0500104401203010b941c42403014500710000a210020301c8402000390010030600703011040c000038900340080c40d0a012541104801030b040301303881000da031101c00c10b54000203002c91000d40ca038000d14100d40c0701b616080ea40d5180c8011901000e441c0680c0280051240740010b40d40906d040c05003c11902c01030001000c2c001161070311000e880d0205c65200141e031000c01482491803651182c0007030304da02d403032400c3c4441100d5030707620 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 359783480 1250 359782230 359782259
    0x1060b0a050d1103010611010b06180d0f1a070305010e0415050907150f1e050f070f02060301090504140105090c0609061c060501110316032001050718060207 69
    0x41080150100e0340b84000c0c521903201600203c3c00710320043d2a076035141c60040414030604050b1035203508003410b1500c181040000e0b1120740c0641c21000342c4900881043c46401131101c581a50048100404c10f00030600c1c10281c4c130500a1b40c0c0f0011049450009400f505882042c0e00c215052034006080001042c400041d80d840080c050700c010410b6100c00340d0f0545004007940202d4a42d004010007041d040d0341080c6200c05402c0c85271110361440006a6a10061080f40061040414810070500310000d01d2600106521846020304d60a161200e0f000300c1c00701d400036000400714a55070342c00c0c4402c1c082c010700450504681c1038003d0041e45001480ca81e144c0008403207a50003840e0100d15a0650b6540c4010b841f0280200c40300501d03986d90382c13110300003c1c01c1240b10309408515107840c007024082000c001c81d801000c00d080500880355207540c044801c490001d5105a1030004901039481d1070000703005250290722565104a10401d5250140c86002d1443d4440350030340d445100200051540d90980 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 359784730 1250 359783480 359783497
    0xa022b09141212040f02030d08010815042a03080d02030a0f0e0c010f030b090a0b010e030607140d02040e04060603021201060e0604020c0304080a1b090c050d110d0f0501090b0301060b 80
    0x48a40c07944580c03401c642d80300322641001f9894025440c100d0142503200c0059412500ba010403500702c0411320440d0fa120a20685000c1d081520040c203142d01c0807031500708200c0c0d2265025079210350550740e803120f03c484d030010800300c3c100316000070500c40000c006000b03260018440c80c00401040d4007042d2100c0d0f070381600d450000d060058100a480c0014021748c0003012106001e40b0301189440e0115442005140b50b41d00c10740030840c2914150383c28100000d00612600c800d49820000c030142508180c0a5003140925120341902040003044400800304e070b0f43e005522480700800d2043c290f2040204018a03030f5289031040c0e01d801030030004086a10306986c0c0100007520016501d21860580c0d40c158481c50300612400e208000d101e00401c94107140840c010700d1040352542d950b584a009007030541e60407078419800510f0034050041d0320511540146400511400c20515000c030042000d07094400341c41d103a40c1d036035540360300400044409008240070304100710000c01502d4141181c1c0342503801840d51 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 359785980 1250 359784730 359784757
    0x20a0b04030210020c0c031b100305130c23030c150306150708040801050c0403320d030b010e030102030105030304270207080a0210060503060a022b091412 68
    0x3050a00d4000c2c440c0303000400400740c05550f58651624596500c5110804640c007130711a01d040e10018001c0d45905d100d1192000740183c030f985510342012000b07031402a107040700c0c10004034028070008826101d203030020042c4451103a00b96a2680e1075008030200b0b010307224000c1c1c120f1600d11344e4030b03650060b501d100d01d890341d035596440e2b40740c0001042d90322203a0307545903a0b1090000760340028010000098021a140c5c400240443e03520854040c03044e010b01c2c44000c190b12080c0d180c0041216194440349410b5118801f00780f004080e00900500d000b413280d5540d004070741c1d110802c00303495071301050502403c801607000b50320310b516140102e6902d108501c00c08545c9446c3ca507a011a54110242403d000d4514030825510782d28641030a40855020115110142c804c5031030580f83d1124a0140c8400c84400a01406480d6201d0404401a607c02d0300e2190b028403884008212008024420741022044982d00256000c8a07150049543c0b07200c0007521550741c4010b03418002180c80d2011910925600003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 359787230 1250 359785980 359786003
    0x4080a0f0c020312030610030905030703030209041e061a0c03190c05010507090905010e060f040203090102070606120326070f05041805090105180307060507110616120507020a 77
    0x80c030031100c10000000003549801107080007100800c914001d5802820200d842030305202d0001c3c8154100c801c0504020a940c0040c4121404640a41d002d005403c00281c00820804202900d4070300c075142c00310342c8842e80c039a03d840c1404807114100889640e54114021285406c18540c821580c078040d5010141290500c040444405c43c4115038103054254000002c0c0400c0c2020100507010154502440e040d2618150001075810034079031141d4054140941030041011424050001960005040303004640d001c00014000030303150b204800c000c00d40e0160418100c8041e14000304881744c1082a04104195600c03d030704240e281d6102c03107401c4481800e0107440190702510075901c03405191b000032440c502050b0089070301046600014814a0000000c00c0940c3c2c80c1c004003000e80c0100700c04071005620504c90f00f070000c0c0c015485107402180604024400d5824501000c0c0391800840c1c8c40b010b002d4041c003409142a400034800410805140e80922440c44c010400035592481c2c1c0201525200c3c099 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 359788480 1250 359787230 359787257
    0x50a05030f1b13060206060a05090f25020a1707020a0e06010314151014040608060a0b0301080f010c03060303051c0f06080703020109050303030717040302010e06040b010e0f04080a 79
    0xc0d082c814180042c1150141c660b1401c04840340002040e01c03a020150044400183c000e00e8980aa1381c00d5480042602c0400d840e01266600c0c8014000d22640b0f002c0c3c83c940d056401607031110313102d400203402da600800c0f000030b00e40b5000440319070031903202400c200e09100910069070303070b4040803098400642010030740751343d8900100c01518103030804402049001e4180029a504501017030200142502e4050f03502c1403040003200d648003641d00e009820300c4c06010034810b440c411804036810242c02000c000c03030103898070500d400550003a4404021540714070100c8246010a000ba1041030103241000c00c011803a50310041c0c9103200e04901480c032860804006403400703800c0e600000e00200414000c1001c0c23030701d41d8002039654100d0f0009034041402000c1c00920781c035001007180d200320100c2d0398003101c1a521803002001028081d10032401e40d5298400d0b86c4401c881040668441c5000f42103030707a0203501d402d00780480490040c10200348503500c4002c10020035060307400ca800e81180c034035248008410300c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 359789730 1250 359788480 359788501
    0x1030f060f050106080f06100e041104050402123103050a030f0c0e030f010b0a030f0201050c010216020a0b160210110708031908040507031704050607050a03030606050a05030f 77
    0x1040c1501d042145008004508140d00500c100e02c1180940c08817a215124001000f4480207401e03020000502a4a5000c0c010300b402d80001c0381c40445007050a0038103845400090a0340c10038911070b030f00380000c1020018860780280110360080c1d504640444680001050360300040c1542001a091020029042491900c83c0d031000c90500920001000740c010401402007400c1000240644a0b104034540420100410312400320b14110041c00c4480c05c41c5107640d10040b05e42a6001641407100c1130040c0304400758203000070401a0103100080e03d240006204000b95060306400206070a8002d1184a100c032181c10181d200484d01110102190b0020318812030b02d001c0740aa001080317000350140002d2140d4000080c22681c41c0c5140c1c800301503a9840011503c03e042110081c1c000d44c042c4038200003140760250200121090041218a040d8890000c982c042d0b01140c0129000d900c0300c4d696905055144c820900a42060301d4141d250100081d0000c1840c040540710208880c20700000ca98030003c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 359790980 1250 359789730 359789741
    0xa0c030909050403020d020609011404020d080c150118020f1e0d020a110d08190507140705030a0305061c0b09010f0905030417060609040b060102011d0705040b061201030f06 76
    0x78003074002d10561409107802500c500d04480440054800e2401080b41142d06010b402120715112404281c565119002c01000c54031058060314200e10801c14100e9500c0309002d000b03100404007011040e594900007900450a41d44003400c88541d106101100480014800700c2e1140d10b00841a008078480c0010319001c00d1145040d00c01807039200041c5a04015000810405650180d509540c1080d003510410345090404a074006003030b001900c2114040356599019540002c2e084c0303054280241c00e030085443e80e84c000b00707040d5550380c40800c0c2d050250782c2c1401140c1c0e0024007541e4005644400078080d805160f00d5081c0100900c0b0843c0000f030075404258001c1c1d024941000040c0100c9059061054072036100b40540581009040046001d4030400100580100c03400307401c4031040e0740c0d02e4454010344407000d00128115525000c4480512010058011000070b44c03202520b5090300d0001044100d500010615003c0c240038841c219103d0f100101c1f450441e9089124000c800d405864204010403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 359792230 1250 359790980 359790989
    0x140f06031615080a06030309031202031213050d090803030703020904020c07090912050301031a061804080319091205070c0f090209040c05070c05041104080601080f01060f06050a0c0309 81
    0xa41d00000314005800b40208410015032103108003901c41c0d0b250402035a05138000503010600e801010000a40c441005d0170314a0010700c1035a0400d0203c007528510000282d40c0d95401e11050582c8100340141440701c6889117886041c40d00c0c16601c0c1a05094990000030119030625a0101e6407901c2c544076038044a107441d41e61404e40700c605481340c0c00c1400034205108191904002c4035102450540200c084074182c0e070f0000c0c0304080102c80c040d59880c08c4400245055004100c2a1040586603a40a407850190f48102c4189441e072518000d107a00000c500c0008010142c01d00585902007182c00e0490300d1070030750b64a842e582d903804a0901c030303014418552180081ca4451a8005111079055001c1c00c080c4204032001d109100f2560400c85c1c9174060200c02406080b02c46030f080202c2d1502d54000d20b54044162031040c2810f0b81c491007603080407002d0380004561741250328404481e0701c00f03108202c090703d00040541e408a091200003080340c000c2d0340103c02805024001d140926020303050290081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 359793480 1250 359792230 359792263
    0x809010908031309060602030304170f0715090b06030a031b0507180b030c0901050f100e04090c031712010603111911280605040f02120a03020c0301140f0603 69
    0x3c03c0c202d01d00768a039101602c1142c8880e441e01c00f006c50003d2000c0100c0f40201c2d080f10400000001e110001e51944d440b0940e0b4444083d420089cbe100080c0d059034140400c804a42d0740010041030030b0406c060183c100400c11407098011207c1034000070340000b5460700c0440740ca0071640d41100b943c50114a000c6060700800f5000486c0c114144031603456400202c03900b0816800e40d005500e8040900140c0d03e4280504d982c0062407044090072814110356203c1100710626000c01c1c1100d000c0040360444032100d000f990a0b024200080c028090041400204000300e505640e02e003058240b0750107c101c0d03041c0035100c101a00c80c802021a20203032820368010641c220384481e9006050f82024002d014011a4017005000d0b601c0d000543e500e8400c022101b10381000c080e9441e0b0240e03581c0d104000d18004108840740e07181016080c001da00c0c2d0301c680700d441d00c000c01c0042054451a0038060b140020702c1c40050301c039038102044041d544038082c1d2130980212045400ca0b4080d11f814000034101128204005100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 359794730 1250 359793480 359793487
    0xe0606040f03050709060905070f111c09030b090a030f110f060f0f070f050a03091b08062403031912090803150105130e1906030c0312110703080901090803 68
    0x6009012521000f1202c0c005d038100481c9503518440c00980c0c80485114000c1203210440500440c02051501d00b200055815945c2c0440c140b0002044040d05428460025070304450600400494909050b0041c40c108010401900e01c0d6070010818030b1491410f40800008502c00d200f200410000c000c0102c0c1d40c441940d503580f41c21008040c2c0340b0021500c01d0030603840000400c10303441c000d00d001c03040018150750349481c08020f0002030b4003424007000c0c11206001c04003906840580426070317544c06040c000c1c001e41840d0034070507900c40d14058600c840c400e04203031001c2294140d540000c1151550321211040032a000c2692800340c44150140d083c2da0f00503824000741004011003072000b10712610131061000040e880c92001115a07005010b5a20310742040e585007408100d00124001c0d40c4200e0195122846000d0548100152149030340203d805c5080c880081c82080705030101450040d41900d0320000b45102c40c013007141d8401c00da22001d81103500c0081c0c4505541d2141143c070340070304a81d00c1260b99 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 359795980 1250 359794730 359794733
    0x60e160306020315010e0102072903090708010e0d080a0c1e020d0912020120070f060201050402180f07030509250e0a050103052503020405010b0a030e0303100e0606040f03 75
    0xba40c001c540001d0501200f1003500103070760140e0021003014006900400d15103081000180d031900364030548800e819240140c00719010100703c01103200d0103003100a0b0622510b003000c2c807030079540c604100d428190404100c072144607600000e881da000854817400302e45020a42800d540301101991910146c0030402519101c1c076400142d00e20385921141c4d1510541540c81c3c1446d94010760610009001032500e40e070032414906008128405445008259031281e540c62018035a1110142d0017040940d4440c0100800e5240651400c01c1d14460700d60030f982c45250072455100c441d92700402c0b020078182d480d408115461420401c8226215100380c0b801554840600700740b5070403049200e006842c44030b08002aa11541034003e49040f40c0c2e20000800c0d8024000d8580d003c41d031800301d600c2c00414403561000000d40d842c1c1c01118001c0603074203100e42d41d5402c040401403d0f6541c11114044547c020001c0c02043d09040309100f08903112402180059110780c40010844d01c80e0307070b010030031130301c0234500100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 359797230 1250 359795980 359795993
    0x40912170105030c060a0503041406090609010b06130b210a0f1a01091a0d05010906091a0915010e030106090b12070f26011a0406081504060e1603 64
    0x381034030106000d01503030342c0b07104266507000340c034000542242c3c1c24888522142d02440196811a11442c0c07140c40094174809132616140c4121250151a44904144044806d0078071582120340826140d03141740c41d42c4500000840301442c41070b8a00220002200618410a0f125402540f43d40c802403040034282440840090896200072489042c41d0040c0c00640039100107608602c0a41a145d20141500c0c0400301e0484203a02d404005050600300801c0c10200300522805010b8020700000180250a1044081c12105078001b846180c100c844071565241d03445940039540402c170302400c251105041b6004071038038004e081e0103603019030800d6800300b105806600407400f011010f4400c4508000c2061105035201250b100703e00c0009042c280a00c240808208001d0840c5211080300203900440c0c2c1d007050840b03a000324145e1703a100b10205080e03e145054040c4a0003403a0000c020034803180c2d50400e9401c3c8400c00b80c0300419040c0d840840d13013084030090140108610001503251103032503882c10130700c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 359798480 1250 359797230 359797247
    0x7061d06090a0e13120503070f050c10050702010204270b061e1602090f011406040b04050d230706030506060c1905010b1012152102040912 61
    0xa11045021201400050504006031180104020300701d40c40a440c0900c01240403d0280c020102149100746000100c2c66110004080340c03469502c0035920300c0c15030001000500c0701d1080c0e00820038204842138003004002455004480d80f004005960388504005a009100c0d9500a4110446100c5048107040d800304240c00010101d01c000e2104c7c8150030200311903442160b910329498a0400541101098000c000c1c1c09403103901c00380c24a02c055640c001410190703080701c0c54618203402e000180b02006c809107070b9000a91081c0c1c0c1e09801c01c0d00740794101c0341900880c042c081c01071508048020510001180050f10140f15045112000b0300b18840300340c480c10b0340e0194001281c10301000c00e50700d092000440340103210340d9000e8185450340d0b52104102c0641140150313081c1d900e503091040581d44114083c00480f1464035102d9280d280301180b10103440c1000411200107512070010003150b10f00503410f50101924840c0a0380003d041d100160043c00310350b402500d48030403070303c200c02c0958100440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 359799730 1250 359798480 359798507
    0x40b180a0804090b010302040b04030b040f0213052502100e19030203030f0916030305090d0633060c08070302030f04090204090f05010b0f0c0f06090610090615120e0706 74
    0x1c4c0403210b020401034050341325034440d0645441c1c0c2004100081051040d030303142c100e440bc0d41810240c01c499000102000c98032000300884a07a140240300c40c9011003600004424008000041840c3c03a00c4006074844050f9000030441c01d4a0344180e010720b12083c00200b00540c0c40f41d45000f14581e281c02c000b96243c108861032444440b070103010508005000500704d04c3c078046841c071440060b045a03421100c54000041c156048440c0207020400a00f007070054000d80c100704601c85090f800104240d542658421034600941c903540d800c2844020fa20601e0700c51a0307078001000139070b540c810b498124514030911341d1603404008040340104803c0707556001031003200d044400a0010022180b83c940440302e0038868001510380800000e00d0040c1140e010300000c0e809a81580ca5128140d4030310b40c10048119030520b9250442c00800000e032100807000c0000d010024400c1040700d007031012440409401c0d09180081c491041c42100324030348580c02140c1d100d141c0d80d041d101c0b0207550341405413903002070810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 359800980 1250 359799730 359799749
    0x804051302070519230f0d12060501080f0c07171206010f11061503070801020712110343050f0105011d0109110c0d08100902070b040b180a0804 63
    0x1550070101c091000740d0f000c02504941d040d00121007145c403580b420401c03030103248458020f80c6c0c107020304090180030074070342280180c40d018652940000d200040300c0c4680c200505111461080c05140300e60580a02e40c000301f40100e59940e40b10a040c04806100002000d6200c4580000c043c40c90b050840c40746030007103100ba21071101c40da980f90000e642d14048082c030703000307694420400038064402d078143d0952082000303410780b5030145d150041c0d075007a40e06c400c605548200c120351240106c3c0351b000b8080060841c0000c060360500084132a50000b0f00d15007005900f94044550104035205401e440d1250b040740000520b1503149801d240036602d64074003c000c0140d55203858000a008202041702c941050250407810f5110303820580c4010080500c5117403e10100d03814012503d01d0f800420240300c0b2825151a001001d203004400400e210596400101420b4014030414000a4050920a0300a540f1114800c41c0390794081c55284040d01445242e4918443d09001d0014031003920000c000f515815031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 359802230 1250 359800980 359800993
    0xa0305010e04120c211e02010204080303040807061409010902010f08070905011101020d020417280f050a0c0b090a080c0916030b030715020c0405061c08040513020705 73
    0x82450440181150050840711514074803100c02ca1242c504107810701e00c690360210003100314001c2800200c041d8101440803902000301040c6c002104c078002155040180300a51505081c0000c035516808080d0005084a00205e00386080000c071f50002010b060210380c140c14180360040000c0d0191040c1c2c101a404151078070308141e00e05101d809014407401040d150b4822480c0303003000445e802c211200701480c25550030b0168040d20440d80c0000c0000f041c03030174880c00402154110060516024401d00310441e5035042c960a0b031420300c0701748908078580060051403c1441810080d090036850900280080002c1d1804586041d400002c1e264040f0180ea895800c140ca400141d55620540b00c09280d00070035983c009864002040c50b040d54040007803801003952201a40460301e404020340106601c2c0c001c1c8554060010390400982c03900c2c5408450034483ca08042c00818858804040148070b54071a9001c60000d2220300e0003110010180606a894001b944440d498025040103000300d03454021715 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 359803480 1250 359802230 359802239
    0x40501081005100f02030f12040506071d0103050916080601060e121207020d0c03030e1216050f04061a03040b090f03090405060d12082203020a0809150304080a030501 73
    0x409800054480180c0707103c00c0005070070825604400210a45821840708000b040100400362000d410f5000c2c0224151285003440e190032800d00313078020041810000ca00c05a41c3d1620071601d610545000300b820001559110500f802d4180b16050060301041403851400180c100400120b1034104c0340b69981e0620108103d004101440707507190500000d640c006110389100c0800d000040800610003042c80a103284a81d80e003404500565009a0119105200c5003050781003110201d2800000c40e000b900d00c40a13125800c42041555000b034a00a1810341031100154a490f48000c01501000070341100c000c00c000417107130840c0d1003140e080718000401000714414030b50006074015402c8440307000e1814007803002c0c148002044024285070f442983d58681c0350124a42c0906414914090380d1440c0c2c5c18070b8101e04050002d1041441403c80c2c5d04041c5c03066000c2076001c1030880c2d00552041100ba500d04140c03000808001901500381d034460400010300c4200300591005165600144d1024071650380e84 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 359804730 1250 359803480 359803501
    0x60801020a050d05100302090406020a021b092e180b010212030705090d02090405060702150610081009052a03041a060310020a09080105010f0302030a03080c090d0804050108 76
    0x74036082801042c41030018450324200360300101d03440380e0303840344200245950780c000409001040d5000e8504650000d2035441c1d0f00e40c140080001e903080114043c100c1d2402d1004034918400c01004001081d0b02d00202c1960400d0400800c00c04107a400050304140d910b500f0000355540c0d41e6420340b0940c0d4900b11582c030481d4004941341542c610046401825595502d00558203035001070f100b55803114003140f4550060795001043c0e8001c90050004001c2d074a460203001e0f1510710440d810b50182401e00341004a9a620380449004000d258580007010703880300385241a0324200ca4001c01c003000c5c200170800814080320a0a504440c102100700c070209041651000c81900c4140c90203420b0100300c0c200c159014000c1c211454011001408a403258980c4189200c04c03a08000d40700f00006030005810001040c090040901401e01c0310090076500c0d10710350000795902e00350301000742440081d0300080c2c6000000c105070b0b007081c0c40c00790441c003145106281403030841e131142c007805000c9036500300450145003c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 359805980 1250 359804730 359804737
    0x30604051e1005210705011b060c260c03012c0408030601020d0504120f030c15061d0114040905070f0e07030c0507021e030c040f06050103180b070c0c1d0a06080102 72
    0xc0d62010b4081c0c1c034208001103503000261ba6448888d0305030300c0401e00006c7d605104904a064140c0d543c7c10b1100d1080c0c0c0710240780b241c500340e0550144442c1080c8515003035148112070450350214a0440d608013600d0740050010207003540200c00441e20b04c100000c2c01040001180305031402da003940c044c6903507010155401e00a80c01011b040c109007042480000d01e001d14200d56a900078103126036500c040c0e6460444102c01c480408400ca030f2600404c1080d2515011004440001a860f500740c2c0c2d0b050441c11200c99140d031650512640e120341103078041c00007e101e454068200303810f4148015031540501503600728203941c1840041d02c1c2c02002a40ca13032265090b42c801940c0102001580559002e144400840945540b81e144c001c84100d540950340310321400800d10071065000c15224039000014007103540007034440c511034420401403400030303074075030940341c3c3c81070007424200c81100703e0742402c0c2c00c400010b4014000340c4203680c0301004070240982485101d08500c003814004a0b807202251402d0b0300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 359807230 1250 359805980 359806039
    0x103206030103050c09041406090d020c040903120b2106040507090501080307231014090d05070632061504050a09020d0906020f040e010614030604051e1005 68
    0x1c1251076034407614179110301c80c1074110303000f55140b04010b0054180b6038286002915102842d03030100020145182c0c05211943c0b0000c012903003080341c0c802540b001381c5280b4240700301c2402c1031354444038420307180d513030386203044031003110101d1000003501c4600b181c0d40ea080188d500391001d2203000c80c00200807040380a0241a501900c026504001c4250b4a2035244c0e0784180d140421402080d92901e4804410008085001008440070030b0300c1006440d40b44036a8409444c007521500822003d01c190f030b4000d012074140e294804000101d81c1c21500080608100444402d20020401058205468000f42d0900c1c01000210b642d82002d030385029581c1054440c80c424940c02a0201d0002c20100803150b028144441000c000400d08803003990b0b403002281d005482040b1000e0003c203041c448441c0c0301b2141c6001d00000e007000482d9801c0d102845d12140802010144510780b1800094030040c036104481001d00c0211034440c0142c14901c0e4080300022180c000c032401a4a580070011404503a81034000c0e208 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 359808480 1250 359807230 359807233
    0x3040b1e040809130f1821051b0304180b04050a201e0304051507020706021207051f0c02010e0a0b01060e01111f0b040c0f0810320603010305 62
    0x241c1943c0621100d103003d004c0300340405958804109001d0b4803801030004006101034095503078101440c2c020340c1c426141c01e160000350401c19290701081c1c0c200b0300b252480188403070300e400c100ca00d800a10340781d40f180d40c004001d610840040994203d40c141c0008418003001c03641445540d980000c80c0d0100c40c2071070080c64031400c01920741d103004a14100101500c04071441610f02400d0140c05a10792035002380c3d8201c81540c40711000c9540c002d04075003407a410500d9440940300051809000a648003906000c000e070300c00000440d40100241005802c5421400780c4406420111200102c0300038103501729a04099402d02003180050080070840c0740da5654804003004a07079090500c102c408182c024900c038140b101514440201130310401040d104502030310520844084124940f4040c2da030b1b030070110303405242031900203d0016007010b48a08031a4951a240f8401d0383c0780d240da50b200b510790f50300030012040086102c0d0114201903404502c2101c01c610582000c510360000e20905d44001d21014045 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 359809730 1250 359808480 359808487
    0x190c03020a1706210a050613051c020a08030c0c0a210327110310020a1403061e0f0402040915050a0f09090501150e04021305070f031104030803040b1e0408 68
    0x5001150070110300c4d0341c104000c0394400035455170b038a803030840240c42c0074180e00001000714040140811413000125101c030015501d82052200c069540c0204d01e2008100020100025403c41c07070620030340e8400041c1300f08440c00b4044c1c90030903100d1450020380303140e1694451322119440c10300038003618411800c900010118030f0090039403450400a4032408507506480190310f07820681c0c040229058074601c007130f40103030f940c00c82582c050039031005000c0601588106101300120b030b588d8180c40d0402c0b2020885028205040c400010300541c5200c20226401440481c02103007d101c0381d8050850700081c00c030190b0fa9140c5810402c01c2400851040f1000c0a901103402d000081321900074080c0030b4841c4002051941d89240005040643c9400955081d1804010041580380044032284090200c150030001402e111000900d042d5600c40306909050300e840c40200f1401706001110011034003c1102ca03240e090620780000301b001e040e1805c808460310f141200000b0717a40c0c14540350056520224a615 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 359810980 1250 359809730 359809759
    0x2011107020111030d050f0907050901060e01050327030c0f0303010510050f1309050a0f050403050316090518011518121b080c040f02090d0308190c03020a1706 70
    0x1056043c2c900f400740c60340414800e0700405c45441c010a0b01482c4600d8910081e4070b803031040c061418100d076211074481c04001004000c90358001840e461030030300a01c0c015941796244410b940103084c62043d0b4801d800c1000e0412000c1820110146c50446840e2003500c188581404405a5900084c09102e0f0710412040c070b8900540d01501c000c2105408181c0d0103400c1101c034200407070580362070340e201b50b10060300e4004000d00744c14240704403c0e015410500c100071505007620018011700000b0002c1a85a82c84100d5140450003040c5200c0141401031000000243c110494003482c1400c1c4540340040580b40001010b00d40154a912500318284002c00d83e4203103014650040404112030682d00c10440500c8200b8102110060360081d01c85540103240c030209250a110484a0110f694034065206100c240c00559420304140200d81e090701d01281c0c9620f54126011600e0480840349201a02d80324606992980580282c10440d1060712790720420390902e41070b014006000c82e8110b40c0700c0b1103d0820315 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 359812230 1250 359810980 359810987
    0xc01031d12130f08010c08070206040b01050613031e0b0714070308100302060a0f090b21041e11090115020319030605030d031401051906110102190c050d020111070201 73
    0x582c200d80d2030042201c10ba0380d010000350411070f03500800300c140d4446100c4021550805c240c6600000244024104ca29003511078240c042018080d42e44505000541f94110118541c1080d01030754001e003c4201c4010008202e080301012000f0441c0d43c600c0140008040a014105078034005d10380143e1149070450954080b500404e001300030b031810320b214080100242c0c442001900e040070480d00d4801501c1c0c081070b00030304196a25407019190b28000c00403144180c1801450b15035650103822414403a0310f47e442d140b00011086c2050b9410030361130350004c009001140d80400c9842e0001d9a41d484aa40c82d8016080c0700c0e21442100005070f40304108031170324402851304080c181c1000b0f03d00041c82c4e40c1c840000a09151482946d8030001c3d481d002c0c08025a004070f4006801010f0840720f4804010800040350b8030b0b80454412131044c4007158901180d48002174044a007000ea041c0780d00c1701c1c1c1c0e900051001e07102d061741400644142c41005039006000d4014032850100d080d0391a9180e04150140e80110b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 359813480 1250 359812230 359812237
    0x901020a15060314060f0610020706080a020706140118020a09060f020c1003020901120209010e1905060d1b020a021c0204020415020f0f010b0108010b0313050f0c01031d12 75
    0x1120040d5540b0001012411040c20030311002e00d000040c11141c10081b00c42d40d603e81019000b144036600032040e048055400140c80301c2116a24103248090360345007030b6074500a01983c800909070a080c9070780b03071aa200c2a1000c40e8103881490314800e04044c01c1c01c1880c3c049008261143e030118040480134041240151a0400503941ca031040305c03090006800070a4100354410000701c04242c01203100c0e0030300c0da0000c0c0000c0c0e6241d510b08085003800c500d800000c0100b40c40641403030190002c05c0c409101c030100040d40c10003601006d00600e6941206100e09402440d41214200c90708070295803034100715101059450300c41ea0004c001e04240380c9900404000d02002c094100d0784198204000140034070382c0c1407600d0400761a50068821401c90040b03c9040181e5100500c0240e403401c5140035840e80c1001c3c109040d280e0a40c3c0444d181c0d619060100a81c1a00000c050503601c41c4404041400d040065840160502a64244424508464600040c10825980d80340d0740d002a0500340150300c0e030074042c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 359814730 1250 359813480 359813513
    0x120105120309130e0c0105030c0a0f050d0603030c031b050a021309050604050115080607050307050304020607060e070311031f050603190506091506031b040222030204060b0901020a 79
    0x2a40d140002d0070340099a00c08000801d400030580302c102400c06010240401c0715455000c0c02d11360300c1c40c501000719046034070402c01040b050051046110740d40521480607a0046a240d91040020b5926810060604044150100e00003084004149003100d00c1205003544035511000500640003035a080000e181b2400186ea44066610048480801d004103d128065405540001251202c140c107a0030068210f0300308035026803080713007442911680a005c8a0703104000d80741068a80d1030398400070b402842000b40140034a4100b0010b0140c2d050301007210400c80b0300c1100b0030310304a6000c0d03003410749278007403000c0300c0031880700c07410100040c1c059613080954006001000d5400510100c10582d0084c1d00b43d280039186a4810010050140c504001540304200034130002611442d248000956403441070481400a409400348196039032107580507580e80800c20705074505c215415140c100c1c07082d0200d100c1039128a040200001d4006220401c0f84c0428406a02400d02c10b441c42e11000d00c080c0c4604176 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 359815980 1250 359814730 359814733
    0x1203030e1b060a230f12011a1209150a15052218080c0303161b12021c1d090f0105061602060d0f14061c0501060b130503100212010512 59
    0xd200c811403001d130040c891190300850b1262100301001c214030800105811044452980714a5000310015080071340b15826244e60b02c00603e0f030b035515075060410105000a108185456041c40f4180313445801c01d04140c1c910b469020b9500740d03030f001040402c4010b403801218202c0f0510003c0c030201c403280c000c0d016442d617400c003034940100c480c0d0b00c80c8a543d10400111409801c08424041c01800320b45545120100705c2c508031696000c00e580c0300300300702c074840e030018150000e04140e20f49132030003032041d44030b0130300501015400c41e09821b80c007030002d0703815685d8030105400d51910a026032030000902ea0040703c038209096250780c00c29050091552294603582c0581d01c4104100005035103142c000c21907191140c0c000700780390300801d81300d5040d00c09000000b0b42c0141010200086030315005100565500c0740a8140d04844d082e0030110f0041046411004200300c00085501c510200101d03440201e800550445203c00c020b01700802c128040c03040f221403044c0c60f020040003d440e003c0307101c44410100c40c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 359817230 1250 359815980 359816027
    0x6090711010b0d0f031d030601090209010210060305010e07090501030503030115050c07060302070605010506030622090501050907050a1a09012001020d0504020406080f060c0a03061203030e1b060a 86
    0xc0002c0d0240c00343c1d810882e2592010140c060425030300050032580c0c04900c0d00c171241050320071800070fa2942d60501580d0601c0ea40414003926070381c42000701c41045207115404001160300c0c2d003080d034040c0014400f02c84540c868414005141030b01c0344aa14100d0750400003960440c3d0a1400d0003000640c24200c4504110060101c440665000e108880080041b62401652000d15143c01401d485c0145c2c006849040c00340100519512000a03480b0a41050b2000c12140d401028a49005090200d0060300315880d100400500d036000185000c155101152407500950b503a090f018414851140c001189a01c00c1c41030000d44c1d4003070252581c02007ca801d40d8260704081d10039050881e04840044807001c1d45500030302c41503080ae4420100540103080107002d405580f010b242d80e55601c05010301481700c1002401c0c0846074440d80c4000003500001104010200441c20010301900c0c402004d03270103e000303903440da10318104240321030078078060080c05050502c1e44541d1300b40c40828010004068032080d0f803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 359818480 1250 359817230 359817251
    0x60a03141614060d0e1203010e07080a090b040f1704120b090d0903080307091a030411010203041a0c150702030c0c0d0c0605030711010e100b030105100b1803120301050f0102060609071101 82
    0x6c0c0050350103000714112689071072520003802040e0101c090185603109117400c440c4070124554812040d849074001c446a02d0f0b01c1594034000c04038441d00f80c05068450408140425400040d0700c001402c1d1307005060001e016191070801c941c40703203021540080131030301c2a0010030026072600c0c055075100701a41402d2040d00c0d82c409150140d02219215074a131543e00008010400c02c2c403000101c04031000384000c50600e803d04040414401d0340600780c112607080821607140160b401c02540c1075001c80c907100744459080210001c0c0d5a5041590f981c21b05010f210300d80480c50800740010b041e4142c1284611240c540340440a4400b0340c0050b01001c00c03c00c00007840381903400240600030700816680000c0c184101e84030260000c40301d094820610a0741080240a101a1100e004009481c1148103243d42c0720340c007d0360302040010103001550107001720412040d1a4080401030350480d0b800b40c40314502e100c8039100490f211042100e00540c00000740c4046840e02d0700c0348036078250400c1040c00025403180071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 359819730 1250 359818480 359818513
    0x309090e1f0906020d060501021009050705040e0a02060708040e130308040602031302030a1b06030b030c0f01020a1203050103060f0b010f0e0d02060c030406020d09080a0b060a03141614060d0e 84
    0x6003000174442d81d1a02d908106a581c104080b04543d40c500300100002d8150b942c40a4852615110b540e1090b0b0300d49101c2d0b2000d200500002d58040c0d4000c0c00c11341c1c1c9220741e01d0905000e8000348036040f6100803040c000340141140b0950084c0d150392550b100b07071259031a43d075140029003028000c4010b2041d420306403030041e2400c1184460305401515480101c88805542d500d541802d170b0480010141032604164417505c0020750001127807000c17180030b1120b94050300102c0c03400d01d410001401011854000451190f0141d01690580380912014420198250040c00590f28030780411400205003a8680349140c4c80340400190500004050002c1c0131030b26000940c40d5080765000c4146508000380403c1199010444000e04500314100130319210b00e400410341d11aa0312100c060100e489010001c0e4403a9141c9039440041e40d81b00640080300325900d84031a030740f000e403429150440020017001190900000703003d00c0207404c00070a020310303140700c0002240c0584a00101d036201c0784951031404103074094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 359820980 1250 359819730 359819737
    0x5011a0403170d090c050f0a2117040b0702030c0d02060a030f060801060e061804050a080304081303060b040c03110d0f020c150901050708161b020a0b070309090e1f090602 75
    0xe45c1c400758100342032404022040300c200c520b440c8140c0301c00c1c2c1c00700001849400b150b41c2001000d510385d66205040e050142171245120807800749543c001401050b0800800c2c05084140e00a03011105170107851001d00c1580c240c8908080c3d801b1704140050342c1000d209403c40400700c0010800856026650099142501c04503000410110640c0c0300304541420100d1002f00c45d00c28201e441c202c1e50038540c440070744903540359a026140010001c001000c0c0f014100c2142d10b03095600200c8000c05a80c3d083c414020050f01d52070610031401d1080b15400d0318868068640036201c2d50304900d1801140c098034400800500d08280ba2843d001c1c802000b4907001407190301012486800580c5039403500c20303116070071160014a6801801024028000a140200303213101013042e6604200520403810a40c02c00d0b58041c0c0800294008008000032541400d11009000c2c6a482928bc0800c500d4131080000165480c1800d101903a40c4001440203404c108901c10034518a00140002030180e560748a48050741e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 359822230 1250 359820980 359820983
    0x30f010902070611030907061106010e01030b0703090c030c080d020c090a0917130503070b0307020a0809041d0f0d0908121c02040905060a0506180111070503010f050106020105011a0403170d09 84
    0x200800d07020000b0b09c0d000140b0194401460700904010b40c1849452202264180009062107621100140f0668020380c001110140c0020048403266500d1800f1500c601d014012036940e402a076640304c3e100784c0001040e04121100404a00300f503510b8582902c02042400002d68117082c000404517108074100004200d800c0c503032102e1826507402c000034103181c01c9455012000e40e040400c2045001a80400e5105502c0c0d031115260703664083d00f200040107089411000c11204100038502d840c84000041c2c59940c0e107140800792102c21041003070a482c001e003a482170700201d40000240c1c01e50244001c00403c60b0414610347c0c240128031610580041380c006411481035542d030341007030041c1ca2401d0305d03610307005142c200d0341e59190100d16403601c2c0ca4000c0c05400641481941c01c0d2404142c0b070240680300142c1000b0780208032240e400764000015100a00c20b1002652034600041420718010300d401d080740702c01003002850f003491595400d4510122034011404e110003400841d2130072005d80100d86985 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 359823480 1250 359822230 359822233
    0x111030f070306050109080303060d0809030d02010902030f010b03071703120112020103140112060c091a030f090604170a03020403120206160516030e1201090507170102030f0109020706110309 84
    0x2407038605400b03011a942900300c18180f01400e0000c0140640000480b40e0080050720080000b8416240088840c001e549540341c0c14000c07207502e0303407405a0561181d0780144c000c8003115002000b000d080760880d044204c1068268000800a00400302400c01c0c1c0d589004410040324981f80385e00000500f0340c202030b0041e881c0e403e10f90301843d00355030349409001c091107000360105c5a19450404541d040e454400390042042d5200c20800100070b000d540c28900500070000481484c1080140b41c0220b91b0084a8a140c07030b071903002c0030656120380010014490b5074003040103100110f00001020568003d1303010703002010340800001c0002141659030405024490b0000c0205081c4000101480d02c145403c110030070006001d01b400e01b0800701044103d15805090041c0c0c4281e01e8000f140d1034030900c0c5071640c40b40d801d0500d03040803c900050450110740201d100843c900c06459561405d07448251050820202100014060911103500520005126403000074000401c01ca00d54802e40003195040d042c2d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 359824730 1250 359823480 359823511
    0x5010e031903050a080f25090812040806180d05071e120f0309020f1306030c0e1e0c0328290a0b04030b0618010821070f0b09011103 58
    0x131241c000c1d1019401c04c28500e813084181c580620140d02d841e160008a05100324000c03640608540500f108501071315070700c0c0540d003c020141d005000b0b285d1240c03242460724805c60b03002400b072903c80080c104100146801905c550604010200c8240d000150180c44007002c00b50b6541c0c0317a603030319a610448a849600c614500520328040504420001000c1805042c1010751500c01a0f44259404060300000c5490300390700206651500018010b80e00001d10025036400007195401c3d8651303d441c800e456401c02d0800031048100740006400e1b080c0c0780782c52180014000700b042885c0380d03117001050300d03051800b440c125501100d600c010b941401d641c88822000c50100d4103a84011007000c81083c50040d144072100c0740c50000c101c1001d2103688070150881260380e010806954644c9550528112124a0000c00b561144c28507500c0388078801484041188249290700c4111800b81030b00c540c26000543c4d0708500e89035883c0c00c10b2030700b03000f002c01c83d0555840110700c2401580d00003031406084c12880a40700c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 359825980 1250 359824730 359824747
    0x15071104060915090c02100203040c030605010b040e0a18050a0c0e010605070c0e060d0f0305030919051507050906040f150801030b160e06030f04032705010e03190305 73
    0x216a01c035000840d00d2070402d82c4035803030a103040a210007214010800084e4144908404a060403040a05140c07442d0001003800184154040c3c002e0580f0b0041008008503603860107921554422481000e01c5503a4410008907000466404040c0700c4240e6158079003200015a5480e0410040d40f004440780a43c05c502803007910710090281d0b0242c03c0c14206140741216984030900c050314180328031414000d401c070014586490301488507000d2584074040c40104002403401030a5074000719001c440904c40c501c4921500399281c621411280c0e04007014000d1310002245100aa4100130a41014040100860810782d101e510040004010503545910201c1c18105849564102da60300b075410400007400600100780c0f440c3d10150008812010000b00b600c203041c0680d08284d45071450755110502004000e00868500ca916100d14400e54031070310458243c409458085141c003034201e1540b800c680007400a940070700b8805c041d445005080340d06148040b84899005e504a07070048000440c04101c1d100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 359827230 1250 359825980 359825989
    0x3010303030f050703020906070b040212070b0a0201050907050d020f0d170d0b04020705031204031101050403050c010b04060b1c090503041202090f13021c0b070f1107051806150711 79
    0x81d01300001d490150303e85500340c0c0009a150043c0f00c0701611110742400400c0c119134418000d05a000f8400041e40c070180e58a40d00d40e14150004200b00016508001c0021100700e00441c1c08000e8400c0113200390980c504a03028058540403020005030440501c1094801142e004040c40890729000c200d07072551042c811041c001518802041e83c1e00490041c86000d00207200401074900404052600c100d56a5450500b00e82c078260804442110b5480c10040c0828141e00400400c9540b010300001d0212004550a10045810901c2600c014880c14400200c0050160703a840034408401000411440d00545500e03045d640243e00102c403003102c8244a1702181441e8101c10b901c481070310104283d0341b0f008946407003810002c40c0000d00c0b849070f000407005140b28010911100070380041143c2414500841d029043d403400103026404140d41a0102c03026400008031003080e180c01070030102051043e4004011050341c082c006c01c3d07008900b19a502c0382d410040020703040c200e000710340540400342d1000600 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 359828480 1250 359827230 359827241
    0xf150501020f15060402090d060213031112061b0405040f020306030c0108040b01030807170a030501080601120503040b0c0304150203070213060509040201140d0c27080d0c030c020603010303030f 85
    0x142a1a001880c43c20341040406070310a03400701081e01c0159641d40d0140024030305001c002002429148041190f640d40d40c840c0702005d0549200f1540c2e01d0746030f05800200700d10300311070021100e181d62050000a0095010807081d01c58a91035004060401e500c502c0002c0c29644405000b4440076070220401401c2d10307040111001c1c2c4902820314440506160b00c804200040501000c2c040c81f000040c100208503da249042071b00440c40c3d100d41e150240c007040200903140a1181c24628401d000011402c0054803803100045944a00114036091505c44228030302d42088882d02460301060000180901b40030043c00223888255000c0c59880784d03584100400c070020441846038480c501207040c8003d031915100c013604541c09080031140007041e40c2e4190300d02c2c4211009012000d003000b80317015104ea0001c130f04c50041e021f44e00039506045051950249000918803c2c280160702140c00d041e0700f10301480341740c0582c60080c80c0a07064038886801003801f6a03c00c1c0e00c01c170000707580c440800421881a1140307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 359829730 1250 359828480 359828503
    0x60106050a02150c1b030714160e09030702061902060901060f0909060b1e041404030c0813081603060e06011a0903010209100305100806090a0305030403030f15050102 73
    0x807410000c0c0c0c414000e41c2d40d554082041901410361004c244401d10b15400d6032640304003805000c290264001d4101d85a07040720008540404444100d0741116801007004d0628180c10707000701d140d4034a002d401e0688140007403e03150030b0340420448078000d600c0d00300c000d040900084c0141e01d1040030498000303203055001004662241d00d042d1040c0b00100d0542c401d1011a0a4030201050020321410130100805034243c3d9964807411030907020841240d090149403081d8000c540030004000c3d0170340e040510000c00c580050014090f01d94400010750800c0241016160742000001c5554480f91a44c3c94107400384a218104401400c2c1042000824040c040e42102d20001802c519490800040300b94081c1075108491404003188800203034a09505881c0925001040720030300b03608001c0090020501601d020302d0b0105070071808140c0a000168150140080e81e00400b507180035602c0848054201410847c101900c81074611044501c501503110341010b140c14030740c0d121345030000180c41c00030304106 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 359830980 1250 359829730 359829737
    0x90118020703030f0c0801080d0f02060f07031803030c0f05030411060313080d090b0a02130e0c0904050f041109010812070c03020d1b14010225030c090f060f05030c01030b0109081509060106 83
    0xb010078ac159001c200560065650001e66200303450340d0400f540600011510000708003c03000300340c2c1c01e040c0e00d50025064080380e9140c0c40709140361180c0c01c4650703100884010b041c1c81d2003d0004131003401d01400455205c004040654520b40c1207584002c070b1640701e101c0381e01d4907a44501c130000038010240055504414410b1086281c0070750840c6042c020380f01d520806501d00c0d068000a0144807660089a5000340c00034000c100929100c40a260060015113080d0344840750301d0401002810312400c0b580c1078603040c0c0010000b041080c03c546441d50320200b400c4480d50651200040140c4803803101c105010700c02c0001104030082d03c2c00800c200c001952003000100e0006002494590300411040d420b103540c1501c0c4000e480003c1d260044100d03032540f00400c2142404070002d8050001c4e40450748142640c20b0a20405660304058000c16100b809615419041800b0307520030b0b503021340d00110041c1c0d41810501031955582c00c1c1582407000040500165411180800031310b41820300c0311a001d80340504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 359832230 1250 359830980 359830997
    0xb1e1c05040b01051f0305040809030f100b060a1407020a150c0b0a15140d0b07050a030b010e0901050103050a150914060a0e06012601090911090118020703030f0c0801080d 75
    0x280c0c401d286007400702c1003004d06d50b841d40440c00b440311003000c58040200c081e045805030303102240d4641d42c507180d054640c880586031554040d0646444402c48400c00b603d036486500d002a09003820100d40d00404040b84d001c8855000014840d0511144090501d01e5071581c6a4441c20390620fa1201540200841c1901c2c0c0341150040390f0342d034408001c034141c03100c194808040052003c0455003500a013440500807420550401c84142c0d8080018002c10340ca0340e500780550400038005648145403910b11a50140b80e440040c0400d5110340d0003181e104000c1200070803040004e51249407a21440d0304100c07074054444242032401d1189001d80c1d60403550541d100894246405440306602c1c0010f04650b04000c400302140703000c0c1042001c103400102600e15040904d50b13640e446200188032450003101d803281c52004580d41881c101d86510b0485409014042d468400e164030b45000390f0001c134048050540c2c2d500103e1000000b032040002101c0e8039110203c041d410b2050705231624250003000403c000010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 359833480 1250 359832230 359832259
    0x402040c03052203113007030909050402010314040809040e0309060412020a0305120405151c1d06040b01050301060806070f0e0a0509040312060f0b1e1c05040b0105 72
    0x1000c1840c014208800c0e0042060440e207030813110361600c001080140d1003403801401b24107030b401c1001149844100e0781c40d2034214680c00120102c3c022458050086030059908000501c80b0b0740103254000c2c030524001078000b0302c070720340040b559074140ca05403005400840c03020a141070903c9000b3b4003110b10340045040101d4040010007078801c0d070003170b1604110030500b0f01e011510f50414079009154004145d07092140d07a281050255000780c882c1601c03846915800c84003549905c0110b070000c04c286411100c107054120700741000303841e45010000c1c9504e460b10280143d400d06102c424001c0e40314114061040d4901010582900d1840e0042c51160301f0040038000390640202d40e00e9007440c00b42c03d0000002a41c00c0010b4180000f65204541040c100c00410041560140d1200340400c0604410807a2985504e03164503446454024142460801c00c030010100a9284403501d1020045a5203480d1a07440703000542d81034000001c0f1282c56031600103000c01c00c454000018058103054411300c0d1070380c005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 359834730 1250 359833480 359833501
    0x720010309240902030a0503030a0c05030601020a030e0109091d120c030a120902040203090109060606090b090d080f22050f0a05060d0912050703260c0d0f11030402040c0305 76
    0x14805032980000c1c012515401c4a20b6800420206130000c050b0349101909040054a95104540e80c0304ea00c0e2070000114800c42c00360054034002c80e01030b8004d05541c060396505807402c00d0700b4240181440b5420100049440e02c500600001255200c018070080c0c40d122102c03480c0c0800c200c10145510760501c031030840403000001340d41d000007007840c00c100c0e8212410450001041003810281d003040c0000204035150005400c614a094890142000f0b82c40d520712040341c0003e210300911085480410500c00f00e4076002c5920614907025a248924107200d01103d9440b0358004e1858401d0391704202a11642410350f242000003d20b005e4a2820944010720005030401c58540511841404041002d084800c5640e201c046410340c0002000c8010302e034807401800c140c12a01c3d00b14006166450f01c510700e09900509031041001c003040402031070b182c00c84d2014141d003210708005502940c4005586450301540240c11b075004e5807109070303681ca007030074010320050714240644202170505110034801d100c8138 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 359835980 1250 359834730 359834753
    0x7030b030f102a171807061d03070609050d150c0e130506010c0f03030219091e08060f071b0602030103060506040209032104052706420720010309 64
    0x42040341d000d13890b92890702000914100d4155804148244a8003084094001c0d0310241c8000b02c03002800300360040b1038100741d0343d541700340a4000010075048040001d070800305015203440744112110500c83c0d043c0f13410601101d540e40c000b41d0024940a070a80e115003000015000d110314480303c10b11030b62170309000280031050b402d14000c01040190f0980d40600d0300c43d0381a07544101c9410310a4250f000700b00c10081c14904c80d8024004c3c0101c014120036040ca01c070950308801c461411000d80380325501e91440c050a01c500810a80c18040c940d0341c1e041320307110007040030303545940b1034840180c80394114180380b421501d0003444140190710402005541e5600015010440ca0210010f1721094420041c1081c084c09558070054000410010100001d65042d01042100308102d11060f0342d641e03003008021081c5100341c10540321044814130107000042c0300b116080000e000c814031980c500320141c08000c165001a2003a11800b2a90a11040d0f00c02003203042c02c400c11091138180300b10b200a4441c415101c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 359837230 1250 359835980 359836007
    0x5010f0206070806010e0d150f0e01060819050705031203071b08070f140f01020706140c1611060d0e060108060105060a0509030a080417010501120b07030b030f102a 72
    0x105001c00c10a940e110301d40e4400312980400c920700240c46150300c0b00301410b89a01001ca4044c145403100c2100d0005100f074ce422580000010150015a070804010b801e14a00007500c00d40109140454280c4007004900d40e0515014003140d91391400803002420486507003080d00f0700702040d0a41c803010035120300c150361802c0d8100b0894203000401c1d01d8002e81404950701628664001c0807407200c40b40b041940900303001405040248030380d81c0c51009000c4002000c69103000c01000c20b11480041d40c10101e080071486102d2914040700030240d40c00208641c00051003403000ca40c40e5001801c043c601070020324018041c510050150354102000120180900e0f50000c01700400400c0d81625a681080b14070349054000c1011640e89449512406102141c801c40e90309540c00c090000072564810a2a0444560800a0361040d0b40740d45004030084c00c80410000d138584540381d0b1700b035001a4103201e0302040b91540c0c54006628030542c0d40000042001b062a84050540700009040d00c6802c41d500d283c41c03a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 359838480 1250 359837230 359837237
    0xa05070206091207080c0102060906160f05040806180d0c0b0c0c150406050702070b0333120d030f090c090c0c080406121b02100c030204030f0c05010f020607080601 72
    0x8039140d01c00309260078021040040203104c0d00b0f40008240c100880e00c100c106a00b80e00b0f888496890307000541c2e81e10400d0700c1c0001c52800c0400c0d405160382c0704024074240d00d5200d03d0700c1490b095458101c3c074a894000d844a02d0340500042d94600800410010072910220600b4100c210141c5911001222803006002c08032015001a20407d010024409000c4451841758102e001e0700306400c00200411086800c0d2015220300c00c80401c484801030156403043c100060034001000c0100c3c0300c1d00032140303181c03400c0c1540207000032494140d0b40c414815a503c81c1801d4010a96886001d44c000c064503910b10200480600d001d69000100b000040d042c8203480e82d1000104d058590181d00300e40d049481c100182c070100001c02d0101d041c50307001c643c400480280040c1030010085001e80c00411356004035040c40503922055102c41d20142c180c000c4110313501e42e41001424203a5035114910a4007144208440801c0310060502282da044001c07032460012906c028101450702c0c04020703188440240485050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 359839730 1250 359838480 359838487
    0xc0603060a0e041202250312140307030f0b1009170f0f01020306010206010b12152206051903170315120c01110105070f0c0624030c05060a05070206 65
    0x2680356040908001c2026000304502c920b01810100c100308240242c090042c0518031901c01d558445801d00d0390802d13540403100c42414a180d441c186a0b20240c1c4200d1f041c0030031208030307807000d00040c2c0156200b427406450206002c503290926004451b901c001091080512420040c40d49600001c1e15040e80c0c00c940341a0020f94806d060a4601540300a110030380e84143c20000c4000c4c541900514040c40c002e03002c5410690300d0300907036500e901401c00d28111030010a00001c5000c400618440c3e040e40018040311405440305056a40d90743c0102c413000703216503c61108000c1401e007106620f0341c012010380c540c040c46007150390705440c105018018030382400c0c003c004a05490f2010441d00c0c110313900200040081d441004005071650300300050580400c1300070f84ca4909625060260900c070316525a941e0441400068003a40c10764850942074a40c0c1c1d56561155110000342d50b95400e24002111000d0f034164039501e0b004201c641e254000314042c1c0c50506c01c088129801500b074800f441d9046400c0c648 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 359840980 1250 359839730 359839741
    0x1d070803033711180d1101030906060803191d030a030c060605061c0507140a210504050106080714090105010c1104061512060e04030503060105070b0f100510020c0603 73
    0x1003000c2840041140030f407400c1c5140c4a8408448020080e0b0078548944801d08180c0d10f0800c82c510f500c3c1a4042e04109280c1c0c1c503a44558840d901851400788500d40001c1c1c080e48402c00c0518540001c8140003100fa00e008200d0752141e04000d0501501c9a10f60400d107824074080c005c03d1311071404c0f000080920a00f0404541004440d80001002d00b00103010399445410000c106071001ca50071102c0c0200b2480c05011030300c6644507408001c0c0142d160003019150034642502140c03000304081400c03403481c0f03116070b00ea04010014052240200d01039000481c0c0d0b00e0810319043c2c2001500da10100201c100d1080c0810756071500d240041c1111401d0800300c4280d900342c244000c001c0403450300e02d070b4006d2800401050140d9001c0f19001190040e076a0a08940079012441d02141c416000742d505062a0100140009100f400103690020040c0750550400340340f542c3d004401e103415686080d00381c03000820040219060154480180340032192042c580e601b0030006501e590407400d40700d00a4000100140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 359842230 1250 359840980 359841061
    0xf0307030c0c0b0a020d1e170702010609020d051e07090b030601030902030f0a0c0911030a020313080c1f06030305090f03011b0509040506030f1216061d07080303 71
    0x401001e010f00e14950310341000000079201c001c260390040210303002d6401840c12003003494030362018181d60386804e00300c0481c626040750112801068035003150b480311400b24000c030b031600242000d4504e0440c00706c0c2ca42014038140a82032050b00e41d1001c602c10080800200c507900c009040c6c2100c0c02c00400503620384407400100d010742054034029405124110149180c5140014004440ca0080751040300c1180c0740d03282d080c161002c10004941044090000c01d40e034010f15030046030424116444141a10107665940183e034028011001042c0c001907105880343c0d4182c0e5566035046030750759080042ca0f0450354060030034001c0a040b5401202c11741207048071500c095004510f40e0f07080500700e110114984100600c140d000e03c4021b8051414100801c045040008948040e44501c2024026040321014141020317000b035204019200d040b00e41c23080200311144203c03034850b0701901c02d0024600c01c2d041c1c51031410740e40e9845800340394070803c100070440e01c202c0d13181c8000c0e040026008400c07851481149 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 359843480 1250 359842230 359842253
    0xd0b0312040e041709010c0204020c07050d08070506060306191505040f0b1e09060108040f0204020f03040303140121151a0a0603020f09210a0b15030f0307030c 70
    0x6103096800980030840072000b02c0351a00c103510a95078000d603d4a01402060180a01690507001c500107034840c9005140c41d402400c600300100f021980d0300d0b43e98400003068203e40f07100c2951404400158042401010b00c4407651025041d0000c11085c10807180d0000001807002801c2074460f91000d100411100075001c01e002042c00400c244010184245280d00501100c80314a04c14028404224420108040c210343c2507a801402d011007591420015100401c00a1040710740c1820401c41d840142c0d0780384040c1c004002c4040782c1c191246002d240103400c803003200b01e400003a05410300041000401401a007626840103030f079039900b4042c9516004c01d0078601094044541030038450340b000c2c145040406081c40c4c01040b0b45481d1304030f50f101016000c92044801120b01d03000700300300c0b01520342811465040c40b00611080c1c2824040072a0100c0d08001e13203108212003001500051050182ea00a00a00040001c90140c100026500c0d0700da80ea03449440c500a06110300302007801c041c000000f444 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 359844730 1250 359843480 359843503
    0x5060d02040c1e030b0f0904080d15120f0c060305090c0630070801172517010c09150c06230c0301062c0f040204050604170c01050f0d0b03 61
    0x3412800381c004038090064080c5c07281d55405a0b100c60030544551a01d0315107140602d41011001e8a403002401d0303040081d086010340342a250712880400600d414180c004035503030a000f00210304108403285003c001100d5550300c200d00301401c1000b40300071440040755030142e80b030701102c00380c0ea030b41410402149a5180c0101e0301800303143c41e0008603034192518468501c550803da545c55842d07a243c20824001d61540700e1144e5083d0b1200424101550b0298a5250551b20014401c001566262402c0c28070000c03020124500b079445007002d111440d00404100081c03e084d06000c0c07480c109040000744045288140981309545440030104034111680c034049006155000d401158608120b59241660081c461080001c40f0012401e46071200c0c9030b60760800140041c50300038a842c1850400a1560102040b81e902030380c208800622540e4010082c070080481302c40212150b6008104c45080a90000750581801001c02c14021aa45800200d800d01000d4400003d2031149035008a45440c002611 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 359845980 1250 359844730 359844767
    0x7030516050721050c011404120f06020724020c0c01031d01060f031e0c0506090307091a0a090203091504050102040f1d090703210e060f0a080a05060d02040c 69
    0x20341c03040340e1410501041103107015400300e45e0482403100044410741900c10706442611405e1000b4005421a6046100c41d04e00500161070503075441d032220002c0b68450b041c210303192040030702130150070802120802d00c0209400f03001c42c203114a1000082d2501140300c0300034101507075429040c51285601d20303580e405801d035a00030050240c5649083ca4602200d000a40c0c1504203841900b07002207045100c10072850344081070580151600e07052000755040a0360341d50781402007000200764080d4901c50740c15020070208080340c4000460040c84003002a44d0070284150f4010805c0111007100003c07030011400c105005003d60b5a564140b150084c082c0e0341040400700c4000c6000034a405850010000782d15081034001500e0f11031039906a07a80301103110090003d0002c010709e403960301c1c08850800c0168198100030754890480c0c000520180e02c0131134500190607011501e80c0a20341e12800c0503511502800080000d8100b200014180ba4001540240710760b4882d14481e000398458915001500318229 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 359847230 1250 359845980 359846009
    0x10b0d0e160602210f0c0309180601120905030307050c1908090a0b030702070302060a020709060e09010509030a1409010311070b06121b060a180b04031205070305160507 74
    0x4906004445125400042c03184407289681300340c5404114600c16024a410741c44c00a01000001c110f41140d090064240000d010500c00c50b1030b130070a4140c4440001e0000d807900d20380303500050021094040c4008041e450f10203c0d0000a03000011aa041002410502e03119200300f80d060f840d15030003c01a080d00d454040d2201c04210b0124094608040c3c104e402e170030016241d0010310100e020480d108001130303021241c20400b500b040d00007441e980401d4410f41d0f90311034403000048140d60b40c0d580003101c0b18404400b0004049020300c90580c100c02510007642c81c20401c160000d10420705842900000c042c00180b00e00c880c1c0c029400b81284004070083e10761118000c0c00c28880c11201280d8441c010720140300c04561394140450403002e030038a40e0b2007d084000f50f00d4180050358008403092000e200001c2c12503010640304c500d03810700600342080800d94680c214548030000f444850303580024800e06001d803000186c0c01c0420365041a48603c0100254035850911628001c1154000401e20500a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 359848480 1250 359847230 359847253
    0x60a031401152c07031104030c05040e0a050d050a05040f061e0201061503020315040501121101031e020c150a021b0304030c1503140f07080601020a050303010b0d0e 72
    0x6401548203820344122040c040b55403081d01d11241c05060403000c0c0700000d42c1c00c110042180820156410050a190019110003035a4069460742c0c490342098130620f012240400152505010340303084210514090405040303580d0b6001d5580001402020600c0790215040d09001d2080094400901141b04401d09040d07031214090a00c0e19482801041503c2803601034580342e005002d070b03204441c08400c5803441c10080301000c40080d04064800b40c40c2c950100080c5540e039481740541400fa0454001607200f4020600c2e0080480040c901010b05040c105030120768030240d400c800e0003020240c6080560343c2e10740400e08a003050014501d1506042c412010311074580300d260301800c52003070700204250b80412020f00044e034038025032000401e05d0300c107140e09100712444980d0b451400c9085042c04114480d08214070082c880040324110b6020240000704804c5c241e1000d00300f6003208003800a000090800e031910354491005014000001000142c41b084810f00c9032321400c0c4011802083d504040c250 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 359849730 1250 359848480 359848483
    0x5010c0305090c0a08061503100c0818190204020304022106070f020f1b030a0605040303090b07170a0509070e04050a0b0f0712230f01080d030c020a0b060a0314 70
    0x964a4480742c0c4103083c42015981005241c40b015110b01400500d0203030703118a14100c0194241c1651900750207400000003844801d07004075080c2d02d0300e5407207000441c940310b0184015031140e1940c0e4030441d0f000600ca040e001ca082e65100740c0b100d4040c0d0b400350b030300da80e0b83c00414614000031126801c2050440381443c00e040020941d540140a2039076190440c00c0071003000c9076940d01003019100743d83c0098030303c62400c03840040a117801c6117021301030364581ca0590f00e8501c12201c0c102c030b00ba0046502d5244d40c804018210308010351100070303428070302c425405014007131410f420b000f00589940342c5c0e5100030600e5000c042101d44c009050f052080150351600c1d140c260344a42285504030303880b00d00300000c180800b81c1c0c0c103400d520840681d0b03500024141030140c154003800c01c00b6143c481c0900d03d240c001c26000700540a2a01c50f414504090301c05500d37001040785000400e1024001305442d180c42d1419940e0b000c210a150507800c188100e0144d291704c40024843d0307240b5800101407040d400c00d4407010b02d80 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 359850980 1250 359849730 359849741
    0x3050f06041118151809031305040c0c140c030a150507030c0f050f0f0301121406070509130209030105070903050105130c0e070c050d0507170415110a05010c03 70
    0x8909101e002c07040d400001d01442404070390305a0749407031043d00043d4644054040d50007412000900c06507283c1d800150f0306070910310980c4c004000b6000056544000742003000e9400091000351030401070119044070040c015007003094002c111241c0c010902242d068200b1014020640040c190382d1010603a2514401c40b4181115403070909050100054126010341300341045802113894217002c003002d2150484940e44446481c48854405200202508103501c3c05180a8032182c0300d2980c12800d182001d08048080f100b030001c1c60740c041e10802c840e00e40c1c00401c3c1c501000003503446c0c0d4510005d401218029000300f0019981541c40d0000b045181b9521039001c100312070007040200400e44485100840c408051080500001c4070545c1c00c020000d60800002c1d40301c81d81d450032801c0710011307a941506007845428603800280380800c4100601032200e00c803050344100c0d02c601c14079091620541c1040b0716100080c20060081410340041c06c1402401014005940403000300f00701901c01e60060010003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 359852230 1250 359850980 359850983
    0x203011404050c07050c090a0f09030e190f050f0a0308070c050a0e010602060c071a070f030606090302130b01021002161103010209010221091206013f080403050f0604 73
    0x40c104808922500f1032032080341c40d07141d041409400c55100390310901c0000617001e01000d1b410740e0703121503501e0581c020f03100d51188144a69901b020340791a84c030400610000f6948402c001035070340b6000300300005071411203404452082d02c400b0305031811603000400c1c2e550903610140080fa4001aa1410409042030003000e40f0b100b00d0314605030588075040c1c6084040d090040c40096404940480c074252210005000300c1449400000c0c46440401c4040030042c1040e141e00c00031441e1451440c54440d050301400c1c014000760710389146814950380000f01d04c451860407108000303aa0f541302c00c1290f40300f4040006007a8080c0707000e641c1c55981d00c2943d02c0b0080c0c0304070141e504090000030b061440c83c06008564500c20140e00030603001507401029000c803001d48001141c1c0c031404026041d520f440c0d180d03420a80340c03071150141c4103075854040341d01001b2521501031211107107500440144080079603c505c600e402181812040c000286c54031158038400c60304080c00d0361144248400c1d40300d000041c054880d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 359853480 1250 359852230 359852239
    0xc140705180f0a05040f02120d1101090b01150215040804090b0609012003160c080f030c1b01050d02040e06030d110307022412012d1203020a020402030114 68
    0x224101c0c6080c8021026102107041208400100d00c0081c11500301d00e80040c05105919200e5290b1b50020302c50112522415203240c10001c11192400c0e004102c142e000900c6070700900603001141d13680f03042c03074a0501070780080c40c9400710040c1035684200900038810410b032203d2419810907080078000c3e0b130030a2141080c81d504004100400741841d8041c0c840020b81a1624601080c280801180c012941d4500807003c0c0300910070540100303d810300410000380240320300203901d402d0a00582c2002c5400c407003000664401c00c01102c03440c40000b440c1106044580a00d0940c00c0d08000480e124170a600c0c0e0000c040380040707004200c07600d0baa141705000300000c6044030000082c8034130540e00d4400d10018902d458000380b0140c4e015040c00c40760007401a0504000440b00b070b150303402c006942e4002031151000e00300341c8801800301001503524880c818600c14259031034580030802040c98250316015082c44e40520500d102e0400d4020403d084140d07030700400654913980c5a00d440c01c001c0501e4000d441c801d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 359854730 1250 359853480 359853499
    0x70c0906060507020d050a06020d02070506011a070308070207151205100612020703053001080609100b030c03061504060b040f06051b0303070509010f0815010e010c140705 75
    0x911020303104480803a0441c0e282c50341000340a070200206490074842c10340b03c40c001c000c03100001804510040407101c62007800141c58801500f445031400c6c01c1600312120f181c1d5141d04119581303c2280c01d850300301e61f0504d4440c03502d07911010100d0903c0c80030360248100790600c0c01480d0b45903030050740405040410701402c000e244d07504007803180404140c0c841c8601040c0841900c04941c000f41d00104201802403d04600c3c080325402c102e10903146a03001241b001210130741d021041005e5010403401416000003c0c8120305206040030707182d000803984500c5003503480443c00c038039480c00d000b0720f0042003005068507a04e00c4c141c0354403600d4800d50303178000e845035140a0002c2510380c00c0c1c2040d641551011441032071254101441510700394440d6030040e04840003c402e0201800041004510560490703442e0790703c4603e00c200142c80e000391035041105000381c6034200a00c40740c401c01c002c00440f4007442c004840c4c0540c280180c1c0c2640d000030001e046040c4050301c00741c00010006100040b03580684d1003042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 359855980 1250 359854730 359854739
    0x50d050f06010e04020d02090909030a020601080307080f090a030f1203050106020d170c09030d030204061206050612070509100918020403120e0a051810170c12100c0203070c 76
    0x500c0c14101c1e1601d010034422180c11040d418141d02030800c42e001d0f004010314202d88400002c01494003103a482c00c05a1000407030700d14542c3e0501c21180100601e100071400d00f4081d50710440315002e04d50508076101000f2650751020350b101808400115002444c10203819980e00306440d00820000012020908140c0009055440054a115403e0150342c802c41c100d061010118958400030701001b003048800c0c0702c00c003600d541c148100b441d48025502c0c016038a0b0b25045000c0c1010701c505c00c080c541a880d140c0104000d80703d50341242e840594040904240e9503c0c9182a82c4c0380c0605601d05420212000b0b0180300c29422203060400e135054030402c140303a80e0f0f0021041090748030700c2c0801003280d440240207810541c0a0b5040081402c8010210b0042c1030720340c800720f01c2800a441c01000403804100600c102c0c08507030310b036400152240b0101e4411800380a23546654414040103143d005a51048071a00311020a0048510080d40c2d02c0302848134001d0414020f5490300400310507a581500c4050000c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 359857230 1250 359855980 359856001
    0x506010503070e1309020a0611070f060c082214090609270708010c0f200303070509040902130203010509180c060a17090106060207050d020a090914070303050d05 71
    0x340700c0e003110307a03480c18901c04000c20320052544200c84138041e25150710040c401a928955080003410880d40c5228031a000b44048624000c0940e0204818125080c03080c0301e00d9a020302018413064002450a0780d5002d0b60381a218a01105074503c000d014038030f02c0100d088615003901c001031031005c54040c17030b80f51900303000c000c0030b110305480e01d0a030302c96200d021403103029080f24401d00d06040141940d19052303580703080900351409521101d0004d00c0b48440901c04680000c03513001c1c0e0140b00100900a41c1d01c3c840381641e40e01c0013030040d2007406004554000c0d5a50b441d0050500300fa400760100d03181c0b0b030040c148080650407e00840d80f20310000d40000748401d00007038140000c5c05c0d021004003441010703401840f01c1035010b0840e603800c008020003c5100b0020101c441401500c0450002400c9490501d009081820503000107100720b10f00005800036a44811205042c0d07101a400010310444074a00303070021a01c804034810b40c03030068034000401d064000010b0325003201d2910003842690703030798482131 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 359858480 1250 359857230 359857237
    0x210201020301050622081f141306051810050708060105071203020304080d1a01140408060115020f060a20070302031909080712060c020303061f1407030503060405060105 74
    0xc0d0400c07030034821400811000101400107031740c0c020f90300c9010f07900d0b1002075040c14205240d210700c44041480180e40399246100c0c40d0194100340c80720300d00504001c0031032183d14280c03041c0a4903583d206c00c0401c001d00c0380506c1420002c11a5821144080c07458001480a09002c5400030003161440c00082c4c82e65010340112008982e100d161481c031410440404e80080d00b01810079100c51805004007150141144235220802c0c20300c40042035860f54100004014200c602c10708900200c09010803c01004005082d034150341d030145607241000c030008801c071320300207406064241c80d2140905000c030f01e0400e03070303c95458200150400450059140c120550911034206d000b80141e008000b01e0031540c41c03942440b84403404d549040740303c8650310b58907070b441d108840d00f00f1440031a8103440a41000607903c03e1491440b00b5001030b5055107030801c0001c041070b0211003c11503000307540d098062898491042c84200ca03d06100bc90744825407414010042d80003284c00c10b000e02e10340404540c0560080007174 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 359859730 1250 359858480 359858489
    0x705040b0a03060e0703060612200109030222051f090606140307030615050a02011a03210c0d03020301030312050c0d0e10060608040201081003080702060c031303210201020301 77
    0x1d06a61841d5a0350710b0300070a0101011310560103101320110028806005500c000c00c14001140a54070450402d880c040540c504a0b0a1980001804e04000d0343c10855403402c030f98045038030920840018108000e4114200b0071901c0e001e1400d810071000101e0000480501c03640c0c0700341780300e2890f105d0369148116159409880b01103000005c0d0810340d04100002142c0c0480c991a0102d0410359a4060412581407018000c0100700040b0b08624107550900c101c100b4206a8a080380d940600000070075200d01c64200c0301d0480000a40008400c1c203d05001c8803034039000c1e90b04491007600b41b0310340140290000e0004070700140700c1d40071208044103607000d5039000b21860340200c0d01d0458162103050082c203d44619600c54020001c45000c086c4c100d00c5504001e000603140c11100e4902440010300c0c202c8001d10480c0001c0e02c003403040c0041100c1358203540b540d60b4180e5607143d0b0796407101001859402001c0002500c1180890701008201e0a05400c40701101154400070403018040d03426403c1c1d0009014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 359860980 1250 359859730 359859739
    0xd1511120c0703050706020318010c030209030111030f010308071707060507080c0703080106030f0f090b06011403090304140f120f01050c0f03130c05090123041a010806151b0705040b 80
    0x172000801e215034001d64018030001c007011985556034a0f5a030948102c42e02c1500469408a009860390500307001e003d040c0d02c01c220740c2e64a98600030020f004160010b0002400e043c00200700307034040080c401000807204c842e03586041d460707400324604500506011101000001c0502020680602c4010b00391000150f02da2950012607007410011002040300703110010f480c9858100c0c809640d4114400c07100c260340034130803000d01e0740b52100000d45545100301424201c03000401c200302c003050b000b1095030155450b03e002124035062140001c2c58900000c0d4405500800e400c0800002050016100c0c002c1c8883c0c00c0207200c240d48205d40c410ac280500350100030f409104000068144940c0041452028030030b02c5900321080d00d40c00821500c01003604500030402c110003450400e003110f40329101c0300b50403c0307506104090104560941080310785003028180701100c000f113a41070381d40302d80320000c84e42d0388400d180c0c44440e41050102d002c00b040e010011180100b10010070141098050100f48010190 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 359862230 1250 359860980 359860987
    0x61103130b07021006241806030209180f07020c030d09030209101505030a0b09011d060a0305011a010e0f01050319020f0415020606030a020f0d1511120c070305 70
    0x22200c12072000000c1002c000c5010340c15454149011a1260001404804801c02520301140119004404621984400380040b440c5e040f8084c031580c40c003100654031186000f580792150040031500c085c41c41d80a103141d125180080040352004000c0441c80380e6460350071140b5020f140010305880d0700e01c0d400c3c00070005201d03003814005401c003501020b400c142c0c5501c0f40c90203a69520720040100552211110005000100740155805940a007a40121040f1580c81e0380d545442e05616103c001255002c010480e140000b9106564002c41000116003000080c03041c0b80410329669884014200040d01203031400c0c0ca4094541028805c0040f21141a150301c6d1850701c90620700640c00703861082441c8699020044880080c2c0c011002c1c00040580c2c00e0321915518908001034242000103000d54060fa02500500c0c01694418505415105083d145803491a100341801443c2442d12403c10782440e09240c0c2024143c80d0000c024444111448a80c0c00e490b1904034071040c40307200d03000005d03000600c1407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 359863480 1250 359862230 359862233
    0xd2c0606120d1b050604030206040317010f1a090901090213091505040509160608060103060806090606060c070f0b030a0b1512061c030809070501020309010203041802040506040f0306110313 83
    0xca03c4850168445103403510400d4895031541c0c5005401c41c1e0071001600450301b1300042680010010b140d040041003a50840c0d0704104d000001641c6a205461200d1242c1c01c004810343d00540c22a120044040c00303c20b215a11031400e030f80030f5445440b01e0700318624140e000191001342c0703115450080341007061b071128403407a180402015141c00381540780300780640004129206544003800006080710340b918a02440d040c0000740403500c05a00400e40358202d4030411000b12004540d04c2c0d4440e000310f80041d01c41090300d48941c42d101c0c1c1c0c0c0d0440760307480c44c0700103001c2032910354100030b58412408450140b004400840500c60062203194590066a8040c00300a00c48800b09410507803001c00038017144d0903c2c0c1c51844003502d04122032400e501044900060100720501440a180a00420b000462508665000007903a80c4182c1c8211039861403008207108581c1c90300e0b01102d0050800400e10f64032951106505d8110480c58482150038074580280382c0025200e41042e00d02c035141c0000c00c0071548075103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 359864730 1250 359863480 359863487
    0x81b0708030c0d1b080109050703020712080a0204150306081b01080a0203060609040515030f010b01052a0f030d240b0306030a150c0e03160b0d2c0606120d 68
    0x4043c04903040740d2500c950701096007007110344110480c80380c0e80b40b80f16949810351000072140301400d0f40c010140104020b070042000c00c2c030314014038021480c1034011703540c4081091000b4003880c5c10400c05400c54880800301207500d03401c012b0135202c0070300c155034941001e2081c0d4511425200c411502090b500000200a10195400f43d43d22a80161060345482090300000d4129201211019031b001505001c0200d2810104a1100e6200784803000700b111b07041ca040041d101d4000c0c410040001c0c02401c0b41d40d588503018030f070711001d403044100465141550f00784055441c3d03005a4010708405103044103c01e0024180001e901c02c652006045070b100c01d04006901002c1ea000900c01d0780c052090b0106000014100005100f84165081c4006580610720400400200d6048900fa01c00d9100300001100300204103041d0003203c1210b04419960140005284064021100c1040440e0202c0c0e05600d8038a408444a004001c3c084042d80c0066031950108880316107608050400750307002000000c030f418003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 359865980 1250 359864730 359864737
    0x6030c1203090512211b011a040b040603061a090c130312050705160807050a0b0d0b030f030a0906030c0302071223130f1706040605070c0210081b0708030c 68
    0x1c2d00d01c29284175000d4040480d0314202c0100310043c500100060300c80c0007940180486044012181c0280f0039951200b500c400d0070301050310b0b614401c03543c0d200c8041c0d803580e8644c080c400840e886002442055204503800301c207040308030012401600c1400c00200480100d004542c400003c440381c00ca06135043d602d46070b186c0c0c10242091030600104105d880003080080003404210211603041020403030030000402d0521507964042d0307008910800041c04003e82c0348058a264a516003400076082c084a8002072920bc98490b504641e8000020400f0304581d114509409840007620248210003011804804034403074624003030003003031040140740c40080c460500d070065000d140c0d055012060703156007110b41c107620031024070303174420766990741000104240e42e410001400549036445d81800050300c800e4507040000c0c00105129918400145114010280c0c840681c0c0c0282400c0140821503001074402c41c0241d0f00074030118503106820042138051000c94502d030350b00ca1503ca003035440303402c224407240c1c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 359867230 1250 359865980 359866009
    0xf010e0106121e06061107030b060f04060b03160221070b0a0b060408010212070906050301150c0b090f0f0c01021b0301060306230a090b01030206090d0204060906030c12030905 77
    0x342c85034040144669024040c0c3c515007032240000541da8a4420003070f103590104105209960854202080415007581c075407984803c055650020000804002800520300c0c0d40000041490100500040a10110a82c40c08031465000c89001c0100e141540c141c00100b0410031100d404100b29400000b05480c0c5116044030110070041000c071100c90000310150016001110940c1d404182e04000c290040c0c2d00355008945410600806400c11100038610301c014080c480c640c80300c0c411581100d0b44240300c0c895125802401034661030502a17a51511070000740e40c14016480754040b1401c03aa00c001c0350509a451050f002001d000c1414a03410410349454011950b041d5601c1d8000808030b4511301a9001c0f1440300e203802c018216603181102c409107405008911090714094020740054016810b04d41501c3d011100551510007603c0000c0307041b403001e48003e41050805034001081d031409c0e0032000a803441000902060b644500008030001c1000a000e400640900020000303800c041c40c8482c0d009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 359868480 1250 359867230 359867267
    0x30c040618030b07020a02090f06011e050702370b0d0b01091206020c0609060709050402090d1a06030705061603230712141305102705090f010e0106 65
    0x450341c9490f0195890700407102d40c80543c0240a4210840c0781c1111a1580844001c6520305a4200800000c01081d2400c2c040150b041c0995464214103000f00306881c40e0307030350080c0f601c0c280040309542e05880c00741845081c1c00141d1104034021482c43d034845000241d842400e6164101880c95080398041c06144590f02d040c040181c8010401c0510712100041860003201e002daa11300c00041c24a00d05800200480810f400c04010702111580c446002c4040354401c45002d41c840b522040000c0b19401d80030401400c005148540005035800140755601c21b64003202a103414641d144140a0588680a043c007034130b546810a0350000780c000c04013282e1510407242d098107403814002c0d94103030a9024040684504c03002310f41401e0141da00541800310710f9010038845090503110b85140c2802d00183c0a00e920907600802005034640c810340a40d241d0011081482d41e402650701c5949440c01d42900410307016442034400500c60b03c44071a02941202c1c103003a0f81c00c10b10b0f0310b44207003150450b1640c000e02a14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 359869730 1250 359868480 359868527
    0x12030f0b01050a080c1b1002070c050111070b0d0e031908100501050706050403020307050f03090f300f15040606120b070309050a0204022109011b030b0a0503030c1b06030c0406 77
    0x60316080002e47c60012041c0c43c0165503911908003103203000d519a1140703041100d1202022600303400032800390102c90381c1000803a00d0740c0000c0c11940141004a8060205100209161013000340001c8408180c07913060703c80b07050603220040081510000d602455001c500704204440c001030b01a84941e60140c003078030589041c0505aa41c450408038001703080c120903071012443c8442c0340b03043c4030701c03482100e0101c640742408240340600e904c480700d0040c1c0e05054526200c3c0b9607070744640240007105426100006079404c110265141e889440403e55055842c580390010114814a050210b4190f10b0b802a40085041c1d46202045014054a1400300c6450242845c4000180c590380082c1568907210384074240f030b401e44100d0001a60300020701c4440d0301d81c11305a058441d84a07030361401412180c0da01c0c011604912000c080f5258481561205815110000700c0302c0d400d20700483d00c143c2c42000386405aa042c08020104170320350100707031054000c4c40c00800003005085c0c000d09189040d144040c101c0350301d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 359870980 1250 359869730 359869777
    0x61119020d05070608180601060f0e1f02030a0206090a230a080706060e060d0305090f03030c0706170a02040e0609042603011509030c03140a12030f0b01050a080c 71
    0x10292182c0c0513101043e040b00078010b1255013998042c010518a82c000d001c030b503260420080002480c00b403201d0612501400348001d580710094542c80c0440500c172000201403018500035521707806003201c0e2005000f40780214142105c0400c0850055801c82240180b207000d07140300003110141d40d03114601d18440d403c1d83d0b0f400180b50402034034072180105000540d0030700d000ca4880c000d1070003c01052140d4802480d200009070890240d5469450560304480c01452142c007103440d43c4560640290b01e07214034070b40020031a901c010100300580312420300d80340e503445442e528001c0e40650300500c4005001c1c68001411414609186a8050302425402c21500e00b1080043d070340045a1b144816000d40000c010b102d224056607190035450381c140303041e0207a0703442c680343d01010601c00c0c0401800f400b8002c01101004900700305001d5401d400c025000f01000081801170002c01d40d030031008411340d040000c280e4856020301d041e6076180d021926854240d07034800d49140a075500180044021800700a800078 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 359872230 1250 359870980 359870983
    0x1215141908070b04030303060501030c230909041104110f0d051302130b2805040f0b0307060f171909080c070603060915180e03191206061119020d05 65
    0x80103041003d5603035551829418002d0903125250095030605040075151241c0b40e50142d140065000d5000c010010b4080400b0325542a10400d200c441c0d207c1c1c00c00c0184001c2c040d1001058020000403202000a4000300500d4541c40c02a0b07010994850020300841c1071040d000d0300269070000e040701c135032848800079900082a04444042400201d030741d90341d140b003060424008020b01c101041d1402c40051000000b4034008903040d0150900450719028a440244002d402c003031000440103054a0800f0b460f0040240184814500103001800e420580340443e030a107c5858000d44035548030038062201c0801c1400a80038502088400141c10080e002001400b40034100141943da50041903051504d002201a00c1d0114408501c40410740c2c400c015030030540c00440582c40e150000444e5640220f6802811170184030100d061340304200c8000c8030b50991052181d07032481003806041103400c1c3c035100129444200008050340c681d100300300384119181142d40c031000c407610003024500c608007290f4a0390b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 359873480 1250 359872230 359872243
    0x201031104030807050d0305010b2506061503112104030e03010c0e0114040503060f07050408120a110109020109061206150c050f030903060415090609031215141908 72
    0x1038480c60b00105085042000c1400780490031401e034a0180009d50515140c40c805100718070510b02c04010901c41c80751074003403411084800c6600044100011036440c0ca60803821000c8409000029181024402404644000317450041e000c0060b91400414004008034411030040d00c142c0c28004504114101d170b03030f001d0054518003c05030399402d04110b201d0002610052000f10010304c3c14905000a120320f0b10005000b41d840414094803141c99115440300b03903883d1040f5040040c2c61301034100c001141141c1240113000703a404960700c51010700c2c011501d0a080f0344004500030700007100700c0340030403400b1b2003650002c9003054800c00008105941d00481c6a000c18001c854501042d2201c0d494020312106000e11802929540040c0d40b41c4076040001031748600009000030704014407030b5401224201741d035204d54403103948084100144801814090a126500394071225000d0400015481c080c032142400d1007200c2c02c017607001d00e241656908100c1740c0114450b02190845403414000340300b52042116 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 359874730 1250 359873480 359873483
    0xc1205070e041e0e06040b0c0a090f030b0613020c0705060306040f02041d2404150306020307020106030c050307030b01141906090306200307030b030c0301020d0506040612021c020103110403 83
    0x42c1c03079183d05401d60110507202c0d00d401d002500d4000c00c0c104004295000d0105a0158540c2102540d6980110068442044540003840351044001000c0300300190100041d005030412611040071040e94018001030b0f2080248402c10398119050400c40ea060010185405c003000802c0410710101954a01c0100c2c7c0096009010782602c0c504c615540c3e0803500712080d00001c150794560404088403c00e4007042c1b82d881441030149684161889a9808194170f010203190b111209640e00d0600007c002c3c040c0046020a41c0d41e4100305c1e90015442c540052140201d136030041544000e42e00e0704c4005030695154512064100d40b00510f001178031610510680007521190710703040e0000742541400012075403001030b0300000d0760f20100422400c00740d03501a0b0742e00610034035000c1441d40741503000c40d040030158031031b168043d80040354400c185510f5400c80b034440c40040e01c00f001a2650b030942601c690313810180194120302e1070002040328400740e802800c41240181808160042c464018103402d5019900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 359875980 1250 359874730 359874761
    0xd0519140402090702060f18030403150b031b010c1104140103030c05010b0d33020a030617070b0403080d020c030301091b02160506180306090a0b0a0c1205070e04 71
    0x100011843c0c004410368002c2c2040c80240264034220120401c4094041c1141d101c541c0030a4030f01020706810411603028507404a1a89009110200340502402003210101d109000310000030f000c0145072030161981c000149e4605046080d552541012180c40b42c00042d005500e50152104003928480800e008600c20394540400d1513503030a04500b12401010350718442c02c001c44102d008100090b682c1603a814070310401200701e10220341d40e0348080350300d40440d040e401d0010032031406282c1c160f4000e40850700300a524180c1d4608804075152104041d00968480d61000d110910200d00b071a0701600360180e03070200041c50107201d280780c40e10b150000d81c0040c0007a610344d6046800310f01c000c2801d041e4200700e4001409120090500c40608010901441e8003480340882c414602d0000aa1011040f20703001c1c0c02c0d240701e403d1030100b0903100c040048041c4c0d500f00b0b00d0b002103200d040f914405c00714100003d986e807145c0c0c410607020700406404054009400c102c3c01c6000020720b80e48a100d40d44030000c1021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 359877230 1250 359875980 359876021
    0x50d050c0109060801081f180b090f0601031e17030a02031b071104020a03180803010602060106140a031e0228020f03091306030b130b0a0b03030d0519 66
    0x1000804942c2211040084500042224081c001029562805900040100c01f640c403c0f980008041d642ca01d441c1184200500d035052080481c1070310b02586002040d01d01c2114003010030b541d0b402e8280b000070804141c5552980440781c0300c00c1e11200e1244907200c0311141510322000500c03150070558040c040258000140b101c15002d28104840116a01020a01b01011510f40d00c0d0000c0c5c5140c19240a00c1e000195108102c0c465400301c200203044104aa078050080c0c01c0444403030f0002d00410001d480b4580012030f95030b000b1403800014010540c00f5a1070300070003100440150880c41e901c080c03007036545042982000882d001408510b540740c03452280024480309911540110f22227050155040062040b200d030201000f21104c040050b40c52a14524070071807000000d120395070016048403c4881400003541300c3c4401940e425006003440c00039520745018100031600916012540340c1d10410500451b11800d0300600d510004c0a00105101c103030354955041074a208421201c0f0a0001a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 359878480 1250 359877230 359877253
    0x210a030206060f2d060d020c06040501050c03090d0f0c060c021c0f091a04090e0313080d270e0a060302011704020d14071d1522020c0304050d05 63
    0x400c43e80c83c00000464995900e10b050340c90307408403003000e4a82803410b681440d81d01c1d0313142d841d05411102e8024113540115919000a0b008580304c0a0994080f100c5501380340c0420109038196003075078000e1380024080e10040d10400c105072102003805280d84144158503c070800440c0d428490309075a45201d40142200d00910701c001440380d50040054404d0090500f0138056003079000e84020140d56090880c1000200580d0000402c0c2c040c981c421482c590030300e26180f0140001002a0035080000349880100b1034480802e11380780d040c44400400003802c1640700c1101210b03540000c01200c0041000c072440d590b12412513003038451040b00e038007050688a100403c1117583c002074441da0502005100306180c2032550001f2000b03261001d01400c2ca00c40a0304400d102c400500c80c1038000c0000344119403182c01050040e03843c4100458412400001403d002203c9003814640404000d8101d1000d18540070140030590082d0050100b04005120074040810b207911008256101d1501a00090440ea03014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 359879730 1250 359878480 359878489
    0xd0f0507170c0d0c060c020406150507020108090604211107030c060f020303160c05030f030709141c031101091a09010e0f1b040b041d0c030d0905210a03020606 70
    0x502d000140101c03410700e0100b010603078441c00d1000303541051800e10303485003641c00000d0190640d03801c0b240604100c5003103500c185030040002d00d0360510030780b110341180e0b44860745251a0402114048c01d038909204900314250054603a041201d03020b81003041940120806481c502010350700116405220410705200c001e40014035000412001c0c8020362030b514184800002d0704c40340e5800c000501807600255420000705100390b5610a088120054072407921200043c501c00c02449071044d800301c82c46140945081003900c10000141c00030018008044581d000c4840c1c0d180707105141025541c801054000071500c0c0907105040300315506040c01424400213803421285c210f60202040c2e8030208142c3d0610202040000c83c0200c402d1b0382c28070103402200420050b1000e100030139409854110343d260709080307058864400042640844084920701c00c241a80c80000136824004102c2c0400208007030300e0b2107900b54940300100701156100151100215107009490340084000d604a1401c010140c1031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 359880980 1250 359879730 359879743
    0xd0e0627030610061e14030c0406030f0203070203070212190f0c06020d0206010b1c050405030d1b051c0f1509050601050403080f030601110f0313091a0d0f050717 71
    0xc11043c2c85824030329020019040507100000003d40340a510b5070405007500a1400b950705138180c0c81081e6a03494000c1c02c802c07071a4494000c1101103072501c038042d0354002c01407003a01d100b14044e070011403800d202c4e40c0030040c00c080210b451040d01e201d0109110b81c1602c440c045211582e101709158105510700d171820030324803c440e400200c01c5600c020b084000c510781c00154241102c800c0300c00c2c0e43c0e448600e40380e1032205000000003030344600c0c00c1405220401000100038103004035001000c02600306810245040c0d1022400c4000005000344481601007080e605110b0030165078400003d074004240c1750070420f0b00c10f0a810000505c0e401d84080021007180c0c007456a100200f4607025107014103507a2610712a006150001c2403010011000402503400f030000c0d805c07a8500700301151000b890014240741c2c0ea0b0721119000c280010152000038491000d405030700a42c02c80750b60a41d020030a40c0050000c1d0704200032059038401c02000c3d07280c02060080c007000703002d0107513071484c5540844211485850b100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 359882230 1250 359880980 359880991
    0x1508240f040506070c14060c031e06061b030c010f060305070b0a0503040f020f150c011404080906032d01030201030506030f1b0d1b0f050d050d0e06270306 68
    0x119a0300c2040009100800c941c2e904c010301d4188001d201a02d42022030b148011145071480602c00e0750f0a1000541c0c446002e148030308011030132000d81c880d4101460346803184c1038580303079002a401d002410f801108040c43d560360075401012241060340e9003801c0b03800d41d88501d451401030ba59500c01802400303410312078000940350040c107c03458884030b540010034502c4000c1c0003810f0028088489070440d0344424014100c10340050001c032030550b21504040d50f5500280d0303101caa0350700c1c205803048820076015002d07104680040c00e2a04003a450800d0140940c401003010b554125200003030703114206040718180140c42c96054004580d070640c0b001404642003c3e04103403181c1e012000c10f8019841c000b509d00440903100c40c000c4101c00410010540246c4982c0008108454100c20300c0000390042d00722100300c404084850f24a10390350418044038501261000d030013500030060090b5214020b03a494864803002410041c41c0012050031201c1a0b000140b02079a16600042c688400f4030f020403030141c024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 359883480 1250 359882230 359882251
    0x2090a0b03070219060b0306161b0308040609050c1009060e04060b03040222020c0a061a03100216020d0f030806010318030e03030c070608040c080d050904150824 71
    0x60401402c003a41d9256104190202540400c1070f0408001180e0070a101403031003d41103500600b00503050300c0310144c031030350f01d07400007014955801c03200664080304000c2950036407140135154075281c0302c0c040600030986083e102032080c21f00c00070194072100c841c401c90b246560b66440745a4203143c0c0c01045210524a05880340d42808003e06c50039401e50112604030390704981020764008040140881c41005698203601d85101003414040180040750b0071749843e10509082003080200c2c1016100e0000c90000d05405074081ca00140000001c0d034000c00701c148803101348002111640d80040e250001100044484d01c040c0200d880806800050813600408242002d210030b1140c094051015000b0f04409000c11501149140003a00c0c20700444001c241c4d0700f01a14004c689030417024100390010780317084030200a80740c4000b892030f402007442c0428900643d80c4a1910001c4020800540305d842c241158489040b0743c0003490010400105142d4007219015100181320201d43c0f030001d090060020085 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 359884730 1250 359883480 359883487
    0x5091e1e07060f0e01030b03010203011710050408070f060603050601090f05072a060b0a090b03060112030e040c0e03100b030d0e10180905012601020903061b0d0f02090a0b 75
    0x140e03401c031a8240080c8990304d0040ca00540220049014001d08000300360594800030000c20400d00180c5580d4888100303904442c02080350000c034508480c81201e01a00200091080d0302c0010941c1c050002418056070b0040354968070707526228204030f000e0340103542d038541c0c0d0384200036844c019002d0945d003d03031a0300308804080a907030302d5020301255040f0500100101c0c1802c0c00300b04403c0c2d9100920810014000150380c64807074a0501c02082c0501c6054480e100d21800083ea44075886075000700140c0c15511000d007072500006010181405a80440601041c4d00d125401d0740c82c200142ca1180300c00800100349001100309250815000c0305c415420401150b8846030241c0780c41002c0401035003a4600031100030314201c0b21901b5a06182c0110303840c41c0c00d0100010b05448118200d900c5030a881100c0685842d6401c01e1900702d2240c0305115805070880780019004400728a559404011583e40d003514001360301381d045e41240c80059890403000d90116118186080c900d0018010f01003001d401c92030b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 359885980 1250 359884730 359884739
    0x30718050a18050d11011113170d170612010c09050f06131a0f04080705101d090411030a030801080f070e0f04020301180303050a050c0a05070605091e1e07 68
    0x4890002a405001340005d0b040c1c100c1c00c0030025404112a1003201d03100315204c0c40140c11210660b01180b140c1401c03505a07903903040a084020805000340e405985134082908104034500160410051290b9072000d48101501481d40080c01011200c460680e01c1030b0149091000b04605400b448800d030380504018071544141c2c407144041d01c0292403445c088000c100b1202035140003e0702c00d0441580420380d0114000031200d03c0007038005c007691011100007a1803844004c0442d802000ca10800b82000060702a140e2141400d50307001c1d40150084995100f40e80d0302c0b901192400034005000c60000d800400100481101070141190641c0584094802985071000325102c4940180c200c0a0321001c10004c1001c55401358842d0f88400c088003000c448a00311810b0143c0101011550500903508050000340f034159a84104e80303204c095615600c5c104480c5480b03420042c10001c103580554410304050090040056008003114180c410040804c10b800f0b15903c1000c00d80b1001204055215080030b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 359887230 1250 359885980 359885983
    0x50d0617120c0111120103170306150c0a0605011509080c06030402150904050408031501170112110603010b0910050307090b0309011407020714010507050303010311030718050a1805 79
    0x1401402400a280c1e100e0002e40c2240e801021400f0320b00805131000074a02c403c0c50040420b0740c0c1224054400700c090741c21a0032030541540305c01c0340c900d42d000320200d50081c642c1e88044003814507086004101c642c2c1c2e041079541c17901100c1007a0400300d0170300c5800805244042d4800303245006000c1d6040074000d003008a070701244c06404013810003842082140001180b0601240954080700402802440f090500b420610099441900d4406171820f901d801c12a1550003044201c0305d002c3d105443e46016803801c00009426040020b084803d140404c80344031b002d6845038065400303485250501070380e4403010001c10010040386044d05041c040700b4410050042d80003014107080300d055843e065a25a11041402c1c010903d0f0000595915801c0060140303e0fa4001f51071400e981d840c001d460407400c0c13110700660310b0740a0082c00501681c0208010b00c0010101c8a40101c40320020302211001a210055015070044540384861203559a10030060054403d00900c042114a0700012204143c0c1d521410f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 359888480 1250 359887230 359887243
    0x21c1a01030b0d390303080906061305070e180f010f0311091e090f160b04120c03050d0c1703150d11030a03110f0d0203041a130303050d0617 62
    0x500204a20070f04c41e000700a4030810b0750700302c00d50781886060400c000b401c0052160726030b000550001d49441c0014150200c00548036000c1d65004003800340088541c109400903100c001d10000801010161600300d545403e040b01c00c03c03800791000303100145400e1200085210381640304545060201d02c080000c507100c4e02a25103450b03810b84500c10183c2d588010395189500c01c24054a25400a204021003c000803074528084601c000c00e03146d500c1c500ca6040ca13140715680c06100240e4008100c204459180050a0403907d0720030141019600d80d66202c690034406132140c2c01c004120340341c07200010044501141003003000701d401d2607400c45c01d000c1809580002e600e0100b600400200054400340803600300410340c4501d0090444240c0f6000c2c2c60024a8852070500440a9120300c551400138000f0109044901d50b40e80d034002c506046c0b4104c41010001220a0306a6840c1d004101c141c45084d21011444040c5000e5120340f951681c0b074111031001c8484a602440890004241804401d200810700d03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 359889730 1250 359888480 359888483
    0xc090603020a140f0d05010501110c010c0c0902070503042d1401141c0b03032113061404290a09050c0901080606011e02030301090f021c1a01030b0d 65
    0x103072500c0d51034006968100c50703407003c07208012010410b0020032808100500100b00d030440148040e0741e0b04c00041d02c05030004290400e0503082442c6010b90303075105c1c600d0201c1d1140142e0f40c001c0516919200c400880e403080200f5619070300005030520001900c0002001d10b071003e01d41c42c5001310306411007420031402c240982101b803d04804201d0321a813080e074000522004604500381e441b60341d2600e03200d0f0000d24240080415040c4916405a45004002e60b14030705094288201c80707880e0440340a0810000400c860240d4000e240000041020381c442c40401d0356000c40104010b003041d003007130112540100e00c3d8a0221015603501012250310004003030b0046203aa0003c1484481450590b00b00024080029003109a6400010b00f40000181584c01001c0a8071a40c510981203156110485041d0760b6140159000304010404518154001420601c441c0b100501b05000c09020300004e900c484405401c0350744545040501c0800c3c92603c544809003420104000301021000c6030050702c84a50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 359890980 1250 359889730 359889737
    0x5031204050307170c0a14041a09070806030a0b0a1d010203102102031207110904050307030806010c0203061006020f010e100c050c160e01060e030a060c1803060608100c0906 76
    0x1320044102420492000840b2001304540d1200392500d411244030045040c030350748540e0400c0a401150081541824140300015200d005a5a5404000e5031421005001c9039094400d62507004086800940d507c0e000b01b80031803001c10351106183c02c407544800005070520543e44104140890802c2c0144000100c4030441031a0306400e109106041e551f0b81200340194160081d00790411442c090f0303c0c000c01d1401c0c401c0307140280380d01426051280c054811900100a0303842000030602081c0107104031940814149442040041244e0100b400c0c040b082d40d82c094a2007998609011554042c00301c0b00301c842c0c03440020400e8500e0302501c140e44040c4010385083e0b040c0e8491034502c401e40b04008a4841c40c03202011a030440038010340d401003810546c0724203a1140d40010000c00c0e080e00c603080101203841c000700180b0b0182d80c1b585501c00103100d600d194400b0f200c9803c0003c1a1480400162001140100c1c0d0000d1a107103420b1004d800e0210715410346180c0e5140404403008180c003c203003e020344003180b8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 359892086 1106 359890980 359891009
    0x30605180c013009050102121609030201080c0d020406020a1b0506091c0605150102010e0715200a0f021905090a020d0605060c010605031204050307 65
    0xc0e4818001a100d02d558a40402000e04840f40941600301d034400001583c44008220348480c8411902070f5008156485e907681c0384590550300444140509519901c480f4006061070341900009040c0b1a850001c038102c00806420341d0b56000210b00c0c110742d51030310b0f148040d40e01d0080c000c0468641c0d00b10886004584c440440c9041100d1000d07045a0030010f1020402050b81c2d241503424100b40b40c81d0003218082882e03401910b005422080814092000304400242910a131052701c0603940c1c80800c00b00a01000300c3d40d03c000ea078695181031b20500310003800c025251083c80c14410302034420a10b03080b0a00c01440410354402d8421102c007464000d100c0240384081e0503e21905500241e01e50004240c2c007155001081a103c180100081c001d413a100091055000940d100d0302130b139568082441a0b050070804070190b1844440e04074113051418000a540306250b000d650f0b100300211 = true := by decide +kernel

theorem cover : BRFrame.Cov 359712230 359892086 := by
  have h0 := BRFrame.cov_init 359712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 359712230 ≤ n) (h2 : n < 359892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
