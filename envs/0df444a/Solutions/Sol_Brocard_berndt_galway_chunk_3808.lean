-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3808
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:44:52.838564+00:00
-- url     : https://prove2.me/submissions/4e92a2c9-388b-4181-b506-33f7a1e2374e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 684712230 ≤ n < 684892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 684713480 1250 684712230 684712261
    0xc0a090801090f0c0b34240b0603040f03030507270f170c04052205030c07050a030f11040b1002030301030204140631020d090312020a0c0201050c071a030901051b0909 73
    0x7c001492080c030020001d4482c0035803103403996800d00304010708000801000810301044070004c00c0d55611030605000a0301c607411168201d4040c1c201702040018006c11845030040080d05a200316100c11700802c0a450a49103480c020407034a44150701a14550b0b0b03c1c25155846c600d40755008035202c4011508021500f8240403074590200291030342c03044c403840e20544aa1041512031014803400002080500e010b01640e411242e015400c901d4000003680c80091620268068030b45c4260b07241c02c851000d4a034482c181c801245294069940c0358194410072040f502e0103c58034900481e400c04102e00c03501c1c1c1603110084102502a200ca01601c1c4641520305000300714221400140003040001c00c003000d175040403140d18826201c40010194514144041f4020013681100050340100f400c0c026500800c0201041490700058803203058480301d6005c00100e0900c5c80c48244803002003009032010003803040c690401321002080f040440080c0c0e00380028051420181e1250595001140611201c1800c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 684714730 1250 684713480 684713483
    0x110d0203030703020d0e090621160f0603060b16020d0f020303120612011109100203090603010b13090c1707020102160506190203010b030c0a090801090f0c0b34 70
    0x1c881c1d58203881e02d8001e444191048000c00815205403148602e4900b04044a00c1f41c4409455003098810b03241c2148481c8070036081c01d01c094064240c816035503030100d42000d4040c0c0107041c0c07a19040c501e4102d004007120319036401039114003070a000c0402d102c03800030042001e085c0c04441a900018881c1082a101c003007d1030005d40c980300015102540c081013080381480381804a070b0000c0d006013a80041400c0c3ea50107002240c1601c8200040300003880d1108421944135114411241400840008613566600a0b04507011022001c10314628071114a294100541051141802545551400601f40c410300265032401610040e0029038200d1003541a248802101b4200c151400201e00700329441700c0e0141d40107045407070441209020ba000d5402203c4c102c4100c00c5010340f941e62030740c030407407440d030400e4a41104120703454500003003000d400d0169408007402640d95040903541d07890032078503128080c4e106001c41c8a06206100c805043d01121600022816100d4116000f803200e80b00781c0c000a0300340 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 684715980 1250 684714730 684714733
    0xf100608251d180a03080105011b080309010501050f01050f041412100c1d09010513150f14040c020613050f0706030203061305040c38091e0d110d0203 66
    0x410840001508441a00948003040a140c00f82041e80055449015050300a008100a840104141d5100e1603110085004180c01010880c419990704401d0750b009407000580faa440b1001400140703407407031074111018800d003400b924081d12146c031561035009620a411360850480401c00c803c0e1070703076038030034003034000c48000d03540b420140c100240f00030900c0c4841d290003e44442d445501d03600701005c041c1118080280103420301d03841c1c10108141d1045800f43c240600d6118625070305420401448000580301180c40882e000b4180403c07501c5900f080e00d8560320890a1401c81e103220394000c80d803e50001c80f8282c072000d200d1302c5420461314103545400c0d1014580300302880050350603032680c055800317a901180c80d542100c040d0240d031816901c007920b0103480035003100300070400f0905501c003081005003040d043d00c0491080030003400900c4c4404032214004400040c840f001c40c90040c00d034010001c001180840b1814401010604c018141030004004e0748070519109444d40d10b141d0759110940d402070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 684717230 1250 684715980 684716009
    0x1090e0c0607060912090b120c0c0a050f2e05100302060f120109050105150a0e15032d0105060a0c06090c18020f190c140f10060825 58
    0x603200d0004c110b00d5005a4840709600805100141b00d040000d080f80e03040441542007800509002c000008042d29001901004010041a64801b071043c2c189650082c005441441c4080c910141050300006000300090030814403020007850a194048034078204a6000178143e440104510602d480d0341c0000c1d40c8400c001c60341e10540220711008100b090340d000103000b0300343d0f6203800c400c0544800380940ca40c40040031243c80c1042d03403294080c080c56400f07481c1480a19040703001050302c036210303101d0500008200100300010350140c1844050040002c116602a1140c005010300704040103024551164400041203004107105401103160709805c0035080282c00003d26000000680300d100b03840c501040180c0d4403460404500c02c1d80c4900340b50001c110725003850b400110b0780c82d81c4041c0c84901072102212907480412100768145125040da100100500400d40d590107141000d001e103a15212414994140b101580c040750300724002544280d40200303a18a41000400303c400d60300030401010415 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 684718480 1250 684717230 684717233
    0x4151214090d0507050303040f0f120c0618120807050c070e1501110d0509120616090801060302130c02010b13060f090504023d0504092301090e0c0607 66
    0x980031070048030003400321103030507540c150191044c2c05018030140c0550400e00004020070b41c0d5180c0b0310320052161812800070280d960b904030031040c0040d88000017030f10a210100c01c2011510800071101c01c018080700b24130740241d440081103140c448042041002c0b21021522a44c001c0c1c007070b00c201144d46d9058480554a8214000b0034040859041410811050611220394040c0d04000287c03c00600540105041030000765115405007003000d8010840b010402c980150507c60503004c3d407424209510308980d143d0002700304000a420004103030345416020001651000c066980024410f980418004000b040c00e17401061500d56141c0c211241c0d16120100c2c0344651321030800e07204039241100407940c82e0094030084950440700250440064903121034400c410802241c0c2c1d01444d41031100740e580c01000410034070701d082c0e460003000c40c0c800300702070001c0340c180d0181c680310303c7c82140d217480402480491481403a00c10f00c1075005940d81d61540940c0b141040c0000d41034040c0241121b035959100d13 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 684719730 1250 684718480 684718511
    0x30c1707060b030c09091c021f0c080a0203012709140f0106080c0906040e101112011d07080411100503040b0a0524060904090602041d0606041512 64
    0x442d10344039000350007188880b4030301502080c0c05500303280c004090f400d00380c0b8010301818110a0045c015032080540d000800d041c000e80b825484044024003045405403920080e01c0c4507800745c02c1c2c001e4a801071006100011f40411f51050b03e84181364200a24003490040600818258101804800d181d070600c204110000030455198544840200701065894500c1c1e82c0f40c1c01c1c8400a503a202c0d003c1c1c001f1174018605a000641c6402c4244d00751080b0490030070f44202100c1000420540f60300740801c0d081d15102803840c1e042e00610b007034650340e01d54042c51010079030122001401c06003882092004601404000540f80030100c0014201c9810020780040c00f51031500102e0341150b055040000150f02c0e000507001c0c090090002d10500100b0b020001d0006c11031742c4130010100d401c21030a0069003074540d1203000310b0340c6d61401880c0040c4c1d1075091407007104074008003840e001c02c00303000103042c8112900d071401120100ca00c1803041042e50051b40701c08450a5030b00320000c5000d41c1c01d04e0301070203c07004c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 684720980 1250 684719730 684719741
    0xf081303051204031a06011e0f0306050a08032d03070e21210c060a0902090108060c07060b0a0504090b060306090a030c060506060903120703032304030c170706 70
    0x40c1e012074102c0110985562041d2081c0e00000384400400381104942e076010f0448160000303014100700c441c44449000c01e10064150011810008240766600c1c1c0b84185c0510544001e40800c2d0b41044081d410102030707036a00d100c0c00ea1001c07245505d142d07507101080154052001c0c048400030380305175070f424910001801011242c444a04c52843c9100c00340800354005000c0d9110307405100a040341c02c010f06c00a1f051201c1074141845680070401101c04071b1070003032080c1d922034040900c5c0051000a50700501c904000140c0000849030702c40c605101d61814010207480d00182d100b640410b0030850000410b1180a180c0e0101d41c000f07003040076034020031101609152007460142e0455829070b0300c60f6903280c0e5550703407040041d01281c85207000c600412401d80016504c07103005001103140c2144100420f10748a2000b40c201481500800c01d035040560601400c9002e48000903040304001d1042001004128040c20003400e100c08402113604004c10402d00c920340e65110b1144a407a90041d050400c040c18 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 684722230 1250 684720980 684720983
    0x160503040e0109050f011508150a081015060801151809020d0b27180f15070201060302100503090a140102040306050c0f031b0705011b0315030b0604090f081303 70
    0x2070501c0e00180e11704034020748640c102e0711400c4d0360300c101500d220f406640014004e8044120340381ea02e01c03c51075603100c665122008103e1900201280c0011240c11411219032642400e403ca090040821500b5404805c00d41036030a0703030750484001e420341c0c1d4052303070324030101c0c0d42c620b503981140840052340c403aa81e0f020300785a82e400301046c414900d00d84100030950517403041da0703c1500f412843ca81c0e42d010780c10301225400403032184d903900c5008407180700c18500740e001380e2020750561103022890070150680c90010341040300ca000911109003940c0c00280408101c100f11002c0100100004502080400401e43e000d41c2062000090481d441c100741c9c043e5015010558805080002049040c099030b4100c82174084607500303290840d102d1240d9203804810482c903c111082091095030701142c020310810b4900b4600c543c07454404101c180010b004d03681112074540301134510281c1000401e00c50000e195009400f190001128585490444101c880d90000641000e0010600c480400f01250a9200b601e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 684723480 1250 684722230 684722249
    0x50a02100c120b0f210106210c0f060e120319021e030403020f0609130507050304060e0d02100b060c10091e11061b01050a090c1502060c160503040e01 66
    0x10070483c203011281003c0072034140c00125182e418040340c08080300c03d03449000d0007000455401e998551030303901024803040c04030045d244031340400304001741c141c029001818004400d070b145500c1c108014180c680d41900c0346018082059180f10601c100388100c0e0a43c10480e184480c03400c4081000951301c4800d400400540758051502c010200c800000340c4040f25401044804d040300c003002400615006051000d13002031071056002c108030300c0b0340210780c4100c100d1f640e01d507224030305130a142c0107031043d0072208051908000900c1c40340c3c660100385d544c4441d21a2001003004801031010840500c251070350001e01c0c1c090a0403030085032803190014603007207000b000b560385c001c54406000ea203e02007454000344086c440c52540d403e04d091505c0030f01000c0400050416058200c03040050035035034116112411a0369500310113007001140203044002d030402e20402c05506080010295a400c4041c0084540510200c3d12400032130f06501402ca02ca540102920b403103540e100344000702c514081c01241e910303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 684724730 1250 684723480 684723491
    0x50d0903030f030e0c040e0106030b1e10140d020a080706170105040204060c0618020607060e0f010b10110a05030f1b0a0f030c0204110307110f0f0a0201050a02100c12 73
    0x800d4030130b0060101c19450640a45030492500003040020041074014040701d540700c500010200740c1a140c1e46208690b8603c0c0e01031500e05010852510400040c9615801d0320803510911500141c84c2030084011416145801c102e5034600000314a919540d2101d8401d200f44807010612551240c1d4900314183d001d0514042d03640c0354420001640164060079001480948000000c40c0e00b50700034000042e441c14030480740c0d9510313401091490307220a006584468030380380300b5840d9001c00c01480350f00f540e030390f0000c00040c014070000031700e6080744820440801c050311400c1c43c030400c81070101c80c84241d4801c080381d603651410f0060380030980111503c0b80c4504510342d04182006000b080c0f07061030980c8203140a030320102d15a0191850031410340c0690700280e07108650080914580b00642c09441c01e0b0301c0705020300e11b62405080c135129080c1e51030f0141c0c0d0010883c20844c04000101d0095090342401c000780c07240c0200d10102d1804484221a243c00c40c1071881012071180c00401401c4001d0004000307010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 684725980 1250 684724730 684724757
    0x314010f050a110a0c0303020415030c08070306210c0504140708010b093007060201062102062d0721020109110415030b0c0d050108070806060d030309050d090303 71
    0x11140031101c07030440f244080110901c11403046440c00300441c8a03040060505d5120112901042e000d440c2c0040800e61320182000d085800502c1e956000c5141d1070240100d40c10045601000caa010745507140028442c070140d001c21000c0c0f00418003030036000c1c0003085110b000840f54544008241d5161022604510020941c105480129504c4c09030240c05504082c0104c10590403c46e40e1152840c09030800504506400c403042c0502e4004006560002c03603154142030319403180c10144882102c241c031226516600580359041654110070700c0c0415000021085506c18a007480c1502c140c00c44801c0c0060101c080111443d503d4001400b8803a00700c00c000c0903100144e080303031035444001d02642c8190121075a1803030160000f003c035050561440180359925501c00800b80c0050b40c0306644000003003002104d160083c4115401007041c24020511186840300480d11402c000d4005409200d00c13103407410605029410038a4066030007000ca882072620355100620f4041c1c3c6000840009040f20720000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 684727230 1250 684725980 684726001
    0x11061509010803120610030b03031b011b0c02040902030a1703040b0703021c0c0e0a08061503010204061d0f0604060201020a02060a020901090e1312050309070816030b100314010f05 79
    0x100c1d5044c02e10050b21194072200108407a0598951001003055101d24500d4401d407001e1003c0e05080307406030030000e1100310340c052060948000c41c170040070f80c0c80302021a20301d01c1d9000d600c800c5a29010355000805400c503001103403c0160030f40b4090080b004580010b04017010080c011031046020718000b00c0c1da030300c0300754040301688940c2074607501540e14a42c2c2104101c01e654090720501400781025001d2840403c007144680d032603680304d07071015049482040710342200745d030f29000401e100b01c00071440d042c20800c02420700d100c2c0032400088240b8500b4007034044c1c0c075aa607031058115070040c00c42e62900d1303031044000d01079800510301c01300500500c80456040301c1507000740d4a030300c10140c641030001c0e41005100303070181a0040c000071495000d000ca490126901403176400c800210307a40d829a407072030310400652a18445901021007688441e90340350841c0c920300180b030705507940545102e8203a212890030312180401500301400241610010a02454056100461451201d24203111999030b101044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 684728480 1250 684727230 684727237
    0x31b031f05060f040b090406090c0c0501050c070503120703180c06020c090603120d02070c0303172a0f12070906171510020f01051914100b090111061509010803 70
    0x1208041043c41309124540c2044080e00d240c007406000040c010303a4911740741c01074072404170610307003c18003a0404d64140102030113a984d2041c03009100c28a0122543da4080d40d07481400c8080d030b1070329000c2c004074104511940118151022504104203031241e10304159a03c8021440307820058412000700350f8480c00c0c00304156100d480e00a0162135030300303001202c64040e5404649082102d0342e0820942000a040320100340180d03000fa03686044e81254a11010655080030b0003202001079070045002c2d030000c40ca0800c806001540d030b803650b1280c0340c903940c01c00c4a000b10380004003482d111408005400c1e41c40f982c01412110369548000c68401c040b500c40e80c0c0001701f600e98801d220211030a80126045c07505e03000642c1d10052040b40c100100300303422075007101c4007601e002c40805644040d85181b010103001e40110401600c0200a07641441305481c0320105840c414100000b1010400c2082680180302012405201c0070a880c030b42c1c58810101410069801601845903061500100d80c1102c0082034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 684729730 1250 684728480 684728497
    0x1d0309062505010c080105042d020d020403050a021008102601020d1401150503270604080304020f0117040b1008100912020616140f0f0c0601051212031b031f0506 71
    0x840c80406d01e046c100440080748546027020890b003c1101290b4070030356100900c01580603030081c110351800b41c81080301300d0904c01d000004115a030400d00c12000c00960018040f15804150035000380b050035484208030f44201240c2901d541b001c13941c1c1941c0b0a03950040108190304005c0f0b41c865030b880e0301116100720682038040c0001202400029a400c0ca5000d07071800c00115614880f000780c0105003203a1403e002150219484240402400110b00701502070a00306503003428810314030000d50500c00180c0b640104040c20002075a0045500841d40d805040040c2400e10143c460020090700d000019102242c000c5540351648441c80001c1744c800f156a5020b0303003444924900203502a130b000c51b49100b0740424078030300d04030812011280c48074883c0100014401c0711680d0340c80302e007403803402410034005074403450086601c141910940b9401050926820401d11011340c0c990300c2700c13407240c0c408400203000580b1540002041c8400d002030f04c84100350b51644441d05c88000c41d1184140f040c0c50049040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 684730980 1250 684729730 684729761
    0xc13120203011b0537030e1015031a011a03130c171011090d030908030a080f2a070c0305010e0717010c021e0c130204091d0309062505010c08010504 65
    0x900711024403036000840310074004403c861085480100b88230840f1503444814448801701c4078104104151300c0440b040300b90321640805407031762400d04000e0300e80c5040c404110b45000b0001c0001c0f09050840b40f00c0c0901a08081d28140807501c1d040d82405c1d085460101c08450b1144c45007010b0640c40745c1c0136214420950340201070400300e00074240084a0f201742000c80a024032000702096803601003000d000d1038403490381d8a80e41c0d403c04141102d4600f01c0502000d542c4149244a80726000a940c0907160403c001200d6603603a15190420180c00112500010480e50034409010022140020b140058500c60041e201c03141d61340d03404d103c0c00c0b02d1038940c0c583d0150f0407400310010b0030664081280c001803260004d036010a00681d00040c4072030501c1684045140c4e01244c02d0001c1d000c00d02c101a200505403a80c202203584140d06580c0d00c1c0942c240403032185034006140344400303003120b2840400344611640e000d08000b042c40c115010b029169826030001e0300380c800005141c981405201d41ca4081c1c000b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 684732230 1250 684730980 684731077
    0xc03031c150e09010617010c0905060a0e19170a0308070f1e0f0201060915090207140a0609060b0a06080703090516030c0306050c13120203011b05 64
    0x120140c01900303104501c46079141203440d00190048034070381d025110307012980000840c0707030420091140380e24202c0302c903812507858442d09029440e0000c00880554008540d141c1c3c44114806040315560040920340d40c10022180000c440b01d000490400195991143d003400d0201e21041d1450b940d9001700c4001d0002900c00c030120300601e0060841490740c220302e14205440c2038200403c10718481c01c000c103100003d81000340110740a9270a105100180079007080601c9944e11802d0541200c0c0818041e580c40c02d40d00180400412020003000740320f1048038405d551072003426007041002050021015542541405104100d5151100104094400b10b856403d015103401c80202c00408101100300c5942c420881030031580c4120031001d034011846684910510382c11468050f068440c0603000502080c802d00400c4140510010740f1016903046400440b5009090b0000074007404c0c40702e04c810740b4825002c44105145a1082c011711030b01011000d00c9400780784194074100d50b456041c0c0268a003c4840 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 684733480 1250 684732230 684732277
    0x3150f0a06170c2b1d0a0b01170c01110115081f050f01090507020708120d0e030306090610030b0a090212060a08060a0903030b0604090606020706030e1906150305030c0c0303 76
    0x1150759880b1354000000002c0c030b003081040103c003481c90100c40310340320383c1c0480003140800c4092a0128090510103203050030801007032078125940c000c4100e1044c14000ca042e40a0300d100d000b50b02c10410f044481c0c5000c1da00d00c1d40c541803d51500041101d810342101301da6039030b411868460041d603004494031024100d01d0380c6450800d000420010740000114010003100154990041100c03865503040541c403542e50b40e40c0c0c3c070511000c07580c1c0c070300550041d0340062042180c140c2d20242c2040d07000c9010b40e0051041400958102d009026000e5102d078080d00c600c1002c5920134881d40a800c2c02c80350307910b01406c0c0b5140c0800f0405e54403083e2041c4445070340310b20001900300205400c1290a00c0c80790134003003081344480000134402d0300540c01582895540b080d0800c01d256042101c440107043c1400c040104002030020720707454501304c1e4000c45800b4071400010003000300c994080400c8103c0384415000c01070300c91602c15101c0d400003a1034112072181325441912854080110b800703000d50403200000c40c1c040c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 684734730 1250 684733480 684733537
    0x420602160e040f0c0e061315050d1403040602101404120e040b0d0f030224010306050c040b16140304060912020612070203030a05070c0803150f0a06170c 67
    0x3072003101d507220318400c01000034070750000c00005031045d480e855626103031280501c60a01c0c580903e440305581071491225074144800003850540d0000da03880c0b0b52444a0b801d16503d45000c610b000201880300050005040d40d010901802100381c410341448441603000300b80440355410344000c0d0042e411044030701e00580c020489081035840181011401c1c182100000320610307042481512003180700c00d200d01c1015414403040304140a50b0b5003031015001003954201c00d072941400003e085603982c03c08a16860f580c00705075402018100300d000c2e075403110704411440d4004044070440e0a2215000080b45031320000c0b090314107440307165480d028118034042e40c500c0300d0f422510080c1d0b001101000120381c03505920070118404e40e0310303400455803410701413040400c071000101908100a19403610100041e0007030200da81100c02c1044426100859100290402d0064044e06601c40720980d8000391081e01314204c14003d00d44018454010341c0d80411414403071181006005103903216400300184245c2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 684735980 1250 684734730 684734759
    0x302040602190312090c140607170a090e040503070c0602060c0702060d060b220b03070806040b12190b06040905250b070602040e070314070342060216 66
    0x92511019540b60b84d820350045400c1d043c0f00b554002903401041c400a81941c400c2207504605584451404900b92a400c103010701c1e07440810300c103460020715514054816000c030000791001c141c0c0304010b810070f0300e0015070382da016040c00c40b01104c20784400207449002003030041c8101801d5403a07920b082215400c202081e40030700d0b141c02c0310656600d00802c61900407409040090f240418000c1d00302e800c15401c14080e1a40d07803001d01a80001c208000c070499020001c283c01c0740050f0303004110516130341d002440030941c140603800140300f01031602c018166100e641108081c081c804410898641030700340019580b0503803029140c1d50000c0542508042c503808812403061151140046050700e034801c0c100168010303c41910425008a0107100c0390901510300c03078110010303080410100e42c00a040010f0314000030050414580c0c2c4540044140d004451004090200d081507920484009580c091101180300902c6584000b80c8074003103030550002502d414401d80d13a001c2c8240c400d2a11004041e03028 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 684737230 1250 684735980 684735983
    0x20d02071205010f0c050405130b06070821040302031b01050114120304090509010204140108130615050409081201151409040f02120a051b04030605070e0d0309080d030204060219 78
    0x41da144945139440e00c0318451905c00154503070700c05513150310380400c202c00108461318120150f0b00c0d1010084072a541d8030121341c3d042d940700203001d0720345407145c004c5450316100c140c01444c0200c0c4402001b0400d80d000c03000f095101152000c24400c2010000c4540c01c0f1a400d0081680d03010040e25910818942003601c9410040c07102e003201d14190b11503101e101075401c00c5e91181325582d00410709203d01c1d400c18040c81c4c0031450a280691841c90410f6902c024003000d01005410655200b48405182c00c0c6103400348040c0401510a2094204614201c0d4090780003880d0b40403c0c009400010a103003c80300414408031340d01d5940c03941c034014444064010f03540544030b0660310698800204403400c841e4009040d601c0c001032800380e154500780070345100741c410040981c0c034000b50000540c00120481800d03103013560b0700b00b00001070507521400180c541008600c0035550180c441c10320b00c0101688010014141c0d4011301c01d0780c400b201400030039400da006900a030400740c3c01981144682d070111204054100b03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 684738480 1250 684737230 684737233
    0x1621020a15020417061009020f1c060504090b011a0313060203060a0e0f0901150501170603011503080d180c1413110a09080a0305042105100b0907020d02071205 70
    0x190b80c2c1c9004000b201c4800c0c0080402c0e080f08041114006d41c11403003100516214200758949551007901103407d204140c40d0300120700c102d1254041c40350442d07010001414001d801000080e0300345c1002e4040304c40900c2480b104c404803961130845250400141c9000d00703414880301d44501d2039540c45e8806500018001c0f500880b80b00070006010f0301c5250124080c00301c0a10746005030030032100007429030328104103000d81011603600801c041d0364460700c00d0100f02c1c18480380841c50303112200024090480100c03a811715292480020050024040040c14500300743c1a003013010198528101c400001140f00240410390000300070051905401e81d40925000000c041c2103017580e41c601408120356188070101e1844001058100d8000e42060429003c2e0031108020440b2480550b0000c0c818030880c010381004141445d02c0f04607601000c103c180d141c50b0b0110a690307400c903641440f08010024000366070301c10003801d804500100d0000c03566440b10901c940c05070900724188041c41480c0404910100c600303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 684739730 1250 684738480 684738487
    0x9060d080f030411010f030c08070c030905030a03170f1b0c2e0b0906031222090f050a020910030e030903031206030c010824151621020a1502 62
    0x101c000e01005510661051569003000c0781044001020340e9100c0b8444824545000713041da1040d81c00c40280d40e84410149012005902d29140440f0035264075800320ba010b102e601018410181c0001004445040c030103600c80751691010f00d241001c188c1030301c02001c46a10409002540b0480c0303401468988515030440e014541d514402d50488046e0b2060641104601c40340c1c440d101c1c02d140030b000e10083c002c0701c8140d400c0c1805c000090700d500c8540181c81c140d440001c0d000b6001e03503500000303004050031a0040d13046070303503100d0400000e800744416a030740c107a117000c0024882844601c04c3c1c6d00d810384050018110b039481d2003c10350092800800303070b910314031060100100c20740d0200014042d040c03411400021504020041c5071820745164401070500102034200a0084072080200c40002000d00040304502e85423004120303100610201d12038000f42c00906820540900036081038040d00c6004017034880c0c1c01180c00001188860040e660042c1c00c42120030340410144400704c2c0342c1c1c9401d240c00514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 684740980 1250 684739730 684739747
    0x316022707080105150405090f1b0c060403090501030e0c0f03030d0e011407020a031b030e0405010303021510050f060306041103161b24060e010b070c0f0509060d08 72
    0x3020115064000200c42e8001480241403d17085082800311000c00281401d00740700002e0501d000040203810043d03c00000603a141607442405003114001003100fa6880d81c081c02d10781d80350042101d056001c10413040d03001407a5407080c458076070541e40150260080900c0d00c4108180c021010350381592610050000f022040c1407489001500c51410000094142c2e0986140c00c807254010803c205540021480101094100c034040303010740400205803240d040c02d4901030303590101e48603109030498130b410004402c140d000500756807411030360303290103c140d9039191503610001c280e4010660820085c51030b0324400e04001014503000b0000810109119580201d00400b030b420440302c41d440520b40c080180b8540e5040324005540031031500348040c02d00d0542d15010307000b2500b28020131b9102444000b011509282d5489440600501103140409507560407213881140c10050094561483d48100002c032a908004004105c80c000303005040640d68070700802030490703403030002540c20060402a814 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 684742230 1250 684740980 684741049
    0xd02090a022a030705100209090c0c150f040201231c09021c0209010b070c23130c021501140616240b03011802221e050702031602 57
    0x6941d044040c000f181c039043d081c05d042e860070040203031040303440e407040104046030344900c5503aa40c4800610b0100d82c0e50b0043d00009843d0a6107400d46101e01000e01c1c0038400309070000001c0a001e207000b681d0302c04420207458424040e1000320154000300c175008202012140301141c58404c402ea0382d00340c0010b01d06c081d980101341d010007046e210000f9486403038100c0c000c519102c54041d02404600e4031840c201880f581d100d105551070744c02941d00e000d1440d0081c0005403207000c4000140d40303018003681c510046030f07802c0d4005040d030040b02c1d40c090700900400182121802d00218100c56070080e250001160301c4050040c140e10001151050503400e00b100c40c08190803030600c2001c9031000c056102488030420005085880e005106440b03070741807424000841c2d5090b542100310503011070380100c00d0203004100039010b4403000c80d06080e0350b0401d41704280071031244140042400c0480d60510156880c01c404903240d204410441003888060781105c409810800d07009a0726090044031801101c44040220 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 684743480 1250 684742230 684742297
    0x10020a02120123040309030f0f0614040309050f062703030703090503060a18121b080405130605090408070218010b130503010606020a0f021c0302030307020105060d02090a02 76
    0x40d103450b03440700780300420940308000c4000c0403264450642c3e918180b03980c00400c401e0840c4809440007072480c0d008018426250142e903803071036100381c0810403286000f640315a409401c0705c003074000c43c030340480029650801e1102c1c903418031001044140b0301403d510861205100b2500c07052420140d5000c402a5500c0800040c04e46a000391104003156103031004041c500f0400525881160b810403049516400240e4114145540e002010245181d480b100448014566a500c292200d008402c02402d100c0800001c1040c2c600c161001021041ca0341d103407400752030385440342c80e4228041c0400140442c1079800a04146407005002220880c0d00001c00c4c40213950a0300088026800028150000281406000000d280641c02806401d25090f030103900c403400500003070a112884000c207402c541d2180096a142c0700102c5001410020a0900030350b2500111440c0000d5843e060204040f40b038090b0405524550051000f5103540c2e800a201010750068402d40e00c903160b0040110748400880c0000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 684744730 1250 684743480 684743509
    0x1030e030405490c050d0827130605010206130c030312180b01080d140f0a0908011419050c04050d4403100b070212161a0a08040210020a02 61
    0x140d081c4030b505400c14480b004150b43c88140310794040d62006c0009803d050545412603601060035a520a50022400b800c80400006551005070118041e6917840280c0c041e10a0316002e03403c403022799130f507030900c4107011441e482c1c09002d003412548200006072150343c002d42c0050342041c011940c0c22384002d50303a50704520f8074001c4601c03551600c01480b080604004500002440e0318140724985451f1401c440c10348200030041a158500046100c2c4044c05200410f00074411030000700016042d43d00d0000c001c103015a1040c503000b0200201000211036801404d01480003182c045180914060800c5030004d10b0302000c80b13040c10b540700c150305200150407a8585401041051302e40e049000c0424402c03954900b8031041ca407034401e00510100d13502d1416250240c0306d50011803960b8000700d00000d049800f4401002100d481807612110b944082d02c8408002c03151003559a000e00c0301212032040c00c0c2e000308911980040c03140b40016000d880c0c5800c0303500603134009006468a00103203801081016481544 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 684745980 1250 684744730 684744859
    0x30909221101120b18090f1e0f0d141608071101141e0708040e070c150516120b040204060302120601020a0302070902181e01030e030405 60
    0xc1d165000d5030800320410892003010401c002d840300550025503078803506201c000d00c1c01d0304a0001101c5078070410617038400900135800c4404c0e6521074020034401004403070898025005042c449500c141e0000740745603004200f5100c1d40c0c203500c1c3d0341c44501c1807500f040204032880407a00082c000400c1034440200051805503149400c480b41140000d071540318080b0701044003420801c00520a803d86407917940c0c0d034111003044580c2c2e81c0641e040081642c001c0d5040b00404a103100203000f00c264008007000d00e510b2040121305100d00750598084210740085403105070a00e841288810392070b10490b50386402d850743c0c8000242c02d0340b00002103030032a0440e030840400320740d0001d00c02d407140c02e000041a0b07001c8001d10003070119000c16034000392103c0080c40788622a5802080308042222103c10700a8a810040c01c0c201a05840105404c4800b505102c502e01091900b000b04040e500044219016500054150240010108849030203083c401c45640500b09905840340c4a000c01c0e0340c40030124900d200b5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 684747230 1250 684745980 684746003
    0x60606050309120c07050d15021207090803031b0a0c0b13020414010b0406050c0705271b1801020f01090b0115020c10120b090108010f060e04020303090922 68
    0x1107509281404081072941c460f00c040c00035071260a00007491905542e8155012141460b01d403400d030036aa100a412640580c1c00803030240d0008100012992040c81d00350388009050f41d0364050940c8910040d80e1100f40d000101a0402d40d0060039801424020704501d88080c0685940d16090040304042e984200000054403101056140500070b0310010b42c0c031410681c030554948901d0708030b18855841840b0034010301251122465006105600c0240006031010042c10803400c00c4c06004145880c40070b80d0f80044c040030680640184841c0c036240428045203529141905c60403540703030b03410a41694110300c510b8008080c201c8080c09030b90700300c901c07540715410554146a09580069205041402158000d00c0c0a680c107903920390b0f48220400f128144441140403511041016160840200360020028400002c0482d0305512503200b403030912004000c1a034a8811054078010b0a44001c3c1d49584140140001480c01c410542e822410000940503001403e0442d4100903000800030b4400d0728114 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 684748480 1250 684747230 684747241
    0x6010e100e0f0a0b1608040b0c010504061410030206030c071a0103140d0905061e0c0d030e0a020604092415090609060c121b06020c0c0a05060d020307030204030606060503 75
    0x107600d40685400b007218900e0482c2e050400794503103070181080c0164001c0400e4601d0b01403040328401c0ba80074015194009613034a00401e2400e000e048162004c40d201894000109010111402c5080c01441c09074540d8000c3c3d442c40d002c11030642c00251090000c680108407600003e5031103900e01c80710900e00c1081084640c9141001c61f1030110001c4242c1030307504164030a80071141d2021a900580b01c08480c9a92140d00c01c42024994210402e140800a14009501e808040b00017a0021442d8103e030b40510804a9108003140c071800c220034001c5d008001400113201c0484140c001e81900521004a20030002210036245205c2c16554414926004400e401c00b00256000d031481c0b000d40401e0400080d180c1c900384000b420380d64001e03c0541b21110312720751580000d00c26070300284416104904440000f0b03240c10034a000754022500030146101d04803003500f042c1020b076071400c200e440c028001400c003000f00708a03902a51000702941d08142e403c001c080b0000350f0038841d40700508181e41d69903441380340c036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 684749730 1250 684748480 684748489
    0xe0d08100510170907090c08060a080f0c0402030405010207050105280501500a080c01080c07141e0d030506030304090b0f091305071d04060506010e100e 67
    0x1e401c4140118800e8400080d100d80203c1000f400c50502042c16841d96204800181000d8058001008030b03424440b05850b05c40e400b00c1c001e07000740c0b4211b50040203142d48600071130741e410003c0e40020141c4c00c0070480700d02c945455805540c2c020b004500161401e5816a80c0c2400c56034100c030744840b81854400710780709055080c420003840c60407503201004154140816201740464006820314918005628000c0c140f82041c0145410500c810703018074441c680003940729400d035080140f03c0c0148014840042d4443c4001081c000d83c40c010784a0000d0340d202e540300b0004030340c000700c0250b4008410000b103400b244001c00c0402c103400c040d81848503460b072020000318103081682c8405400c241c00d060900c40d181d0740101c105c0d4211141c2d94030000c1c10380707029000300f214280188000340d408842c0504010110304140c21089840e44181c06481d0074680b1040e10607244494409101d66050f150700000d4000340d410340c820b80d045101414610040070103007000030f00201d21309015a0000d80c15080d881040d050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 684750980 1250 684749730 684749761
    0x2011505040b04020c0115300f0213151a0324120d0e0108010e1b0d0f18033203040c080a0c05030d0509150f0903030409050f0a0902060a0e040e0d08 65
    0x840c44524500301d50540761030a4907078403e1101510400503203003110110342d920241550300180544090118800c88031000d07680104621809001c0c1cde6142c61031a0002e000101164450006007900c2d0901075003400381d411a640e8038000e0317903800a90b1085041342c5060100300d40f6640c3d10040e91007030311846950340010804401030380001c00c5a0350760313414042c04402842e10008407104a005150315840400c0490001d420b020ba402c0c0585840d080003080c00c00ca84030b48071105075001381c41d410241b149548800040816403105602e03080702074060240110742d20300045130000d0250300856806500d640c180d606140650000f2140082d2141e000c1080c0e082c144440e040001d0b0705c7c10b0840c1480c107040c01090110489644a03080d0400015844250155000680310100d00190440e0b1b22580c0f240b620707500422065070444040940c41e0005403c003203803401131200190b8007421050410031550b0003581c5e0f101310034640640c0719490314440b0400c00c000708604010411a55100300c618180b60510409522 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 684752230 1250 684750980 684751019
    0x4140c091903030c022b0c0509100e01091152030302160f0c08010b06090a0302091e0c04050f06090105120c04030c0608070f02011505040b04020c0115 66
    0x1c120710003080465007110140746070680542d02c040d4006055582e80300c0040f900802c80c1d10586001070408148440002218255034085d258404551588100010680614410070345d009444000600c90070200343c000c00121454915000e06140405803000301c08094001c10400e01c032078000c40703160403001c03032010340c042070800c40f84035492003124058405e007001c07400001505250300002e40c15091041e00907100817007500b200c0c0c11103041016180c0b100c0306c180c0502c00c40c0c0d90740d82804015445031038141d04403061113100902417102c007480c40c0d007400780103480200900c8a89043c10200c007032151400b00796a2081410441060313590b4184020000404c0080c1301c2c150081c0024003401d1140e0b42c0002c00c03102810306030b6500d81190350364062903903d01c2c45507410082940071140800104d9035007000c039040c003580300c644608501c81c0d40350408034200d6052540071081610718000c10400742c101940300000008003d0005031034826030100c0c007400d40390302440001d1501020301042061802c007075078100a00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 684753480 1250 684752230 684752269
    0x2130e03340507140f06190206011502070e090c040c030c030c0c080301170f0d0c020907020c0a09050a06031a010303080f09030d05060609040f0b0f03070602190204140c09 75
    0x182503603220190303214498021a030b00d00381c80e002030300b03660380e070305490304c5c1950400500103a40c6c1d0503804000101043c05031542ca001d40f0a40b400403485c0c60b800b640d00740d1400e0069005103222881d0400ba48460700e07001e800e403159406240c4001040e03450f280249455161661400b10f00082d20070b40060840b01e450501c0010030082240342c10005850700100d0341160100345521448002c02c0c000f55080c802e000504070110701c144010007805540081e900e0503c81d00880d015501d41c1d5444205984944660051540c030610180c01030244420540c4400c0e0800d001036800a042e80e01c90755110014030494864400f101d00202c010020540d0168a45501c1005c280808072a400e150002c83d41d82e000b80380300d80d68aa030300e50002034825103405040e6500d01c10000c0040c030032603011100c504010100701507007901602e200300c40751550b81030000b01c03081120115401010f0041d0304180b44420040c4d44030701281e00649650290b0a1100400d52060184040440b015501e4102ca000c000f040000c146038290310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 684754730 1250 684753480 684753577
    0x705011a0307140303031b090a0e06030c0604060804060e0715050c0d020c0102151902030114100806031b0607300201140a020d060305061608090105010e0402130e03 72
    0x50348010040d47c1d0010840108080040c0c0007880d80d209600031202c105030003510840c00061000035030b48040d8000c0b44117406803000d1a144000380900d6200701d02551000c0b1b01e62001050000d01c050340304000d81c030f4082090b6401540c5070b01425030042c1c1079074001000204041a45640c2d80320070720a8241c40d202d10300050026206441c000303920b4402c10515450603a00000000b16046c182c5ea0642040c3d9400315005c550fa5a128542022074089502e0b43c0c0d40034110200204e4419030099020300c0c015100240108200954564509a650300000c0180d03000b007030038010328000071102d2a060804080c441494a464050742480c0c80558a0310640c2c0411a8105a00d60048842050400741c0054180d10096500c41c4c0520400014122583c40200144180401c0014608802c43c035101c9114183c1e95028843d210f02201d5402c1c1e9400303000d58405d210720000850018a414010740307100240411010618050084445007103410060038440c19244451980d1031080d6134501034072510302100c2c4140758 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 684755980 1250 684754730 684754769
    0x60d09061401050a0501111018031701030c05040c141b15010e0403121d0606030d2a0317040f030e0904031d040f1b110714150705011a0307 61
    0x3001e025074440c080c140a47c540181120388014860f854840034140414400e180050a103e079508803207800560011314901040040c0c4c0b105001164100e036049881c200e1000d00303002c2084014001d03000c40400f8010b650080201e090000c1d0090803005e40865100c069000300f4281e1503092404100b00410135000e11401804000c20602d00190056058548032004100e1045c10070001c00c0740c9c4001d5604a40100b51919a0840008a10384504c409900f6144408001e0702c0a80340b082400201f01e4491011200d41c0c4400c45100c00340c4903500740a46018071064045002d8605040c8099409451000c0042410400c0c10380103200d10754098004c0d42c61440915041d10b00400f1002402000d07650500e031000030501c0e40da140d4119943c0160690070030000304c484100a6840b42c514034002e0300100380124807840400d980032410100329000c000a0000c1c03107120108120189030010f0481e007102d0002c0c800f20001c14000d1040c542d0014920105140e000c0d1100c0c00c1614100056205c0a0b860100104055 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 684757230 1250 684755980 684755989
    0xa0605070303051503060a0903090609060c080a03141003064a0d03020414010e0d030c0206070807052b021207020604080f07030c050303092805060d0906140105 70
    0x1a000c5801d80340005064540c2c401041050000c03a4809034184508418044005840d901581000e40b007030302c443c440c0650b589400e40300e1134a184151400700c1d40c0e070100000804c03104d00041040280c02c2c0f50005000c0c80c0c03565424048c041c152001c03506180181000c3c07041060910500d9400c1da043d1110300ca0310000140340170041d105900c0c10740b20040450901c4404001c03a405c01548124101054443c05640c0c1d40005001b90418811083d05454440400f580755000700c0c2c140c11181c00c0901600413990840c0c03000c0d5400e03000c014023260009030400c42c14001c0340011010f8641381d88100d02510034946900d0741e143d400e4135420785414072640c03d00303800c03150302d17070000b80e0034507030b0360112860b19203a80440c0000b9180303009540c022486801907034001002e00d01d0128002054a00c21b120106440341c4940a250740e83c000c140106400840220201840c10940f111407130b807140c0b5010001010720b4443e00410080c0d00300201720700c1c64980b03030314401f02005000d000d9007038800113544040c02c3ca03614100003c5c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 684758480 1250 684757230 684757237
    0x10b150904020a0201060806070c0c050904020a260115030501150b09010c0f02060304050115081c0e040905010e010c1b0c0506091906050a1706030706050c0c0405040c030507050a0605 80
    0x240c4160b50000b6208000c0b8000e40100e80108007100036960b5600d001c1d01c001d00b0300d80062508450000841ca004552480c003c2c6a40380201e4003d400020080e0a0841004103441e0f40d600c201400450312890350500e800074003a10f1139529054100c000290f1542c58900e00b9180218500e82e02010401c106101034191942a10144a000d107010002003c5a00b840d008015040c0000380d000f0200100300000c1c000c05411140101c20f1109000c1c02407561011096221540001a1140c07594030000c1811404c2c4a00c052400c4258020b10004202880c1d98030300d402c54550400c0e41c1c0041e5101c5001c442c8458001c04610701114404500201400c110350301c0c155071000c6405040e1003080c012032800280e80710f06081041c80100c03d490000016210303400030704141c0020100c00d0016006402d0440e2580504400500440026000b00401418070740c042d50150880410811035128024034441d031a41c49000e020702640c00780303107208550b6003103052141c20f0242540120f40100c1450780100300350b0342c0c0803084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 684759730 1250 684758480 684758497
    0x50603061813020406090e0708190204051009020a02061609030f0b131b140a14090403210e0d02030307090317040e18011b02030a050c03040909080705010b15 69
    0x2a031001e5034900480700c5040c05048006034200c0d1030f040c004112248258807100c118180001190311042d039950440d40c0d03440c1c489600c036001800800d08000103040070b40101c0d40160700139084a06184c2c880d0008800c17604800c0390f80005a002c5418009070340c030390440c002e04040c1d5a00e4601001c0c0e003192291410000c840b0002030007034094000003501c58208081c090142a4851000c00c01c1c8903c4485008650205005100c484e0740480620400d51801d41c0c0341c04121280342000b80744214041c81000508400200240e0901038034541100400b880f8215540e80d01114500018612000007041450940c1c0c102c034480c2035500400034024a60f8105140e0f42c1181d502101d140059900028030700e100d4003031a8014881e1040c0070090184256219002d520002c1440c0d00070000800b10800c502c3e01032441c86d01da103000d41c00c100700070811688038400400e4910781e88000c4a1410390340b1201c44080f035501c10f400340c1d25414007203812020071a0038084c02c8052001200c4185420038a4400500c0d14071030b8640 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 684760980 1250 684759730 684759769
    0xe090601091a0c0a0c0f0e060904030c05120d0617070303020309060c07360c1d040216030809060703110a1d090709051305011a0304140f0a030905060306 67
    0x411102e4800c0c030441e40c00c00c5084041c0c400c2d40d00146000d558001d2980104486094070f458086514298010b803588620401403241109031a540c5094131034040440c015220380c010b000702e0707410341444000100020313404004000380c21494402d044440480010094a06403c12901000429800001d448109008468003982c40c500c0106452600200d54400c850000c0801c02518052001d02c220303c100f41d8280c58403842c0744100c0d850384411200312007800700c04560440c032003007a014482c2001c000c400c40041d200510700840144c00128400380a80214005100c0400f00882000c042c49003581281880c20103108010071481d44095a01a8008400c20001c4085c5050041001080e001010500107002d00c0303501d0030000e600412084450092500980b0311031042801e0b445280b003503c2c102c801c2c0c1350b8854202d20804113016603541c00a001138a01030051011a45000d505000c08140703029030754024500c102052a005d82500703607940c403151160b034080c400c000d07041d11240c10910703482d01c0048 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 684762230 1250 684760980 684761009
    0x50f09120705042a1b1a0612030a080a0c09030c0308090f030a031b080d0c02060411010f0e040e070506031f12050312180d0201021201090501270902150702010e09060109 74
    0x48840c081400c0d040050a9898606c114402c41c881240c0268085e0f081618a151a440301c0b4180301c2d52480b0340ae00c07480010b040d442c005140e482c80d5500200000e400340c0b4240011507925221002c0100302c9402c1980c050071b0004c3c40340f4462810080080d00d0200683c0a040f4801541d10007410144400d0300caa03001079140401c0408109031681220a4001108810440000001402561140d00b1501111005da0f184845d80a9600840d202c0801030202d545662050b0041001e010291555860031500ca1085200114681d40c07130b10083c0d88104040280900010b02c0710b108021450b5459000d0201d403032080340d1880204e4070100486805003891100c0c0e001c240c81d02407141da000356451500300140e02508021100c01caa06400a00d4405007019100100d0f0340c0320242c04d01212800e1103a840e650f41c82d80000504055040042c9100030483c400019803001c6a070080703a040e050011000310404c4000400c9401c56030805100c40415500b81c40d40b415a00d4290006405003140f401820580310722203 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 684763480 1250 684762230 684762257
    0x4051011010f0b032814061017030a11030c0a030f09090204051305101a0a020f07050d0f0312020a0c050f070b0f070c03021302040e180a0201050f09120705042a 70
    0xa40c185c5c4103954081c140207442e4440150850311200b0550314188461090000010040c21400c0c203495030003441000f0314038000c1c0e00c020070303180f00030f01a040306e00d01e01062080220040041c800501d83c14041e89a40401005180c4001d02202454002c800003c0c0f0611050129131203200742c01d10000d0f0701000c001060b41301c00900c42181c64040e440b0455030001180c0a059158000d409001c850115808460318400b0030100c4030344070f030824000c0940000d400450580481c0c2107901403040305000f81070070190480c2003270604060382c0c0300c102c10360301152000c0350520410104201090441032000042c02c0c03401d04100d2601e207244203805442c1608480851110b00f4400c403065000000c6900034602c04050440303003a0940603400c2403144095041d42c01000418070343c04507040c4605154000081c050340381c11980152840d802450b082c048141d01480944026100d44541c80c501d40f03100c82c01000c8441c0303054100400d4901c983c5400d0f001140a408403c104501d003035182400041ca400c0c50443e010783d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 684764730 1250 684763480 684763543
    0xd03180f0615141207031205070305130602060403090803030403020607050c0c09010905100806042402040b030709080f030906071403071e0b0105010e031005090304051011010f0b03 79
    0x216400c1924400000001402244000d80f080281d60107540708161000c1d8603410644031985440007506d0b00d03200120403141148250020021903102c1c1c1001410194a000c6040c0c3d8261607400138405a801001070105250b04008010300038119000210302d945410340e402500c81001900c1202400310200310151840010f11206640410140021125607034071001c08010301419240d45032241d08109003c50084000f03d5168842c9810294045201140c0d0030480f81e04d0f0391800079102030580c2800081022824400114044d50441e43c2e05d02c24a800c010302c4901b407030a20f030681c101c87d61007042050040d4654900391080150842a86404010703440c0004c2d09600c1441e00c02440300e80201c461032981000b5010100000c1c0c0100c0008805030b803200d0041d1103003080a215258168460320802001b1069500850341c043e4581083e40c1c103080d910300c00b0402040741c40c95203c0206031040d40781c4800075002d203d506903080d0000c40038401d10390140e0200703480e2881d5414a03001a5041d4500c1000c0141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 684765980 1250 684764730 684764741
    0xb0114040b090405070e0312071b03030f05030402030a0f0b0f0c130521010603080304050f011404080702030c060f0d050f0402010903120201090b0406050a05070e01050417150a0c020d03180f06 84
    0x4000c7c2c1070350f401441e032a400c9a00e0740c0c0828422a080690700c1400c0c1c401404020fa040281c07681a1103500703c0000c5000e0580e4640c00041040b68984100029080040c00302200c0d007811741e12401100e401070a24000c265035400005018040ca854103000741d4018401141040c011189c1c2070742c451106184030000c012481e580301e02c0d070a2945d828000700000b0403840c0001180704078004c00503150b403041c12140712801c0e0340b407614a204160341e11101080c0882c00b0741d8003e00c0c01c0b510003412144200c80c683d0104844d0b80206040c0b4907503480104001d501c41c02e460080a034402c0c440f621080291405900107428074059000103000284003140c036400b400c0c002d40c05040c0164000306442080c1c40c1918103440074080454101000d60b0424010607820b502031002040341ca10305031603660030306080c10080805010f410780d10180380c0c89105a5403910070301c0885140c1c000c602c4100080340001c1c440801a29000045842104240c80c00c00301c01004603450301060a0990b0201d40540c1c92221414110003800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 684767230 1250 684765980 684766007
    0x207061b110601063605100201060503030301090b0616030216050d02030601031212060308090a12020d0b060105040b0309012003040f1104020c0d03090b0a09200409080c010b0114040b09040507 84
    0x124117990460740e0425070003420f0b04581045130b142c0b04200c0c044100320b09903038080c03040b103405034803e200500c1745a00f2a00042c0c1c160401030541428801c801c56243c81c0030291103002c3e40540c001c401407401102c115810f0901070700341602c40d4085c136006640429550141403001a11050884602d003403940d1048171542c02419041e0000d01100340c0303d04044481d07505c220300350391040c4003000d40010001a085042406250024002c40c601e1141d0b07112545082d00c0103050300c0c1004010031010032400a40005540140032007000040d0410180300200014006030800c003415102c14010880010305000045510503444801550034500c60303001704020713002d00c1304030100500421410456a0b43e0681c8010311803405200889416120074030345100310b6251030000f501c030342007801c001c4c9108ca140d8508940c00e0030010704000b0b404041070302d40ca4401c0d00041103e041c165100d00c000c08044d0390120310701031030701d8414112170314081c0b510a480045100e5440158051901d513000200c02c2c0c1d001d005010800c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 684768480 1250 684767230 684767297
    0x1e06240e09070f02070905091902040f0908031509011518050616050d11100b0307030602030c030a06061403040219050405090d02010e07141c060207061b11060106 71
    0x80c02c0111018001400881c00701d0300511071030400090108890048030b00aa11440180c82010f4a55142181c80d140c90344040c0d812684a102400803070840744900540180215144c80c0c0b24204840001440300002c1000e5100d4400c00006000c0c024600248074110350040c00e100032000454403c00c00f4031002507000380d42c401e0010540d22484c00207040c0d001d030420f01c95001c0c1c0d03541500340c2c1025500d0f41442c81c511002d59101c07804030740000202da8001000c4d004e0080845d56041c0d581d0b41c50b01d050764011200400312040200510101500d9802440d010f803a4600b03114200944c0800c0003140341c00300801c041c1c41455a0303200204100e81c42040c99010b070501034014070452401d0b643e0130344c1d03500100400c00c00540ca800200c846846020402d1000c0c1e860900700d2031000503041c0200003048141401c50100302c4110800d01c0c00052440c802001034601c03841c0d000c5401e00800a50440c3c180c2c0a40c0c078075081c4002040113901d0003401154243c1510341c181000c00321080111100203464943d4030000d20107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 684769730 1250 684768480 684768499
    0x10b070f0f200405070503060d110306010b2508030c0d330b04030b07082502010603033c03090b09071406180f0d06020d1e06240e 57
    0x24042d002100d40c022444141d0740000c00000081880308448081710301717000144091010800301d15025426140050142d5840a00034007070a0020b42021000ea110304034005001030341c0c0c1d41c03000c65142003003e400380721140c0f90080354150315081e0b02031000600940110400054403c400e0005521540340c1c040d00440c032854484a07040b0703205003846002e188000300c0d90040800105080340c401110241c0c0d501009074201a180c10303100755000b1b40050001d6442030118640e03844843c4003400d0481540c0c4565002041503895070a01030006070100c080702d2400103811b64450f280c41c1d82c5150b034100380c0700150002005a500100e044009111061303004004592000602c14800d10001d0214140c540581503000c85065500400026214800700b400d600144840910b0040c41c2020f841400110f025141210b804010b69814049a1000d0b0501b45030a80e1a50307081c11200034500c4941000d03c0460042140d80e04094175442d04c50250044802501d030a266100511485062401112800603024010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 684770980 1250 684769730 684769733
    0x6130e0a0c08060c1c09030311030a021c0522020604051801090605060a020a3017010501050a02071e0e18010c05031302010f170c0d1a09010b070f0f 65
    0x8491841900341912410011550598559048401d103150826105c0080d403003400d000405800d04a4094041c181e941c1b0248035210300c8400250b00c1480c000ca001a0f0b56055444e80041c440303090400080c103503180001300488640800640c1070f001d01561146109006184000f5816108a42000e0740103004103142d503584c4440c0e441828180c13044020144402ca480d03506004d4180540705070303280182d004800e0000400c040c0850202d070540300804840c500c0484603a0700050303000801c544c00024105800840b2803980c104ca215001d4002441c1c59441c00c042504025a90f8229000e40f020140030014480324000d40c0b502403100030090880d2200940c9040300c0c10900205035034924550315400c05205070b0000340300350b003140e115803c059201d89604065800440307050002d0302040003400020060070014083d64800b0510513141003c29594404240c0c8912081c1c40030700708588035442141501042917503510090b103055034403580300325803070f13801038109080300401400002d032803040c03902072840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 684772230 1250 684770980 684770993
    0x6210501060f060e031504020d0210030b0d0f0203010b030a0203100b1f0201020a021204051c050a020a0807050a09020418020a091a090103050606070b160c050105090d0201110a050306130e0a 83
    0x80021344101c0a032554040c481d500741c0c1d45800112002548070724546030110051914044c0f4480700381c0c041c43d0014482500e031000c0380c800034840c04240ca074010080039032000c5260900503000c0b0300d1010780c0139081c44209540425510700c452218041e1494440310344a21f651202504041003600c410b00321103210040c58000f80c000e5000c10b9110006008010760410401c0070310045a017112406018009800c1c0d03c01040f44400c28030380411034032800341ca45200d01595030814410054042c0c90090b000541c6820100080f525066204500990051004000c02003580000c481d00e800007040240c1c2d01d10390800100c1d001200d0350400c1f030311007400d515029a101c41d41e00180141040a807020032880e150003041107614042c0c10001886051514000f034041c0d40c603422007105100ca03606005565040c1340d51a1401d450040740d0100095104000c91012030303909005402000303d030803140603e4949190710040c21444014880c1380160791040c42076000000660040030303d0000007041e40c4803440d483c985030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 684773480 1250 684772230 684772247
    0x40809190b071b0b0f030a0b041508190b040b040311060103030302091c020607200a03060506030c041b0503100b0d05040507080d1215051002060f010906210501060f06 73
    0x1543d02ea614410b0f103a5160b81c0004101d42a100c1041c043c50401804c016030310302c19030000b0b146d843c0d6aa00c80c040c003881d80e00d40303005620306540580c0c08d0a007860f00304554980340040c0d12501411800c905500b05010412a10945401c2030b005401c90322a5030707071800c0c191082c007104d4080308083d00c01c140000040c503130b00d5805072000722001c036509011448442194030b0403407000c0700c1c00ba510030000c21911000840c5002580c0c84000401c0c2505a01c241100028102d00300550044c0c80c00c0f9218403c2000a141c01d0180541c102c1046508020440c1d03103122800f0200307202204e110510400002041f40c0952450810b4010000d00c03502c9961116006030010181800b1740742103c441c40b0741d44c2c1c04a540180411250b1780c0c281d8940c7c0c0e102c00c04200d400c2001c0508202d140002802040850110b207540f0303030360740c05540c0c0c0030a0740040009081040c1118400007050340071804072850f08030107002d020080b00c0c1807201c281c20501c0c4c0130031103482400e00300e0043c40340d54003040d14480050320010b5100d8110351807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 684774730 1250 684773480 684773483
    0xa0b010903080c0708120a030c080403091e080d020106090b04020f0901110f03040303030c080601080906130f0503070605071704020109030201050711041d0f16050105071b0b070606060f08040809190b07 88
    0x80c44000503081e00ae440c852000d44006010500003042844500d02c10310842c07480d150f2401c1c0586415079260307119400c054041c00c1c0a00103035110601030000f8580d9004803082810142e404600d070a414030300403406402846604e134104001c0400c800c0e80131900b08600c6440b44100001d480c1d89903a079140190040503103042600104182c1e0000610540c051641180301d400200007400381c55481c524070f111090321241044404448041081d4040b440c1040646500b5100e0080003440f030600f51030141c41c020900d61840da070124480100300050364890a04c400310fa6082c01c2c00d584840d0310b0f00c0e00614035126014016042031504080c9041034494030007038030884400d101900c04c2c5070100d0988030340303801e0540302078000c0c1d12803444208081e52150004001481c000c0100311464403030040d40902c54880c55003c4910b0320008142801800710074030888006115900b04640d0780703a00b404000d08a0580200090f0906034045000e1025884d0b02c100e12001030304902250b000140c6820380032140c1d8001c0b000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 684775980 1250 684774730 684774737
    0x151201090f09020108041410050f0703060f0b1204020f1003051501020f060103110d1b0302040f02041820040e040c0602060103030507150605060c150a0b010903080c0708120a 76
    0x3510845071480b072280842458040c5d640340110b5980751540d8031448a100441c401900c100800c0e0313062441903210f4240038840400c3c080c82d1a0410200060070303591503420048013000e044108124a040010480b10b18140c6600341c0d0340c0569860000540d103010450387c0a80200e00301d40b0080d920b945c507610044c45640055448000380c00c07104c004a942c0c8480c0c045652050784203a0060000c80d4298000500006004003405d90242e441d65604e070100000e5158484049030144060046141c5070103000030044c0c50440450400b494121000c1d0321481d00c48201c0302c01c40c0c3c0c91003002400e46001c6036090f40c2c0601c0c200c0039aa5a07a64280d1156440307403c85003078440342400e038070101d10701d84040368282c100ca800da500c0d9800d0120b552210010400110915061a07984030b40010350350702e07610301400300c200807107000d4245440c0b03008090741d0300e4800030080441989055806001c680c2c01c05103c1080d2900181c89640380d200c2e05010300d24058003500030124501c05d00c85513410b550284001030080580543d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 684777230 1250 684775980 684775991
    0xf021b010c09140d0b0402190e071403101806030c12140f030415020f0601121b0b030c1c050c040f06230901020a0b0702010203100618030303020915120109 68
    0x2840c1c0c014003018032480765031181c0d070384c031351000030540d80600ba030f40190000f4020f10700c04804462040b0b5800e0b20354001d41c5421140820085129081195150040080c001c1d8524618181d040e13400042428050b00e080500200003407131065805600801c065540031034501c007005c0c0c41796801c003408842a0011290031181c0313003000d016004040703582c240707501c9120000c60500d42030a40700c11103986100320036000c600c5003800c5049501d00411465001b0314030701010000342c40003414070119040c401580d01031603840182080208041c1c0300b08981d0f001c3d10600c0d1440c0c5a040b80000c44c0b00080b0204a0407107400e091105008145001c40c00403c100c4442c22540030700345a441d0020b032403400b01340808540f403442d55100456608460801851900014815030f410351072195100391401206813001c9005030b5002c42001403c0500d0402c0c43c014088504005d520b01703c4803101183c0c00141400300404040d00480c0340000d41d103450500442010f80820103586513480400001510b0340b091040c02e0030641045e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 684778480 1250 684777230 684777239
    0x60c1803110f0d020609061c0609050117060f0601080c040308030c1b3705060a0905060106090e0a0e0c10030e1c0509040908090d030302091503010501050d0f021b010c09 74
    0x1401c1190f50a80c0c090501d50130141c05808104171034200800c0010b110500c01706c0010102114450a030290004010026003075042042c3e400c030740002002d4900c02680b01c0c1e414403400c440c0c28181c1d980e115809282c507003a65582c10b060340403540103030b601c0107041c0350b80842803112002038100a0440c2001e10340d812034010320305040040c7d441c00f082000003084501107180c2201803101400f0042d99403102ea00b490f041141d190f484500d445000c880c2030741460b80d074591201c20802c0900c001d41c01401d60f46004030744281403000d0200d401d1005024000019503515460f10700301ca050ac216038140400074036202e007034107170301d0301c050050507001899102501a0314641c41c1c012b0780d02d0825840291381682c0e0b460402880800340030007404409819600c0c10703c14000d01105035034000310204114480d503809602c0310810020b019500926541443e000c400c2440140b0980e44d01106940c034101d0000008208030012080741e100074450780c44240c1c81c030446101002c1000205411010048881c0c0e0394210741180d65 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 684779730 1250 684778480 684778489
    0x110706170603070e16051606150b0a0e0103020d0b04230a020f0a120659040f050307121106070e01030c1418030d020c030a060c1803110f 60
    0xf82c01024440281d807804900380c0d19100c2408100600141411440c0c40a0a18601000c929212088928036242c140340c841680428032540003e0003401201c07401e05a0100000d8001d0118130f4071241059030104402c2401840da402008208102400c03c005103582402e0541c807078080c49901202908030030300401c10030390385e500c01c849000c008034052500f051000d10040782c110020810303c9500b1501c410002c20f20340340144020a284080010500440a01400c50070304845140a00c0000312240c0a40d41041030340106c00d10100d0084162060b800d0340d030b900d8001c000c00780c020340107001d40c4000b040e80c404100300f4403030600c40c0d003071640c8841180c600240c0c2c0030b9a0303425080300c248000030f0000c80303030442550003600140504511401c0c40042403101c90b2401400341c1281c50300740703000004140b04440b54107050241d00c011b8003c601c0600544642c600209940d002c0510b80184519a100e21785401240304000c81d0141070507000303640c4181c80c0c3e00d042c1680b020b0410b4680c0362145101d0030527000c0c51f151 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 684780980 1250 684779730 684779743
    0xc1e03081b180909011e060602011104030f0b0414010e01050f0105030a0215130b0c150610080c031302030a06060e06010c1a0604020f0c150a09081801110706170603 72
    0xd100b90700c4203001e090050100269014001c02d505649804110702e02c94900321503030080d09031001c400134a25240000090945800b009103850709181004203102091651000460080d0015030000e061784135881c0180103116015081c86c1154644a09850260b4041d00701c00c2c0a40c01c1002b4854660b601c400030562161488076000350b01c2101c04081c12140c0e603040015008000002c114500c00702c0d0707111180c1000d44e0001c00200029040b06041d150b07155450821260072004c00c0c1c034205101f41d8950000751003240302130b000c087ea41001000060f112290a0300318441c89a000c1d058480f2990685481c2c8050007007800790761103214900c000203481d544903030703850070340140c000003111110043e0300714032140e122000d010140c106400b000140ac01d02d81003070050040100c0380005280181d80d00400d01000d143c058a05d004407800c003031044021403008001d403007419018160714031401050200503a034103461003030a414103000d4041e00083d20ba400001000c4480200103494000b6941c1004140d107950 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 684782230 1250 684780980 684780997
    0xf071110051e03060f04151e0f0f050108040807063201050f03100911091303080105060f040608100527060301020c030a14041211120d09060c1e03081b 66
    0x5c900b1001d026180c6056082a400601d402a800055646800b002d081d84441c520325004003c100840401410000b440d02400810f50109032031045410705000901d00d04000d400503011000204000d01880000d91100b8140c02d041389560442d0300854000d80954848244401c10500d10800001100c0c100ba803141d030954500103024040c3c0c003800b00d0b071140007041003100969400d4802080c002640c0c5422880c10b01920710700d10451115116890014280e003016000715001e01401d0240088426091f41504c4c1a1007190400d10016a5928084000b00d4400c0c0d1080b42e00000e00070108848403a0b0120000d0f40c0c90881442d03c0459031100141403d074400c808000300140d00c1080b03004075551150111a510500700d00c0da01c1e28107651502c0345e8a2941e0a800b0590700350442c443d403a007452400302c07180f45101d01020082c201d1081629000740c02d040f01f0b0310070300c028401594426002c01480c01e4480050380c00002a600400d4101d007401852650211218000c0103d410800140c2d8661b1201703440707840e07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 684783480 1250 684782230 684782239
    0xa0b2d0411010f350a1506030c09030308040501020d0501030323040f030b0c07080c0d090608041211072c010506031b0f0c0604030c021f02030f071110051e0306 70
    0x154072101d002d010282d20a00d4140703501d01307000c02206082c1c54490050140300b40010200385241c0300ca00c6100c81c15000e901090600d8906020321460744c0d00401008102ca4260900788401e035914104980a48101e15558001c3c924040000c0100f50700701c0340384a542209071151400e00b80126418807a28490390084c002e031920780030000c10005460007d1503070b0042d8400b0b2a03a080c64802e6440000540018010000c0354000e618401c400b04d030b1000440004010303601d0003d8050900d40c880c80000e80352841040c1c00c200324407a0340b1080840810110004001c941000ba103003000c49038600c11155174460a0004019849000103102c1c549881543c1c001d400d60701c0130016010300400a18007076404a0514000d40406001c1007031081418000e041c0300b540640c6901008101a104010b01c000a4141680104e6a201100b00d001035001054a00440c4051540c0d680e40719542444003078001d031006281d80c066102d42d0841d11350f03940320b0007501d14441d42d006900b42c07138110300c051091079000448041d41c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 684784730 1250 684783480 684783497
    0x6090b0904150e070f15090b192f01060602032503351b0a1d1002154501060902040311030f0a0b2d0411010f 48
    0x458242c00420807402c2002c4000a200c840841e0f6103070500e501c80d8082001010400400c0140742c0c54a000c110345401c00d8640090050704080d100c071400d009403080401042038520301aa82da40c040d1b1002059185000302c03215140d4980e01c00c03c03a010466612003001035003040c50004400340008103a0303007801c02101d9812078410114000c8100d05200407825000c001007440b00c1c4210a5580c03404210002d12122540e04a01c14142c0c802d081c19005004003200d11000500c0a05802d041c1d0207a03a0350140900d02281c403402e00160100c1380880300720119501c240c800b05900c40c0c0c01c1d0002404200c0300121500b201c029503689034401078405202c54541940324007030600340012490120010340c1c0ea400c2e403403206071b069030b003c1055085801c00d401c044c2e01d065000070140140300c0d00c5640e100e0000c404900801c0d4100a40c2c804c00d48941481c5070041c0b6042c03001c404211708200c10412308002c00b502002d0342064405100c602134000800791801e6a10500c0c4c940c1508503548a281c0c514002c20681d01e6801d81c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 684785980 1250 684784730 684784733
    0x2041b051603030b150703030b0307240201020903061e09060705030a0b030f07061d090c1e1c06060905041415030118060609111c050a0b0306040b07020106090b0904 72
    0x240005882044041560b030300d00036244d40c5c0d0341c060382c2c0341001c80c044c42d1581c4402c60307441d010302140d07090a8514480d42c0445020414242e10028007624180c100700c284211452121040e030180c054042004e615000d0f000c03c1000088072440c0c8406014291100d05009407240c034040c0e500e85d04280c41c41c100007141040080c0e80b8000e903400207500c030030000d0100c4031a131001c0c0101034101003898012400241111005040880c40394040207105001202c0402d01c609250b5102080380c45804107052200b00001c1845c2c44250ba98000d0702c824500c0070300c0680700c454207000120020445400348402080c4854400314580c109841502501070202d000d441c1c068942c0701098040009a40300250726641340d0300000d503040080ca15400c0704502c9510041046400d004201c07007640c0d080565032080007401c0c40910400d0a05616034107454444080029083e102c1d182e045016010102d00700741c05100e81801d1000700401d10603110311507145603000b0009181c40c3c541c958251440640950307409058880400c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 684787230 1250 684785980 684786007
    0x9040b010507050c300d020706050a1205100f0305031224010315081006050a0501110d05070206070807030e031005013c080a050c06070305030a05040c0f0801020702041b05 75
    0x1c40900d6110b0342c05800750b44031740041c0c1885c0f02401040440c1d801a032442e6586c0e9804000d0400a810582803c1e03040c20818900100007505011020051907200c8003c00c000e041541c9180010340304845134507a090b900d03400d00136540d0f803100c0e0602c0400c0104100080d4250b22590b030103086000c4407c645501c1080b0b0000440180008140f039080c04a00100c0000d40d00c01300304000a40710041520100d42e0310310701000c103e8203060b00c0e401541403103441131045030000e030041008841c2864500b00141c0b682c0082c00410303102c0c018848010403400001501000341a0025034056042c6c004504440c20943c1828007001a11428862021100c00c90f8a0310340c4c00b50300e1035011441c1c12a40d4008200c21445061044c01c1030f000c3c690202e00c85802c0f110180c0c0c01d00100384100c0800070003e580d00b40c0703030802980d00107100e4880141241e001907500c10100c1c0400010207414001004090303902107900c0e40724007002d4000e51000c04100d1080d4500020143c0d9088040410300ca60030054031030a04051038541b001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 684788480 1250 684787230 684787249
    0x60a06080c091807030b0a0b0c03071e020d030c1203060f091e230f041e0302030d0509100b0901030b0403111603030806130e06040204020c0c041109040b010507050c 72
    0x496228041d85843e221986102124500c074480d030b80d038013041d070510001c24030001c038445400c948280c1c0020040704040365000400c03a4072899102c5260141030315030f080405130040925200a41c00401c1740d100302d05050b07100c03500924450191095021070034511205038200c540074420700b51140e8540c4c00030840701140d9401880b4450f055030131131a00828070f40c0d40c001100c268035958420310010000311103071b0b0a0b95a4031180e000c0c45041c1174588074145612007103080d000f0500200c1c08440b281541504052003441504e01203008036005210606011103060780310322440110304203071031910040d8909440e10002050403660000403881041d182c0d62070484200c20040d40cbc070000d62095101a60201003018514030085000369150034950910301c0400444280070150490600d0602c0000313141c540003c501c964000e60b0403a001a59800c1e085000342c2042107070150341d58090700d84946150003026103002041c00401c100c0c0c04012410b00c48005690902803010f0141413503001104c02c100d00e00717204008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 684789730 1250 684788480 684788497
    0xe0a090c0509041d0c030619050c040803030709050102120f031b040b0708040e0f071b1506060302040f0e0c040e09011d010f0e010e1221011706060a06080c 68
    0x10a20b004460004901618442401000c1c1000503e2608030302e01070500c0400825001180035044508010385404001005109642c035032554070404602940c030107004860080c50640e003500d0301d918142c035001d45581a01c0c801c890240c0984600071200302c651108a40303182c0c00c058801c0d411600d82080f400c000c0021031f034080840311003c000100e4508058400380800d24403410505984900b0407046c10316224010345a003042007908424003d581c5d4201203104449040682c62161440c3c05051000308101d0040c8001c0b07c10f450003802060b40c0d581500144283c07a107002c101c1a03e1562910801540c020440e035a42e81000c0600c000e0203c0110b40305c0040c1c114103008004950605c002d5001203482d00300303803480c584680d9118004030001d01c00c0e000c0c01e444039045200810441c411500c201e41c8461504807644215003000491450548c07141424240c1070b201042c03181100d41c0c680040d880c40741100010322026125000001c1d1581c5030000d01030059681584c0d880c0c030b407a100c1940307824294115041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 684790980 1250 684789730 684789737
    0x30708090f1206160801050a210209070c05070f0303080c03130b0112020f0a030c0501050a0302040f0e1b03090307061802030a0b06040c0e030607180e01120b070e0a090c 74
    0x51441640c0d0b55402c2e052820a0440302411090a0442d80da00440307905114100034805070600401140e0f41c1c043d0110220b8901c1c040002030300c00c0320322001d45148840e0704020741c0010b9980c2844001d5074400440e41c1a40c0c032440480d41480d80762406090b106001e480020009002d14000030310011088000c0c5420908010840c09050110341e03c088402000b40c00c030b800d45022440206096180025410503603407070594644461a0a6803104030155126005041c1803103400111401010310aa044900800b01d0b01550710030310b80c40319100c40340e00c0e40640b0381000f00d0001e41c0b0366107080d6800f40100c034041c1c982e030300095181c00640d07903a0f0405000603546544000c0901030311500503803801d01a007014a841400380c04103903d0a0000c010423a400000c1c0070041091140c0c0070704441e24001079070741c0c00c00214181705011704ca0048100d4401c002e950490880b410ba8900009400503042681c607100703074800d207600041e655441c0c00860b400c0105444256105181324020001004294810500d514080c03a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 684792230 1250 684790980 684790999
    0x615021b012307240e1507050f040e070305060910060e01030f0c030e1207080904020d0219050c15061023130e0c040308190201061d070f0f0203070809 66
    0x50359882c0e40c020034800c1d01c0440a40c06030504141100200315100121440c041151305584500b1940d525004084041d081c80da41000c5445175005000341d400880c2404421a43c8980310354201c00901c00c190307114804607080c240400c120340340015159124501c001001c9160601c0c0400884005011840b4513040c50342d00c0340d9440c20551640103c0e41d10b2401074501103400c0e00d0102005242c110030140f1400d8a4005200c1c100020710f50204407100d1a100721809a11800c8410007036000b0b1144c6500b858a540309020142100c90308003010f40401d1340c03002c0c280c2c0c2400b104996407540451085455540c003540b911140d0140710f0254040700c81c00c1150f0200100d40480385000c040301035000e10301e1030113a0310940748100240005000070307641c400091a075040c14180f440c2d40d000300c0c03801a081e0f000103610510a41100c10740c400d41c0401c0003032584c190f81e0103280102c1410700394606000e4584a00041e28940584420f40c000c0b19409201c0b0301c6a03000310301d80901911114030756044405210b50000821 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 684793480 1250 684792230 684792287
    0x4030c020a08010b121609050402040219200607080a1805010e1f0b0d030522030b0103060c09081914070b130e0103021806180a0615021b01 61
    0x11000005891074000019071a100b940030407100305410b444d079691503440030409003256815440c14601f03c0350080c1012505841d1403002401034010a801c00304440079001003d6410303540709072060f040786120050000400c29080e205034449104031000400319855501040b69540c182d8028a808504241e580200d900710b50340b01760940f00300443d50798060380450709511401c40140001d00341103000000420040380c070f01c03011404c00b1681d408082c060003404149006092034205414842403254186038964544030300c1c20404030745081c0410740d0810301c2e000740c0306080b6003e4000182501e14001c004c00b0b203004041208503100c00d580104980c0790b01c002e02014103401c4100320b8440905018540142c81304404070241000300640c2e0320200596880344010070142c2c9900940005003601d03002d48040300d90301c0e40b0110f0b0100d40c900048000045101e4200040a0595405001070390140f464500b418102608100e0307035002504242000e000e00c004151410f5030103a240d88404880801215510b032845 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 684794730 1250 684793480 684793489
    0xc070c0605031b0301030506070f180e070e040b010e151b1507301b020a02030d0c08030a0209030a0516030606050a08031804022a010f02030609040b04030c02 69
    0x3948039a01149001c810b000030104407101c81411001c1d038000c02e50131517155444090fa02c100c050488010310810001c03807010940b04c0e0b20001e00000c90080340e0504143d841c00100303001c0a0803034620000890b1a04124110b2600d4082c1c5203031140e059540d0f0005400107001c004d40e00758400142910800c0801179220345c2d200e009041021190004041c0c001814501c916103600d440040104040007500d00007400200320402d440c03040801c0d010803030036060f00f0a2141000501d1160012012400d06000c0741c96030703c2c0e00003003810800e0b1083d01a034071220308902090341c83e4000d240006000075001e01c000f0b5402001e0345e003e00018070008049485052143e12020b0800307070712001a03000341c2d82420091061003024001c407030042038282c031061358040c900b618494603405a40c5810b10800c0410700c404940b90340701d40540d6079810b000c1204c1064400900c9031400c42440d25594a4001d50804400e14252000c42c400d81c1e00c20200034103a0303e0140d03126519981104001002101842110300b05500541c80d07 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 684795980 1250 684794730 684794753
    0xc03010c0903110603040503070605040203340b040513240e01030501061d0f040507030203100234020d080f0310091b2a0f05030901080108010b0a030201080c07 70
    0x60311449061030450611451840d0500c3c8800c0c0268030410a02c00040d01c004100c132003071a00000000780a44513480000d052600e242101845d1483d07244051800e00c00544034102030000141c02d14045907070b501e42d410700710701941c0701d03060340241e030740000c50b071081c01940000280540c03442c119101c03140c203000380c0b030840d01540c1c0100b0034400300700005004000091040d200946120b40ca102c00103001d0a44598180324002d0071011800206808102000320400c910805140e004081d207405010408182c1c0003500149803060880d9900410407106018036040301240d0403405c0c0c3c0f0507020300c003140c00f03218203454480c4003214000000c10003460342d51103ca01840c05401c10f00303445c000451a1201d008103462000c1100c426220703001614503d565002000c0740c4410754043c010000150250441009a0024000140403401a0b104d41e404100010005000c1001c091b24ad09207142d03202c1c08414200d035107001d5559082a04a01d05001640c0282c5540d40c2c803290394000350385401019a5521308244 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 684797230 1250 684795980 684796001
    0xc020a080f0f0f011107020f030f010f150e04083004060c0306050105210907030215030109050708090604031b0f05060a050604020f0315010233010501091d06030c0301 73
    0x2004040340080c40d0b0014048400100650f400074001300b02c0840c4281050300c12a80003e10501d40745000c0281a1020301403a0300880010008000d2492401200005000011070484da00b5038099000300d036229200319801e000781d80006940e400c10000b01c0201300c0d20500c6004404055000c4000c11100d010780c2100c040c0700d188a00070100b25007030314450150035108141c022038103102d8184410b60609140b001401d00001d0710b00b40701d81c025200c00e803609041180c0b940000e074201e244141d1154121041c0d4005504841c2d01303146c200456500d07100201d40d0001c040d1080d0200c0e400400102c2c020a00c50b00084040d03604071520b510084003155500104010718407000c850b0f94106400f00248030b2458130546a00c00b50694081d0714110a120485009100040c81c62a80b0824503103825600d034801c01124160080500582d43e40c1c460480300280c2c0c20318940b0145000643c54000464503500c1040c844040381c0b9441650007078a02d452a880500510090100d070b00b40c4035102040001c0e5038240219403a02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 684798480 1250 684797230 684797233
    0x9011b030e0405010e0705090d03090801090b01050307060519050721080a1b0c030809010902300309010509100210060b22051c03030b0604090221070207060c020a080f 73
    0x705800910003a1401644459200c031381c402d0400084a42000c100e5020303110403260104000e08524054620a5194000c03150540c0f030801c000c400c1000c40b59450381610b508408407218036688160444d420312510100c0296084c00790801483d441c01400549040d0340304010345201c00e054040b88452030020b4600f070b200081c00c0c043c20f0041d40d4034188208900790411198444143c0c0c8407400141c0600100000103081203036000c0003540d603200c294401d0f00c209600030894501052541d102c010700340c6c2102d4a00c07860340b8165032107040c2004004100c808004040c0c40d510304040501c010000b000400c1800c00065005081c400c10b1041018070604000d40606507141b5120908129030701e22a0003490141c0c0011458644148043c1d9150000140d00c0754003041100c0100490b803404401501c448680190004c2d03000c10007092140103500a842d03104001004d039160035210540281c8012070a40d00c180150b008400240445d40c4121030f00086a0f0000e03001050265650842c5807901840c514041000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 684799730 1250 684798480 684798497
    0xf04050312030f1302010819021b03090a0b13091d012f090a090c05040803070b0103121b02040509010e03220b070309091d010c0c02010306080706021209011b03 70
    0x1101e841c0924240c0005010a001300102110f0340040c160540113052800455019140000081d400d90100c0b002c84903960366006504120ba411541d0340c0d001661603074801c040c007500c0850125010750988082da00c0329904a0146c914000c2041e000304064000d00031400b015a210b10ba4001c024002c102201100700207145c809206829070902c810101c00da044041c0f0401c00868410303a842d5074002081c0c4421660002e956920648280c1b00380c8900d61010010b4040402c403401402403034100035040764010840315080180414040b01e40c00c000800ca08902c454107199800541403da00032036101400100000303a5050301010546181c01c2000145403e19100ea81e503440d50130b03801002c0006107801a0341c60300b04460313682c000c1c0a808040c0250903919a0710701c00541108644002034a200c040c15000300300101100c04000c200c0e000c880c0040e0f002c682084400a11400700240c0c01003155510341c041c018a00d540103000403681e2200c10040d040103100412965100385d17481e9244c040b0351098546000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 684800980 1250 684799730 684799741
    0xc0f0b100e0c0a020c06180306070819090210450608070522090615090b0a0e0105071112030c01180f02060a020a060501350705060f0405031203 63
    0xc1d21000802c1e4000086092002500b0540c000852011110703040b40c4c51703034642c0c4108060b0700c10603101c151141d5052144a0a20010503003214005005820185119002c004a50030300c405450003000025001130780e00d08200c01c250b106001160058903211500d1040381c00c01060000e460240c1c46920341c0351060314042e0545094230383e5510000302143d041031b90170380c032700180040c1c42401050f0311403564400b032a0000d03600310326034a568400382402041c204070b01516078074442c0c080340c54061184042189100b0205101400c03000b6500b000c0456641e1a0b0b0300c82c1e0070b100444183d00a80800c4908207140c0504500075580c548103209460460070040d9168003040f180e4500b510a03500e40245400c1003a0494000302c0e80c045103d01499405840c215903885095030100c0c075014403000041d00c41032803c00041011300c00d201c1610b10400e0528044078054581480803800010314102e00d45040e404410104454241360740640a6664182d013580c1c1800e9889e00401d00b00064403240c0881c8610000c100007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 684802230 1250 684800980 684800999
    0x2100e011514010c080a1101020d0b18101e050607060e120c03030615272d010309050712030e1509010c0308130606140307061b030c0f0b10 61
    0x20000d051000c000702104a2140c0042c1040750031544c05021001c00085211005026011050380800300d00000c65031540c2d403502c01c030000d00e51403410502c00d40c5e0028160501b28200b402d1a4016502e40d01045000c03894494180f03103001002642e052602e402c2170300010256551405411928042d00020900405501c62142840500310340707050139620a01000040000010a49a1000c016546028810004a1459032074041c1c00008120703440e03c400407d460f158000c680070f44910090b1000558402a8007180003001e02a065005e003240b11061101150344c802d400c0540024000c0c815244c0158a5038010588094581d40c00d90108443c2100710520b4100106408003021a21801c1400c141c41040005c0039082c4c65007015082102e880081150b040b44070340d61004444d8030020030001950ba5003c0200d0381c10403600220710034025000000b6107240160507020000d0040014080758001039602900e8541c00c045083d1601c0c00c01170f070840c00080002a81d103001d82c201e4250345040742d2400c600c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 684803480 1250 684802230 684802271
    0xf0b041409071209022e020c01050903060a050c0403050319020d1403040b072f0c03030a08010b07050a0b0a0f1d0d03020711030303130605060d030906050a02100e01 72
    0x103000d00d20030780c200040725030300c540700440d048507094020a6404035800003c008494100181900c4a1840e1043c1503551b181d80d600818094030f41c083c0e0301c141450700c0c0151203074052000402c0e0180c00100004a041d9101c0c2d20072584280da8a00103030034182c40e9268145150400c0303002590003d014550305034008e804000244174041d441c600103060340542011100507001c046e00c0246a001210040b401442c007440c0d4000e16480d54041e0001da02ca000600c0c24420a040c1c8204c1b1a2800740d07195112003401d01104480c1c01079102c2e290041164600205140541c6c4a0a4180d40074081c60898400150710b403180d582c0607100c8550041240f40060320707203400321000c10300081c0b8031511a4407845031105011030b076650110510708006841d01035a040040400e6800101c1c140d00d030000008200651405900d480c0d00103001d003c0400050ba18a024401d44520014016021401c0d00000f08012441036005114026861060f25403441c24400390205942180040c0389050b5142d403809200c032107114004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 684804730 1250 684803480 684803519
    0x60309190f1a1006030506030705120c040b090402031f1407030b19060e0112110d02070b0c0406051c0e060114100504050a120f0f0b04120f0f030b0a0f0b04 68
    0x2602c00382400c2030240f441000c0c034800c030b505068403800020b80b956030600c0244c004042c050031544d5841d20b58122030b504c03070f2000c00c0e205215501d05492801c541c20b12446192003641e001e030041c0000e01142e10150362030081c13018182901501d5400030046000182685030060315281c901242801c001c070204040200c00100c600c40c9120900010850300b5031040071500420403e09044000345640400000036015440c1d404100f05400907203120321601c1030340240f00d41801208001c034940c544805244d00c91181c1d214100025900740010540c000007a81004030020041400060320b105465580c3d041620981c000d40310310803026000142424081a0b0700c0c219182c0e89003061401d414080021902111030280d007180c0458034803440c04124204207903e1403260055460a8440064078250803601070840b41101d1032207501c28048401401442c4042001e9025210503d40031044ca004800415288040301d0b8030004c00c42e0005014240c10180501510441c0d40c0240d40c0c43c00d0103210364640c0145c20b01c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 684805980 1250 684804730 684804773
    0x90c090509070e06240d1503110f04090204090620092112130503070f0b09221d150603032b0606020a02010923060309190f 54
    0x10804084000304400b0203541c24800038002035202d080226400c0101007440c4c00c1c960504000d914504549803010b000b280707100000034041d000c3c0a1281d00359540c4180300040005056019410040ca0304424000b01d090003d00000340c0c0c160b480d000902074a80c05c0c003068070341c42d6686580342103681d08040c03074205100d8610005881c0c0a00324010560f000a000e800d810130100ea4181c210b5030940c00d010a03412500310800090700c4984205038480c80c01828800c2c1f034803c1c4943d0fa8002041454a490b0304120b5411440f1603090813050002c3c001d001c6d21402e1b02013203426801900d400030303444c54441c0c1c280d1501d540c03486c40503210030442194640501546196054080f14081200c244d40c000216081c868450985102685c420b1007007007403021111801c5c040e05c50900c20b01140740e0b5800910b42102ea8001d0b038600d41181e640e034034914a41c01c44070300103e107010752a20b064902ca090072001141c124104808a50189842c0c1207069040c1410300c80491f00085144116414000c01c1201d00001501411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 684807230 1250 684805980 684805991
    0x503070e041e0f021605160e041e171c1103010e011e05090f0402010f2a0201170408040f080c0904060f0e0601270b0d0f02150d090c09 59
    0x100c0b034085501c80301007103040c1c90b40c96003400c40030720307219030107031141c1e60040c150070102180f0f03d28100da250360340107426a0703180b1009480050000340c0800f80314021a003001036408954072200804c04103d405000030b4814130031645901500d252468000c00c012032a04e180c82c0c00058070f1420030001c1d03c601c030114000b03003c1c082c0700500000282c0000941104c4101e070f6000d00d181c066101c040702804480e80490b51050712081004050b41c00c0c1030800784030302c3c07007688c4a4a9644121400b51120303019208004444581610b5003401141d411000c3e4510a005042984110420701c00302c41c100b500403030702180c1a00c00818108151420b40c0b485034083d207211409130144801e4400800c0d44403500401c0503203c02e40f030b40740840c0c1d4800c0507070001800c04070702c2007503406039a1118181c000442c400f00041008400e248001019a20913103e00241b0540c02031081240846985030303526210303c4000f082c0e0703000500c20203500020201400801f00301e40580740c003046c3c620507810715950040650f4441c05034070342441e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 684808480 1250 684807230 684807251
    0xa05030703050c040506010c150218031b060f0717090427020105090a05040c031d010c0207051003140405010e07050108061f090512010204080111090a1502100207030503070e04 77
    0x800da0f03102c1c180068030700040c0b980e50440100d43c01c420356031001e840b0320105044d440c02103080340c0041c00d0061400f800840b501210206250ba5002c8001c0c50b0040148820281075180c503141c6c0050481c024103640c85828035140d03403030b010030f0218100c1540048850000e4544180e00389400781c2c03210030365071094030003035018800c28420801c025098000d0412000186038041590b0320124907010b044060405c014a04050001800400b0140050050070a05c0e00403055008014021001c1d550b07032a9000c4c00c401840d0805000201c203203610a40c1c2810740700c40c1d110500d031030f02400c00c0e4400c9010b0300000c030f40c1b1105c4018203070400b00e0981046040114460401603240c54042d40086080c2642d01141c100410001080303078002003d810195000310502e441e070145100540181080c4c0c0c003014000c01c82d14000701825002440340550a0f0b40200d6046010014213090350710a2903815100d0040d199125202d0850000b207034441d0408602080c008020301c00501d43c0941c000d561450107540800103105003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 684809730 1250 684808480 684808483
    0xf0a05061501090306050103080706110a1b06061e061106131410020307030218030d0f110a02030312040b0603010c020322030b04050105041208101226090a0503070305 73
    0x42001d0380580031401c0d1140c00c0c1c1d00c501075400c01140c00c54420801d55031a89040300c6d49901120041d41d1980c18807840e007850500b028110303041e09105131146000d0350040f6a00f81c10f41c0d02030318402d81e0b0301d81e0348030b000185030340384040d10103c203440b41c00784842010300700340010305075081000c0340c5119a4880b404000c0400040e5100305180f540140d8031101411007039210500d0441c02d02503504916002006102d815501030b0064078103d810031000303030000520710081c1640c950080740d26200040036070103003001d003501414210030480c000a054402040c05070f004246142d01182515101040751002c002c00e11500843c0c9a40042045009000080350144000d54070b0140b09410641e41c42c05115580200030019010300045d80d20403c00e07105490a030504900928080b40d05445010f070785008003040901c1000c0251040a110240014490400c43d440ba8250b10302182110b0700d91190710103141c903084401d01500c20788030851a9503901d007080014000000030740c0e4000c038007a80c02224103200107a030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 684810980 1250 684809730 684809743
    0xd020106031a1815010602010b1206040b041502070b040c050102060f0117030909130605010e040b0103170d050f011a09221b02010b040c0503010e1801021b0f0f0a05 72
    0x1d01115680e039030300e40003c1002d16544a012550091140300100800c882115408904032040f40e0000c001d00d0300710600740003d0350200a506030740f0b40c0006000800183c00b0710702c02d54120b0701401e80b0011501840c10040201d074041d2030142c541081440802c0100012901d101026040078405012641403180d0401a15203060191010591010303010f180d4000041007600c042c494010b08540e02820903010a10f1420a40c450a0fa05641441c0001c17a54460f141030a42c01240c2c08444144540e04e55200d20380a654003210386040a40f042112240071070240c0651406140c0d2400661495458806400c042d005903484e0381c509800c0520403851b961340c504a425041c2c040c20180460039041c0c2180300801400001c1580c0c400c0001d5071484249594158400b02441c01c0c00c2d0760030042c06c400800c05842c98082445121885000200003440e0706010a03d074a027104115800542088260310340c2c403140e540c00800b001c44a034480d088210702600200584610010588041c0c044018951103007a150803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 684812230 1250 684810980 684811013
    0x5210606090402030c0d03090806070302090a03031412040b061e030c040b0312031801201c0908030108010c170c0702210a150c1805280f06020d02010603 67
    0x1800c1e080000c0c19900c00348140c0c0d041000060000350020030a02d40504903001c0745c000c0ca0107522883d00029800c034028800c90748038000003400d00074903d145660840b00446541e041c1a04c4400034403100c500b501d02901c2990003a4402d0240c50b030b43d450103401f40a80304100c40034006040421a01f21191510049591805230505940c007017450003039003010900c0c0444000314456103420000800c00450340c8040d0410407046003800a105003408c103040708400995207050150701c041c040050031809100182018242c03000640d020403410703480e4442001b2500700b41d00600c031b030b40d46030f0b45401040c55001414140440d501c1c843c50352a421304109091a030b008411000340a0b4840a09118515250820a07460074031000100e806082940c41c0003541c0e0001e03441c68003000c034288801c8500c120b0245100513a00350008407420384040c541010001d034003200580110700c40100e808a01c00082cbc2c81404000a041c07080000ca0142e40381500080c80c1c0720202e96981c045900d0504140300003000030f1800d50080c3c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 684813480 1250 684812230 684812239
    0x50a030c021f0902040b0a08010504020108070804120503090f060a0204060908030315040b03100207030513080607020d20070803040503070515030105061b0f0a050607020a03020634050405210606 85
    0x903140c8089170040c842569443d90116800c00300145608054200f80c0c4160b100b81d8507560191503128003920103620585008080c0221407410140092048014540c00742504049850b0103002010b42810070406940c3d40141c02d4000805000c07440c1c010803100010007445000f14518505201002070b10204298254411902c03005c504020365410020460030300c3e20f0b840119501c017030b249009059640410314050283c00c560800241009010401074400d40c880e80141a0714003c462084580201c44030600d40400c601001c0c06e00840303010000754000d0f0061000460b030f694200401c1501c0c02c107440e0700052003445041d1038030602c001010103a90440c0c80a0300c105031a8040c03420b030703034081560144002c80b07503200340e40241c607404600180310f02c1d205024100b940d0650f19960001c03608d800304090003601507071042d00890031104100ba5000e203032500390304c03254113041248070445042c50318001ca07040002da40480c0c107004a02d800e80c05404400c084904030078403c055010b51940b100b2005210703034481c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 684814730 1250 684813480 684813491
    0x111e100516200306181002030915100b04060c0b15030a1b090908070b09060c07021e030303010b1905070308061309151406030304051c030306080706050a030c021f 71
    0x241c80300b80450044401e0000c00381e03606031410b0b000c01180709404a980c044180700c3d03040200c500808a2080fa8003840f03900300030300480200481441500e2a0280078900c10a0a00b9800608480e1403400350000d02010358940a0782680c03410400d207040e501500c005014160f0310703c181d00c20b0f640000e403400641d83c000300041d0300044d0b0191601800c0c06c02c1d80960101c41c18071000c80100281440280500c0380b040e400c070306698498041c80790362600700302c401c000800000c01142c0050315141c2c0e2205e954407a601d03024200952003030046400c5070002c1e1b000021415001c0f03440c41408041100700c00061f0320524100307092500540b030041c000007024022501641c1c05c816174000107200d50304841c03612900300c503450900c0c03400303d84940c004182c41006480d9450951003c035000b81390210446040340c0004000f010102094140304c50524100d04040302071550740c1c1c100160459060041100800d51078075070030781310303814114080c09844030b030845081190042c0c4c41058814040275106000c3c00035440300080e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 684815980 1250 684814730 684814763
    0x50a080312090c0d06061d010302130b0a050d050114011a03040b0a0e0f070617090304031101021504050a1505190209010c0b101d0c0412111e100516 65
    0x420540900035a040082c01c0d82c00411711119800038001c55030702c501f0004012060450780b2010b91400e0000951203c41c4030580d00054010b50000300e16540020910f8180c6a036031030000d100b01b0034194049406944600700c10b0070354011105018010a030007a0607084140700c100300f940710340c40000e000820500400000c02d2850b48144c2c450841c51420204a440d040c180c50303d00b641e107501c04d10070880001e044a16410b21005030001a03405496070000070340c1082c1c00c0d99100c1c04200e000104c99411031045c59840c3c0e500140315040c0c40e0065004070701801a00c1c2c0141000300c9034005100d44010403074249001d0000b40e60800900d0f5100d880d801c81d00588400080d00129005964004090719002c1c590080c400320115050012045840034400d240c02415004000b80d060502220128a502000e01c01080a0703188000c1c0802c0c0140300d04079800c200102071b00004c0b004180300302c101d2054036080419900074104100810034002480c100281003c4000391035515030ba00b08100106184480c035443e44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 684817230 1250 684815980 684815983
    0x140906031e1e04420501081207060905011514040b0105030f04030804031e030501090b0f030a0308060612010b0c161a0f070b0108030d0605040504080a081503070618050a08031209 78
    0x800704e101500c4541c0502d41075801c1e501c0280c440c80400f0700891320b480d00000e034a801c0095040840303911882c40c981400b159448070b100070000884140c07029500ca10f403065445905d40360b0b000c041e052210207000c44080c035005200031100e0a6601d00d05000042017400003e90340134001d80c1e070003a854604615190348030301e002c56138200e0038019480e02c09071848603106841d070150002416540e441d1400c001a21402c41003020314500900101d4058003d8414030002c24403070f4801c0d50303001c0006011545400c2508041d0135402d02e09a0220607820004250342c05080024003440c00512140e101c2d410881c2e091000892042940222080c9403107800182035080007004000d9554654004803c40869a560b41c60a43c40764061000040c2c1c80f441c00c3d9003c100c40c41c082c414140079540100c2d000d4101010303400e0070340e10480081c3c26010451980c208846507035504004100240015a86143c50900e00e0040380c0f03550000c981045208e4088024203000440000050364141c102400c1d0039111601e884c2503a5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 684818480 1250 684817230 684817283
    0x3030f090e060d0b061f0203070203060c0a053a02071208061f0c060c020a0308010905012102030c030115140402070210140c010e2b0e01140906031e1e04 67
    0x42c0d1b44c000d80403114030305454000c0f000d06581c50003941914015502c607050088688580190308020890511200071420280c00f0b500b40b801c4860380c0c3c010124082d50100c00a845486024000043e80000d504410020207041d00030100d919402c0441c0c190911000113103180e8045c1c0c588058503142000c40703031075840c03050203606c650a41113002000740c4043c0c03a0340291503070140203040c1c011810540001070f07018014070a01e030480b01c0d54025882c0e07511000c107000f0001008004142ea0522034181c848055540c288102c410102c40701da003480d2000c1c0342c4142200b0f060302d03003a01c01c0e00c220b03c140004000742c0c541944040441c7c1462900c4146d29118174590307050341c040c1c014046020742c43d00f510a0101440000c5d84407a40010310b1141038800e80d80c440c4801040da4a01900380081c4440894940da075024540c01d8522001e004045404d0a01050208195410450706003661030300c089500f10b0034801e28078880d50002d201d105820107080b11240c0600c174050000d00010301500300c1d0b0100d41c902000182c0f01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 684819730 1250 684818480 684818509
    0x2090f0f01090b1605011803050405010f0c0506090d021b0a0e0a14090a06110408150a06080114040c05011701141302070308090106090b1003200403030f090e060d0b06 73
    0x125102c2013040c00f04510004a1981180c0e10743c60708200c0d160038402000b2070304149a050baa80c500d0319041800440d64038644d0b00101c018044806260b10004505110580c400c2100c1d8000340f00300c03448848004e15000d00010b011510005103510701c440c83d00c84400c00410340700ca1400702c00780b0340c80b007504203c001c0111204292000c040a000c2c07101e410f40100c5c4c0f40080078018a010b104034a42d1081e4942540f28620580140354003885440091807091445560700006041c0001035075a61040c082e400c0d0b4061403410803180d801d00042100b0860554a02400b5010030311708030b070240e104003038181c1c6400c50600400e580d5600c4500e5241d2183c0e82c07070701c9000404d000960301355240c420603d80600790340002e48006415508013040490402d400e44580340b04100020064030b0004d405400581c010700d141984502c44c11980481a899840140000c0c00158440d955464609803200b500400c0d2591541180b0082d100180030b1094507691040301908168114100c0f811945403500090005403442c3c0d138 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 684820980 1250 684819730 684819749
    0x140303091206072304050409050c100906170c040b2b0c11010902030c040c030b090708040516060f051803060a0f0606081902030615042702090f0f0109 66
    0x7140c91000c004180039000340b602d40c85015034080c40d20b000390942d0030103034002c0d851900c060008001c24602500450f40c2c25005200b07a03040302c07101c030010442150605946c0d00102d0b601c0a0100400759101d8042c000c800008030325581039003081c400c0c030f1751184510b04c1039001c48000400e0150502080d1b031030780c8092010340046410113440c40d002940c00b5165200100740821a49411180d06030070600a445036298010060f00f480c010860402000f0300c020380a000800da65800300d054107460700450f90340600e0300c2c0c1d150f007003092810307207055442e03c000e00c10001d02029402608005881d0000d201c1503000c80d00d41000d50300d0f07031080480b40d14040002076510b54180f1a0400740240c150465101c4041059100c1051000b651250f03003e442e49003054441503040b14805400120805003a80130b075412400040030448d402072421090881d681040e0048002591900c98900740c040e072210240c0b0f03500c0d01c1d10105500701141c1e80c00183d511920710300f03401c0c0031b80900d0049030201c3e07204070b6565004d07290301c29 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 684822230 1250 684820980 684820999
    0x90b0117031308100501170d08100302120f120403030c0b0402040f0f0905010b18010e1e09031c05060603070843020312150d1509050c01080c0414030309 67
    0x1002513452510b00a600c101d545444008038082c00f28046414443d1041c2008204031040c01c0c4080360051401400c0305c0b01e80f41110404001680d82d050117050004c1250010840703a007100c80d42e181031084c000f0610702c14080c00c220400000303821a40c4d0710513064010304403038495034403400450003501c1032880042c0c900e442d00c0c5115440029a81c4051082800340d0002c001c07204c00c1c4001d01518022000901d100c18088000401075040ca104030a984034100741e01c2d40e21704448102600c0c40c1c01000f980c1d1080c80b5000400c1c1c104601550340164041c0d502203001c240620f003491008107030f0910002c1d1444040029090004408440c5604511555000004600c035281001c0140c944921525152100700e1580d02036504000781c0300005440e29a03194600c0400113450740b82c0f10380d90400c00348000340e400c50301001943c1c0120b9610240701400c03240c3d035000400c1d4001c040c41c180d07040048044010b414400c03102c043c0201038820364261030586072444200d032000f10100c3c000925500402c66825407201c0c000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 684823480 1250 684822230 684822239
    0xe0102070803091e010c090e060a09090b01030b0a060f06082a09090c0306010503180a02040606050c0606030f0c01050a020703051e1e03070305031e0c04050a09090b01170313 76
    0x380751132032080350500d591081640380d10007030036929507062140001f02d40c4d0740c0c240031440301e084102d07810100041c03080c0781c92a540d804507030544034000c006481c800244401081031001241c0c2c1c241d40500405410070829042996183e00594140209400c00841d070b80040d40c3c45081480c1c6404000d40c80140708076800d01240040769603404000c205024207200c2003c500c1c4100d00e40c00303883c00350748140c4469003149c1c0c036000360785004003e40c040c4130f20341d100761a44039025032a18072600d4040c042a0783c8095035000d600022515140c1d02905050003135110500000b0b414101144c541940c00342407034101c1e65150841301c104c1c5085c105420141c0580241c4610311040c0c10180c1010042c5c20601e800d5490b41c412180d01e1031103241c54030300c00401a8100b00026400a40301d880119844900913401c021004890301c1c00968a040844018469110008050209140c52041c210091006050901800f516507450070400b4506204240170401c2d080b0b0324443d01842030055881c41a1085c11034266103666 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 684824730 1250 684823480 684823483
    0xa0b0a0c0611211608090a02090c0d0203070e0a06170f0603010b040203162604031404080f010921050904020903120a030605040c09030221070909050102070506010b0910030e010207080309 82
    0x1ea610421800b00c40c02c55004c400d020345482c52250700c1d407001a01c0d003903c5135001e1040000e4014404007240604000d100340c015983c1c80914014052030740c46888111800701030010003405034000000f8030901500e10310248510200301c42d48664120742c1c0300541c0c0c4807600801d0241180c200181d0b4082d002004022500c003071180104400ca0301340d542c64929980300b504940c05125080b40d421007441080b0f00140100e40075420710705480140301c88151400740d0307881d0040d05100480041c0c0459035102d02201060040140443c48041c1d2142003404100340300d401c0240003071085840c4180125004a1032458a079801e000700302c0c04403860350243c1c0c1e0300c0c20324110040051072035001d10b911561820400100300c1f40319142050950394094403030070030100c0ea035020100314a229250a405407244203004103c0101070300401140304e02c200000b50f1a900d451900c541440d005802101100c401445121040c2d81d864002141c500581c0c01d00080c00140c000c08240a4482c480c40502400360010510121000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 684825980 1250 684824730 684824797
    0x2040e0712060f020309060103080a02070f080f0f0c2b0f081b07060e1e102a08040501080408040f0f03050616050901110c0d0b060a0b0a0c0611 63
    0x4202d00800c00c0001c2800d261040340000d8400c000300743d0100005200240000c4001c003a80030f06401101c2c44150ba62030b107241240440e4001d03414a0b0400e40200b40c0c8040100490100200300d0b0005e0031290401c10b000c510018039900c080354224813058079512200e100c010400c1c42c0e454200e0104a25408075040942d01c42c1d0180840c80300c0900040f1050601201c045801010b80d183d07540c1e4120220080010061415440640f058540040303c41c0d441455894a02040203000c07152103a241c6010341030b04d1070311022106a030042072144801700782000030348001c0071a000d03940b090a10b10001e80781d9040c00030280c000d94000002d0070340803d201281c1d5002481c800002c8911450454aa90f0f8984038821402e00a810701c82001c11024000081698090b9000320501c075040011101d0880030134000628403529000261903006034442030142900307103025002c024141c10f030043d520301034240b58001d0800d0061000075060301e58a883d08182046250b08031002c1800f60140740c00c0913484038405450220 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 684827230 1250 684825980 684825983
    0x270703050714040509060108040203160608090c040908030c070302030c0d050d0b04020a08012601110c0c03070305061f050d0b0f060a0f050f1206152d0d02040e0712 72
    0x72000104444900c419000300c40640d18040c1c541217081e142c2c480103544100d400380040f42e2500600d000044e084254509045c02072040703965000076414920710107814414071050980c0107500f440d90b884042404001140e4000000b40c070301550701c000b241030807401c600030108580b0080c01201210707038040794054058030300d265200c03034200401d1203c001044200d01c2102e081101040c208001000420300c1d8401442c000301c0da86607002d2807108200300c210b085668243d4068400038000c6400d0350710480c01c110140c1180e10a41c01000781c54255203820303030b5a2030300501d081008800d190310303042c62010259000004202c00f40080960825502e40610a240304840500c020340402002420b20318103c10000c084600d403a002c50203483c10a8240b092120088500907048203844140482c940c0003009074600c658003508061041400034000c2284000500c140d0020103400c051394080742507410020302082490071280c60419540c01d01c00700300a001406413012850044241c00070702b4068100802c400303a0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 684828480 1250 684827230 684827237
    0xf03060f070f030c0c03032409090b09190b04030e0d0308040605071b03051e03041202010f2c16080d020609030a05160c091802032a2707030507 63
    0x1400b045811021903000ca040b500004a02c80d100a010a02039400341e445441c1100241e10044c80c15802280d148116521404241b9525640d210500200d01e2130181c1200c2850003070803000b0142c40d0311041401c108003001d80752210000104003054080d00c5020301e19100074100c144203994900f000380c5041c0007120705031001818000019607051040b030002c070000780020380e44510502d10b1348040b20941c00050b801600000070f120407003071880c0ea50f8003852085218040c4d400140340031450083c2511000060041c035141444038040072200110309207107054030030b0701d005030352a1803001c0309900d42400c684480340785454010010a1321540455036400d480507036000ca966a0726201c1c21182c3d01d01c00c44000c8400a802800781240e800001c2c1c400310700540c080c0b0010121141c4405082048883c209505644900036482080c06c60a00384a0403054801848050300740341e00c07121560000662507424140310744517860000c5a04001c1842100c1da041c0c18060b004840d240044000e402080c041d41c0c0440070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 684829730 1250 684828480 684828497
    0x14090607020a210912050a0203070902040e15130e03190206240a0f06050d05130203100c170f070e060c07050607060204030f030c06380f03060f07 64
    0x14038000100b07040303026800680301101072080588181c1c0c890303225240c10100545001e0024100c015203000c1d2006502030005005000550310416150000c070b58403544003d40140000c20100c20a0442554440f80103818055500b5810340006c80e800001e900103110140341500c6040300307c40000140c90110080e07240322406104240d0140e9840c0302c11a11203000401c4004c42664421840c03060300020380c000341403060620303141d1083c460060007a81016000500105608607440c0301c50249035000b210249519500707200c29004079813605d1810148850107511220281800c61090b4150003203400000ca607204031b4286400e0841000e6800e40706034000071202000c1c00c02034640300040b905502441001415007515010900100c0d4101003400e490f265400e220001c00b0a000e2043c0c07200c1e0910994840c2c503d9282c911740181114803800341d0400103003800f0b450118030f44841183c0b6803045030160324281c98100f0301000406158002034060380501030300091081d0030a80100d10b40c00340f000c64641606 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 684830980 1250 684829730 684829741
    0xc060e010e0309060a0207051f0f1b0f08300c0a050a03050402010207030f05010518120d1d010e060103031403070e0118230103180c2106140906 63
    0x281c1d9614591901107802c01c0000c1a807500d401002040b003284140141e4003c00d56490000d6046c0301000d0400f40340c010907100701c103220f60b40102d4480003620701d41442504240d8041030220180110369004000c40c21070091101031005030410340360380d075141c4d00d01a90300d85204201c42841040c99100f2034540707182100405c04a88644c0c01350792000c1007070b1b0784903030500300c2c90842140035040c00303070099042d03003d6044048081241030000b08121030080c400401d031810041d0046220075100011f80107141c1050440703440403941d002c201d82217181e10710b0340403a030304820080c42d40070014042020400307986407101b80c0c81c0c00c2030007203500c60407680240c441c60710810a10611880500c401c9800c400018009000d410456025030000001090340d8041c0c01c00d2075480306072050000340309001403000099050380b811107943e0b05008031811a00780101800f00079a40350764001201a643c0903080d5820f10320584000c00c803545d20017032103000c2c0e0030aa00340b00040e07240c060044c01c44410384c2c0721002405400c00194 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 684832230 1250 684830980 684830983
    0x1080417160209090105010e040f0303060b03101d010501020706050f0d0c23160b0a0f0c0206101a0d020901020f06010f06031a010918060302030f07060f11030d0b01090b0a0c060e 78
    0x24126008c0d081c903402d5a0703441e82e982d60004805000c0850600d0b6175800c0c08151410208091485002c1909001c0c920904011714840c04800480c0070300076080d10000188502e0340d011501c0c104489090400c0c68480c8480720715401c950103134100b00755003645030240d180c08082d8002c03082c40c07600904100e1241320004180b00e4620b140b003990a10003241c0c82081c00d81c0f00003052a040c05070302c6850042d000601400416480042c0c0f80f2121b0a400181d100d9018000d01414000d1141d000303101c0701c1000207084802600782c80042c0075030f0b48000c05141d8041019401c503402031107074003e200700c002c2c2523a11640e1950083d00c0310146901070306001078501080c12903250380110000440f04030585510798514680341d00c1d401181403034140310192980f1000e0000068504100003548688400060000c45040c0100100000760031207000701000311849441e02651408421905201e046060206640d107142005a030040cc2b01c1d8401d6440e0280050120949644081e1022074079100ea941805034132100103556 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 684833480 1250 684832230 684832241
    0x903021f1d0102180a230a030b0411030717190515010602030c060a0e0303040204050c090a0801140703092d0819090506040503030405060304150c0c030306060c030e010804171602090901 81
    0x700f40410344a681900c1c0306c68142d464200f050401030000c2c41e40e0751207644280e8030000a950459080d0914201c01905103824400031026000c42c03c0e82000b5004040f1401d65120540340208000c003022402000030b010007441a951480254401e6201e2542d499100039500e9200c09400c8405000ea400031940e030a605004100b40505284003c506503140ca8003008005d2001030400c10176400200f000200b55224012040001c2c84103400024111841cee40e0320741003071500104030908151602c14140001150141c10b40040760705c0078001c40351144d11700c4114480300c500540c050715155000c1400c018401020081c80149050341c0d442c0001c4d680c1e514140051401180515585a00148024451424480083c503840381c003503c5c0799440681c02c250580b0071a1209449000001c402184500c185501405840002c0600f8038181c004520549c80082c90240e410400d64101300c213a00109092041460080380c001152403005641c410400720f0072007998030140001c1340600c0f90b1500081041f401803081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 684834730 1250 684833480 684833489
    0xa0b090f0312011e080709021314211227030706020606010525060b0a140a030305030c091002030301170102040f031e0b0f0f0a0903021f1d0102180a 65
    0x400c92980d00340350240894003240b04040344c0200c06a00005401081000400020881a0740040e0365060503c0c9081003a001500200d1a0841008004e10707140c0721001c1018a04070f44501810702120603094041c240343e800c0070b000c0400b90001ca5008040d89031201c080b100c400da01012030040d112040300341a10b4980c10712560001d85c102c100001c505502860060003030011b11184120b01004000302101d031401203180c00e0340d81c260340e0300030019a41000f0340c2600c054101e0704007201244001600240e099026400700a0070883d020000c1b8104403058010b680b0b400a004001007420340b031543c0d000395070360424847d04628280d441440d00701e155040c0700701c8095401c6001c1010f4544e04545406408100202d05000009000d607007440202e060585424007840c10852082130500b0245c0c6d260b03904013009840c18402510703244911000a0700000d000c4910442c103181d0300e13401c0c1050205400248546030412020f00201e0720001c04441c030643c020040c240008118800710381e10642407002c0365605005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 684835980 1250 684834730 684834757
    0xf1912090f2333090a03051c020a12051b01050a142a0901180902030714090f0906040f0915150510050d060b0a0e090c0f0d0f020403050a0b090f03 64
    0x2204160f14100c01c46003c000308000800c81c81d224041000c00c1c5800c802d80e00984258025080c28018001c02d40b00c010f65407184c5100524207a111601d03689240750b000310a540c1400b41c0000d0300c05039009001c80c1d045503a280d00008100c1c1d45011a582000750442440ca480c203088960002608481a0f1000707005c0c84e00408ad0b522102044102100d4581d0301080e05a414003041e010f9480c0c061035a9840c0c080540008000542c880c04c1a0b0005401d00040e116044a81803080c0031183e040d0712222003140b60f90038111001c1040f07840b1200483d00034414012002d031000e0508028109100e1031003480300743c02130124000c008882264020500114003802400c1d44002c540c00d446450f544140042c3c90010036011002801e556200e000104590203550700b030002c80c0d820011035010745441200b4036400441c1e05000c0d49024012035060750a44140f0500c8072902d5a03401c4000e01007400c41c2e040d9405980d02c0411184001c0d05030609028403201110781d4209032107002d4419407106004010f9419908801c030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 684837230 1250 684835980 684836029
    0x6080417032404021603020a14120d0b0114040801020a09050d12180e1302190e1303020102041503021216080c031e0a05090f1912090f23 60
    0x32190249074182500069010780c0a2007145c1031080641040320485110750020001140c01e0b1604c5900c0305211401b09115412184540c50089c19000840d2280508482c0c002041480700c4010f1f1210400289030801307880002c600403d9480d015030081c080c810b40c0c1d4440d16034503540d8504000400c041140300500c44030600880d4004140241c141d004050600000180060f4070b84140d85004001225207503411803154541205500300451071080e90b4458aa080300b6180c10840740c945a10800390603c4c00012404a24000b030520030f6068801804585096880c84800084d004000e500604038104001c800b86000c564420038841108158454940740c400c41d1b5590709240d5003880e0401081c141001d00340c04281c0d140c9804404c4c29130706c14100c0c1040010103040000c255443c1904d060580001076200100300859075202000038200cac01c0e8804a0303400311a0052408680c00c0f02a41e01178542030300c010b0380100700740321018034420040440c0c1c02185540703c1c40008012a40c4034a000c0200c9291100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 684838480 1250 684837230 684837271
    0x3020f0a0c090b03010b181b03040309050913020d020f060c030310091103130807061103070f0206091902101103040b0c10060501080f2a030a0605180106180f0608041703 74
    0x906540301c081848d400201c1141180c050300c203a4800c540c110700080004106008525095100641003016114007440390071250380451000040060b0213841020584034164040d55020100c07040510701c082501e8503800d00090a000907003880c058445140d05291220341c42c2c04003082540d01c684041c594030483c284030b0392902c0401343d20800e003e81e041a2230348424060104a20003d40c0940025602c0c103441c030f417107143c00900701a4040d080d2171141d0414a440117440f102020b1801c40140c049514480c400d204401c1a2040d85c4c001100f04040d000c0420005440491b2030060020203910005a4280c0008550748604848860003540e0104500342c01280030383c43e4010610340d07c2003007490600c60429040400d03112100500008150013100042003002481e00e50141070001d040688124480446000c900010404140555010000b1003036040c5000030503000c50314010151099950741c0c15842d444000c0400034215020380301142d502e08445004278003d400c4a2156003105140146440c00c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 684839730 1250 684838480 684838519
    0x10b0307050d0c050d110a0e01081801090f060f020412080a020a0813090609051501120908031303020c010f09140a0506120609070c020f0d03020f0a0c090b03010b 71
    0x40c01060030040140b00c1d81c0403000140c45009000940d82c0c039002c0d183d0356044002000c1d0348101400100002050000c00241d0390022500c0c113410720242032102c910b42d1140364135a001c106810413441e1039070900340c01009010341094001205030007901c0912400103101c0d43c2609911851007450f8106141501d00000704400e071025041500d91031055030240c22254490020a812014840110b50291101044124520710441c0018884808107100c1464034030080344a02c04ca444007141800440034030f01e81c40410316031000c544240e10444003500d83c00e2606541e40c0c425001101200548110700c1c06101540c0100d50200e0341101e1a5240600325061444030040d40309140540d5801800806011a1540d6014040c0c03152840701c22010840e0b1a050003000140c0354060141414010300040c8000561030f2940c031070204c10b4094030740c0c81c41485540b404030310f00317141d1910001c1c040c011a000142040104a01002221000c0d80180580f046050405007201c500300c081c0790380814500c1d80b240c0420803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 684840980 1250 684839730 684839737
    0xb04020102160906050f0102120306010c050307120c030e0117011a0c0321010e010b0706020304030c020409050601030c1d040b180d03051906051e030c0d11030f03070b010b 75
    0x1062060b0740103650020301900620300190000380c03881da141d010920150814600d416545202440101240c42041001881d24400070300b019041114000700e007003c0c80402c208851005034810300106d4244c0c24032070024036001d004034003180010308a2052011a6204030802425909009003401090b440c1514078140740d96602e6400411010a01503d40c003a003040c0040c3c0030f17100c0f051034400c01440c01c20010040c0b000301600040761010084006100780385040c1c050320f1706164040c40050b520788403414241e43c00f14103144000c0d402400c054414080101c0400d1283c1264850043e40450588901000896040b00c984e00c1c0c1d54060a94001740200d0500403036141c00603603005c17201040050052229040c02003104c2c50340042511401030182c40900c54000c40422074a144080019500380b00000304010040c08031800f01c0e0811640c1d82e150b80d035051080300c0710300f85d0040c2a800d910456150000c42c1c0001106014400d00500e06440c1009002008803001580d11040c3c070076040e820000703066099003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 684842230 1250 684840980 684840983
    0x200907030c090909030c0b090613030f0302091011070b0f0702091e0412090b0f0a1107051e03010b0603161b020414060f030d090506180a1401020f16030b04 68
    0xb560400603640400384030740d1440c24069036556044004a00304240703015405401491550310000402080a074000c40e41e41d00160b03d071400710185040507000300d02031b014404105502c200820b2482c4d810070f03005020541c840070b060007514105540c1d2080c10321680100e00280110000400104005142441010703030302102002e12520340300c0c501201c094000340d0440d0300f20740c40400d0340c0940d40801d40004000e0010410100682d240a0540c40212987e014902c015014880301c4900d0680303084013030140754017619002d402c990444106100200b030903261800c00c5c500951070102d0800d424100341c02203e11802000c81904490400003c00b101c46844c113032022242c4408800c0080c0c01a82c4602802c10032a0b10707003c07038541c0d42c100b4000b0401d0070f20102000500c00d80c0521903603010590040220400c81e4400caa01c50f1b01c031031074900203501011240044a5018803d02008034040c0042000e40340581001c2c4d007101c1d0041c008400c202c1d91440620f0381000032110a450420015020b4000194003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 684843480 1250 684842230 684842237
    0x6020304061220031015170a0e0f0c040b0f0f10090b070c090b010c02010c0b060112091a0709081009080c030a0903031b1a06060c150103200907030c 65
    0x620480320103d001c0c45000d003080c0d00481d4000b0500014480030268038020b4102454403840480c0c074800060240302d00e40001d616104240d800003001c010441d07001441e41104e00c030a50301856600c151581e2500300c821442e40c800d902d0200b038000d01e400e202ca255110004040c28040074803980d00b0030440c070252448540f8080100519002c2001040c03a40981680c130b108030380061107a4184805007083e030303045200306410011005c29002c00b41c1e0740400003a607441e0300502505610380316180100d0fa080ba620030403402450401415004210503200e00840c0081000e1412901d5250400119071440f82841683c06a0b131094440c0d01800781e0952165406522564030785145c00f150300e03486429030300400f0412001c240503900400a250b04218043c4080076211444056008191381e11020111240d03c58441c03d0400b60006400792196002ca50612610b14215902c800c006a07150522040c24001124221410340d00100012480b402501301800b00038921038059481020440042000c41103903001c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 684844730 1250 684843480 684843491
    0xc05070609051c0305060913050a03030506270f070309031706180a051b0c0717070308040320010c020607081e0c010e190c030f1415071107060203040612 67
    0xc1606221440b0442c981c01d413400324642c83c0000411100340002002c2e810b09031507204080c000194007050614000350f250800013200d444650208892400a181d2002c10001e030003032044140d800304071010702c144805945110550b480507021230a407859040000d004c80d20581c1d040d040030202d900280e6200c00040c2940003014400030294800003021b5892200d0740e0358650900200b10300c6800410400381c0305001d00c0345843c1c02c4040550ba2045a40300f9032440c203801c9141505c10010030b00010004580081942d03403541c2c0c89041450305008983c0c549200301e0802008003800d03500400707021401d01e400426945c10300e2400e07200c1c01580c1d0b00400d020506810f508a0340511016007a0160400b11510400007501400442d01d25282c080d45c654682c071146c01c42071680c0001020305090800303407a4000003540c0f80b2507103854502d13004510102c000180e409540c24a92159801401b258031502c090b680d05444001c9114240e074980c62180100e10060f00100300500c40c06008001411040c40c0c5807500060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 684845980 1250 684844730 684844753
    0x7031d030d120f050c030c09030a05010e0d0f02120d05153109080702060703052808070c35040801020706051612090212010e0c130c0507060905 63
    0x50489001c10080440c00c0010480542c0d85244514034006082c900100040d0400c43c8040c502400000c0c10007582e0040040d0172840c61320107014803003034254068020f00400e452645902c0d140d400003204440010b0050008111840c0700040000118089030101840c000480c0400009090018030810441600e91280c5a440d01e41c00405c42c2c07100c221840202d95009021121410102c003005046103050030405000e01241c11001143c884690482c3daa07607584841d890181ca10b40030f2140134286401c0c203001d520b501c0910303451140da124015961208480c0d0345001e42560f64058026000d0900c28031100401206a6032404d4080300c1301840403144c4181d801a8441c1704558802c0e0003490300c59401040400420205020b00c0d0340020b200c000c0303148040079101c40188a144a0003440003d2501c8260250035074841220114000d841d80700248032141e08074140d280e5500d940000280a4030000c0e0700000458014442e620754101a965030a181c030900b5120030000d010311003410344450241118601 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 684847230 1250 684845980 684845983
    0xf0905030d03051f081225081c02030c070b04020604050a090605120d021027080c0f0c0d1403040905160e0301060e13110a180605040c0507031d03 64
    0x420806150b0b808502854050304200c0c0d818000300d56241405104030081c030100501048a58003a507528242540300c0d001c8843c000d401c004002041c100001c22001003030103009848004000101000c41c90300600340342d80502e2030481c4000c44101c02c0c5800284402c0c80015030081403550000c0c001000c00e800c09444100241d03620340d00f035114420f281d40c0c40d0310402c1241011b00c00418440880f002500c09912156006501c030085008031601095860b88402c0c40c601000ca402c80c501e010200c8480315003001c0349015545540035519440842c0704170607a100700079200194101400d10060040304c0f03049480e45d00c004640110000c3c0d0711480c04240400b00c0c0100191103450f200d081c003c00707001242101004050400400146264001d0341048414400e0645444075540c00528910040001500a00748a000b10311051755565004c1040f207000280e00200081800115403404030411a059513501000200d40c1d01c403004001050b010300c03480d80440d0040300c0c00141515011410b06007143c6100019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 684848480 1250 684847230 684847243
    0x150c0c0b07050901020105060a1a0c030403060c0f0e04050405031602010e030f0601051009230402090406080c040e03090f090612070608070801080d020a060b01020c0303040f051504150f090503 84
    0x100d001560200c1c2141044da424080d280c5c1149003601c06800441c1008414003010f50b0000704052007440018254801c64000c1048800540d04001c0c100842800400002d0001c52170000d20f900041003050701903401e01c0c0920071a4080c0768090021490200c141410384003002c00035805074180a8a400e440645407014410a200320390f035a00548100d42c14001007002001d08030402400b003000840303040c49841003500e201c0861140c142d105144880c41000010003070305c02c8640b0240c005003800b000180e11500080c2c40d00a90701c040703800307020503c401c5800c01c0d980c0c000c000100c0d5000c030302459000f1040c1004810580c012201610b82c0d5402e0440c84030321803a00f03440783d02c1240001c880b00c0030452800da220515501400844019007001588558000d40d1a0000701c2c0280800e80e54001c1c800a0740e00811036a15040d030090142ca454075641d20140c464a0000d1045500516203000440f88130304008003100d0589070034904a51041c0070340c0d0b0040350198940c0f42c02c071080c050f4040c0c02141d0384e5400c0100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 684849730 1250 684848480 684848491
    0x30d030c051c0f0e12090103090c03020d050d030605030c0a120303020405030a050d020606120a151508010e1c090e06040b04050421110a0204050408040e040f050705010c150c0c0b 78
    0xb05840c80351a8080c01103e0003071500c04e50580240b08044102804003086400071102440c0c041100c1d109400d08200103c401e910080d0700c0303c4800381d020104400491440444d0382070741c40c2040060742c3c40040c5600d42d504450b003039500085c5000107010f4100d40c0216030948a000b458014100354950012a103403114011003500c4070b40c0040124428240d04001035079024905850741c4442944140344281c2c3c41301d9814004081c0d883c00400044901c2c0c0c207501413115034043c82c005181156841a245000b40703202d400b803030114006c8502c038131131034400c4403000d44c04200b440c0d0b0381021080c82c0100b40d0140e1940135012550003511450700c48441c0e82c580c041c1c1e501450003a2448440007920007819140d04141074843e501b030080c60018080b1500010031039200340c50701074a012582d43e4403468110502e20850300180105440c0c0024803091004e80c1070045407051140d4122a0301035100ca0054848042c1d400c00241307804140326110211800c10307000315501c64074a0612103600203c0c2c0e520301c21a000200e03036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 684850980 1250 684849730 684849787
    0x10050a350118050106050d17030a0e100b1504030308130c03150203150d1e0f0f0b07170906061002010b1806150702030a030302030615070c060306060806030d030c05 72
    0x100b840900c4000c1c890940103080460358020040c038650350b525076034800c68420180c8850088001000d9549a4101c85e0a040c0c00409460102c40070a100381c00a00c2903030026030184084407410400c1c440400100c0c0d00b940e406440b0b4501a9640e4966401c502074035483c103c500e80007802c4000000740c0c020b402d164446908078000b580707919040e100c1111886442c52140d11591900320f0b10008207500082010b402121402da0700700c0754045d2305000801c04044c610092070748203406040401e106500100b5800b07000d99036030700800c1c142c0d49840040361900c1601c100009030401d80200d940c03807a20044101d640011070002080590250700001c418040080301c248008a00c2001c1002620303100180714401c618a03180301c1c0c10200c141e00031170755808003c01c0007014560300101140459071152000c2640340c40d111402a82e481c041d18015407014070a01c1801c01007824401b010a000d03005400103442064060300800200c40d064104070050100c401d01001400801c200003076015075603100c0001e02c0c0e4031804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 684852230 1250 684850980 684851021
    0xf06030605040e19170c070b0904050f1005060a031b0305060112020a08040f050a0507030302010e0d11060708150d0c1703040b030f07120f0510050a3501 67
    0x7400d202c00e86a52515000c81500a8510060407005186100440540007115005059801d0100707029900c21001e0041c40c2e44284040000c450000358000e0020000940d0b0501c885d403503000652042d540142e9841c0c8024451308400d0189040281c00340034a120f6528002c80c1c00200c442160209001520b0103500103030b01d40f0108580c65800541401c280034440c81c04520342400890001e1070120098401000480ca24441c0000c3c4501041480d003411307005415100c0640e030b80d241c0a40241080d55540040340100001e181880e40a03403078035584486c8903000b5001549e00d5041c101d604607070080c400d4000617005902c2c0c908070349804e5006400148103800c042900c5043c8000e410300b000c40040000415071042105008041c0040262500040d21060840080d140d2100075114500b543c1e44103103510f4544801e0701040b80050300000e00401c3c045501908550700c401c1480145e2072035004010000c10000d041c1c070125410726114400c5550959008542c0c0c8807808541c034251908501c4d04011424200c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 684853480 1250 684852230 684852239
    0x1151d09030310050d0c0905070906090b030c0306041d0f0304030213150303120f0c050702190608070c030e0306070c0b01080a0c03080d02070b1617090319090f060306 73
    0x1210054101030104000d509620b816980301a40f00070300d000302e6000300c2c2c24000702410002c280f180000070b0051448184458138180c00d000306214010f226240000391880e030001011071803241241d02a001c0001c80034a1079a40780180409407115000722164402c0c000510200750405124901c04802c101021716981c524500401001d2411182d00400b00c600d000300008110528890070384c01c80342d25080180c0c207200880e822200402d0100c1d840c0403040c1c100710321116401c0d4403100512041e8800c48102d603070a100150750110840e994011200440ca8040c0440c50090150300400030a61292500801c403a007070340003003420a4000e58070380340420080e00c7c1040c1000b8047c0405405882c0c1d030401000c3c2000d0a444010340f190b183d120151105100190a9400e043c039a011580e10540203c0d1500090070090350348aa00d100d1502620f00103058a510403009107032202c66540114070b004019820501e4240d031169007036114400303a00c02e01c25000000901c240405d007218005050980f000200c042c0f03030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 684854730 1250 684853480 684853529
    0xd06030305190816080c04033806031005060a05030f010203090609060408300403110c01020a0c15110a06020405031507050a0305370605061c020a020115 67
    0x20b90290003030088020401134555203990b20404110f82d00c0c60007095039114003032280d996101b95000500405051100240c840070003030174000c0501c40707500d0125030800342e41c1c00d4040ca2120688030560700d03422003400f04121081700c3d002550420b4008156803201c9584078006494901d6900b400c2009035000b004206600100b800003541c4419818007038480c0b480d083c4e4412a0f10f100e0b01d142d584418592000b100f41300084c1000f052568401c1c0202c4c0f5240703081604000d0068081046103d4043c4914041e0740710075480417401107006940544209825070528007445c00425228100f042000084090741c8181c130010050f500c1c14a00501c801a503642c00d00c028142480c3c0c00714012803002c0661400c1c460450380c00300c1118100c400c24500094541c6510303004d08440141802c04840584424003405400c0c0d091081040e08185051002c00c10503039107405002c81c5000306c40004052403413076182d031525000e46800074a86a40765100002d91002080c1200350f4105441e00318050103410b911a0020b040d10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 684855980 1250 684854730 684854767
    0x40b130501170703020109090510050d0f0210050a02070303030b12030a0c170307080a09060603050f07082b0c0c09090b012c0604090813141306050619050d06030305 72
    0x800030058091113041d034002070510f080c1c9200d00c2402660b9000000d20410221100102404c0300400303100c94000e0505102802c40b03400207059104070109920664003d00443c111107001c00560080c1082e146181c82c19402007900d4140c581e0000030030340c82050307094400d100030b00b08004182c803000c1341c01c1d106042c02546664103072038100d041c0608005000045400c6400c060788503000d40070215800c1d4407482c10b00040d0040e640300400910401e61051000580421fa01c020744100310201d808486809082c08a514000e107800d00e094158a0000c03125a071080c2050386145025142181d0480e50710784101d0110b50051100761280a079090041c040c2c2c0e051405989040c129003803000440031030b001d442da0f03401d40e00900190300c21580e8006440800015000b0307645142e50300300f04403100551304e482906c0c0e05417070f078442c0c1485421407804180b04a402481006d00744c50020300a40d08045698404a01c08200e5400d80814042c2c1440511950003543c081c01028600c039940352600c0f403000d620128840103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 684857230 1250 684855980 684856019
    0xd05070510020703140d0905100b0f03010b0a05040e0f060106031a040504150e12130501030507080903070b0a02071407290717090604030b01080c090405030a0e040b130501 75
    0x10b00401401010961001002804044000d1000c2e0390701d04000181000345030300c8600400e1030148140c0d02040ca4800d9110040c0448181c5c0d0402c0a41c40803001c2500321b032030350a5141d9103c41a12818402400d19030b00003c1e007500350500310313001104006030f220f1a100c400d80c4641d000a80f01e0f030015102c405064600b40d8441001d40d01440307641829a80c010080001c501c0c1c80580683d9000d0880b00e042c0c04000000c5d15200180d4a141c0d00c600b08400400000700b02d000d42400b20341441d0104400510540c4120f11030710b6844055070030050255514029280050101c100311a000e00c40ca1021070061343e980f10701480741500802d1400d24012040704e13003181d2602c0d00b60540201100c69845810300e01d0464425590002c1c9440c80c0d00310a00088085001700c0c003126401450204000c8100000c0c1800c9074141c0741500129000c8440d40020030940031400c5070000e2003070b0010b02501d0351250040500e003038110b07801032001c030b6400d803c0804100740301440b00401ca10b80c2d4481c8010000c40f0180c640c00403480 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 684858480 1250 684857230 684857263
    0x13060c050906030a110f04090501080c0f0918120c0318010503090a08070f1b08070816060c020117090d0806060405031c0309170d1503120f02030403050d050705 70
    0xc03000d0001007050100801464540c2e454400955504200200312041c0c080e441c070700e00351101e442380d83c504000d003001d000711308003481155500c58981c50324444c05111100c1c010f0103054980d603107d43c1202c10b10403803003d11841c0c0c412a1004010004014017616803000844011910b80101ea11076410311659008107034103111041040c042140c80c0070891120440e0410b4000c0d0b6030303000e00d141404400c0719031000a131109064000040c21030310340c810884129036240040740d0300d041d00c1c2c00d1516200c1c0036800d800c04220003442070030080140500306e41c3c40320700d0050405a544a00440e210000440c0c1198104240c1d000010000e400d04c0d00b022480341c0000c0c05803003250602d41400086a520f1404440c050304204a65040d1006d42d0322075001000440d501c030160f030030040704220b0100080d402402650036030724100b0740d0304d603142555071054000b01ca0b04501c0f0b0900c00885120700ba6a00459021601c0460004202c0480428400c01107841c1040d8290345465072407034103050450601e4600e00c043c0041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 684859730 1250 684858480 684858487
    0x70e031507080601030213050a090207050601080d1d040b0301050405010222050915150f210f0402040f090c080f070b03010806010e250906030b04020c060c0306030703020913060c05 79
    0x1030a502c04040d5034803150a003401a501c1020f0b6085e0f075400340c0f1941c0500d511240350740000c5040c01d01074000d03042452041d02264096600c40390b40e1901c0301c4c1420700240c00607071001d02b81102404204880000301c1005000003c000a514000c01d094503022075082d20130382e4000030b49402c4481585142807810007888642903d1900300780010b400c07820081c0c450681c8840b082035071031260356a2802240c5441c1ea0050040e50342c6040b801c54081c41d08990780c00c2008408103540c51000d540301f11101407048070964410b2100e643c840e804c01c00200b1040501d804040e40d1110340c01c000824140000d0090080c00006200314415410307d90f14004403600000004c141c00d00c010800b804000070558151100c3e41c8100c0f00d10380d00c406d000c00d100d103082205c544d81c5005140d0450348450704020810141d411030364051205800a00030301003a88120000c1c40c2090b40320500054210046030050350304500c00405542680d59681c000981c0c010056138000201c0802860400c1000454440d9203000a000d051440c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 684860980 1250 684859730 684859741
    0x2d04060501051606140103051c050403080a2f0c04050901090807030e0d080301180b0301060602030d09170c030a02060609100e0702070918060609023f070e0315 70
    0x140c000c1100e1410310f0ba54020815040000c240c00490f940c5214005500040d81d407418030070360b1001e00281c00c03a12401c04941c2c080d40d40713200b482180e00380c27a0000301d864a0f00510300070461b107071240319100c41c80c180b00c01d00e044250301400c85d59040034411800010481d0351495420442200c00c084c200900681c50010303458006003a4100780d860709501030510758101c0101c0700108040c0b2007000f20082100400200101e05190311070598029100b41c0e035820411400c0b00801e01d42200d4441c06481c02590092004e03c07066001070f0010318001e41320307884948900c8503950942080da08100d0780503006405c08650100700c25070412541d5404501260381d0308582c00c0942c000101c900c1c81e405104c8002651200283d481030003040100d00404008108100490b41095840840c0e0b1014038102c2e021f074240134000034514624004d8483c24448a5480b81840260100702d03118481000361011204d0403c0b01e03001800390b030b5418514800c280300d0700d80020100c400000c041c10300d03051175490b6007680d07400000e105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 684862230 1250 684860980 684860987
    0x60b090108132303091003020301090b030a0206043003050a080718090905011404140d050403080906070f0f060c03060e070804080a0c050a0f030f05040e060d112d04060501 75
    0x800307815801e28080810f880016006086100e98403105402410f04000b440350564142c0c01941220041d21003004848140c0c0c1c105919021388030006948404281b0080c84199100c204038200d60020b17020700700030700c0d45d0002c07281d4900300f0f40c05060300802c10101e484040d01c2e0300710309042d51248840c500369000c0301c003401c10807480342c0d0309014440c816580c40c00c41104101d000d51002d902400300b0b1109840b00e260902d860802d013014503403606507070b0007030f020704408150150301035030f055950280c6198104400d034002e00c2041e8010b450240c5284004c00d004801081903108110f00c168011a800700da200848030020b025904c0503403041011401d0003041001c0d8a80c000301c2d007904940d109460070350768407e201d012070307012070401030142c00f5000c1c1140b92020406c08015601060748203846084002c010f1404c10f0721035008511814258600c2840090014680100484209481410328071910050040400d554111201e22200034840c404008201041c4008580c00e45c0f01044906114450074100003c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 684863480 1250 684862230 684862253
    0x110306160c060612050f07080c1804020a150e0f01111507050c030f1b07030b0c162102010e0105070c020906270a0c03060e010e0415060b09010813 64
    0x40c204411581ca4108016041c3c00060050840e42c2505110956034100181c989024108040300751003000d500040c00e04011500b4440603600030400100d01c6000b03494001180c100410499000e102420082110202c11840b0200384c1c15a64a40b0220445042400450000a0b01130f90502500a038901c969250014030070030704008a90b04141603031100341e000d981a00514850036050b01010410711104103840d800f0b80129445a200c600b00c881c1849012901c680c180c0c0406090b080c1701c0e4000903410031240c80180703e04042e29903110450a001d4542103500a080d29075285503c0c504149080c4603a82400307001e0341c42c2e842d2002045182000b00c0c1c05010741c50300250090003941a440010f840e42d0360140c0b2204900c44c103001c0030027604110710b4082011003084a9200c0c01900d050a00c8284070320038802c103420b4aa0100000b990750b401d0500b0f010250070000c03c11102d00d961008154018402400750000809110071800c3d280c40314500054880d4000800c00c1441740c001001d0a008110580c488 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 684864730 1250 684863480 684863521
    0xf15020f1305010c02300d2105040b010e07120606080939030111030c090109120809060c0102091503090d05090d02040c02030d1a15030424060f090207110306 69
    0x9022008035031903240040500c480346c221800c0c0680403070032803441d8200641c0903c0c600400c511000d090045013004044400569000e8007000c07298006101907400d500406801c1166407e000d2410503950545609071a8541c1080000628140912801d045c00b00300c0c1801081114116082c007440400481910600381201c0c00f44c1c2c03c0b440c1388002c01c0c40c0c0742075110010402c1c1d0958003699a1815082c91a910f03030001001030b00050260ee40090442c0c41030715111b0186501005032490b04400c08208256900542423645183d542013000074050303658443e40c2042002411902c40c1c483ca040200c90f400c20001c00c1009082c4a4200604401680c980b00c1101c0f403158101c600086080d84850104e02d10b024002c81c0c5040c261a040100765142100c8403a06800402122008072015114441489a010a441c000d160403a240c010b0071001c14054040c65050320007000008070660348011000721090281d0000640b598002592014030441100101c65550b00b03a00912990900c1c0d10703060846100c1202 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 684865980 1250 684864730 684864769
    0x409060b12071416050c09090304030803040206030a06050d11010f0302130506031807140a1208030403080c1e071b03030504090207230c040e01050709030f15020f1305010c02 76
    0x45414010954a050f1540c403c1e420104055a040c40c3c917000d0380c0d51642210040c841d082d40c20000b00746c510000102ca043d40e91001503a030175526030340d00380026074001420342a502d545550380466035440300102c111a0b00cbc010b0106d165141c0e141d1300054240d0306a10061b5003014010008507602d2036808120508444050b2002e03075480c1d8885001040c0c9148055400c0ca0501403810b00080501480212602110040b685170f180c0b5943e5410407d0300d00a0040002c0408000f0320015010900400f12950f21082c0300404030301c2c10b0f91042e181802c1c2d5142801e0f01d682d03002c0105044007840500350f8000c48494541c0d502d2100242143c0700602180514407540170759540000c3c0b40010024000141d0f10f10105001900070346c00000302c5000c2e200d50f40c43e00f846000350300d490f6444801321014061140030382d0b265141c00030f00c0390031030320b44014901500c0406d56100340d494018048404451008002c1e4003141c0d03d125450b011082c124180c3e0290359030002d410480000c034910052f0f030345d00c00c8003842e081c0c8800c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 684867230 1250 684865980 684865997
    0x50405100302091308031305150f070f0207080607020d030b03061510050403050a0b07080709150f0509090106030e0717190516030501201801050a180305030409060b1207 74
    0x44c6040c99020032000c003d26070360001c0f00780500e20b164844601e00d500c1c410000da69003000c0342e0f550304602e590105c1d0030f001400e0540011410440c0281010329a1501501c1038841264a40340803516040c029100c20f0010380c001c5490b03045070380e850300c6403081202080f4007500c032504116500b0300c1c3d006090300b492403107103109055400e4024040c40c2141c1c000c69001c17050b504641c9882c01d02041c1403a0480d851000300c0e103050000388500744252086c0d030a44013002c0c60380075500758458049540200400102d0140003080150042035a900801c4e58001c100c1560049400f0b0031000c002070a024081d84041444405020244040c030000303d00e0350010070604400086138662130074411b150030302c1403c0035802c18100788404000e221042d0042e40072007001e4808420742c0c00390240c00b84010310800024281e55240304240404541c8039600400e00b0315210b00d0032070309400e1100003074141c00b11194002c58030303584001410054002140102c000420300622118204460b9040200006030b00034140c608004888 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 684868480 1250 684867230 684867241
    0x3150e0c1215041b0f080726011b0e1c080a03150f030210090e07050f1204050606240702061812010912080105063901020301030b0105031f0c0507080a0807030605040510030209 77
    0x1c40c140c00b41448c201c00030700044103414051341801d600b0140520026000500e494040d041c01c96510700070b00820724122039840c034141c4a55201c1d4212941c040205138a4102202c880d031201d0350001c001d050005c4d00003664510b144100820703540c0c213020003000c0c00440c00b8100030140f80c5d0b0b0410f42d8402901d081940e17507034408039144100b40c4a022a941244907590040c1300030720000051862180750242d6190790940000a0f0140072081c4c2051084041d650800840b0014285a005001d10a09501c02d00d492441014002414501e880c616500c060391341d400508c0c14801c1245540d424041c0600700556294101300104601c0d2090040d9401e03400e0a5103503040e201e0900701a81264140814800580640c4880900e8040c1d8020f03c001d03035a404051001280300e14003c69200741c0441c926000c0398044100300003100203071607031301d4141051040c03d11050703000c100f60000130480f160080d9145085442e103840041c2c210740098210301d004601e0702003000301180d0401c0716039007070701e4040307803800710310b5491 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 684869730 1250 684868480 684868529
    0x4031e050f070501020928050d0f0b010305060f0708100302061309020301140a0503010e060f0a0608070303030c2d140d02040f03150e0c1215041b0f0807 67
    0x1011000500c91400281c4607040c40019030140c00c0c0048125902e44007d140507110052032204010ba80c0c1e01e016607401c0400c00d51500f18420364085215a41d0302c4144245138495503c054000d07801a503090300118200300b018810b034200258000281d0511000a040c0010400943c4080d400002e008080020b07031210b00c50140020720300100504d80c0b00b5075680da115001ca1500c030244d00406801540c0310381c0003080524046c000d1100b41c482000041846595202c040040e070600a000503580e550303030b000003007400c1d1340910103040518026103020603045100440149410300340d480f222400b4402d201140340d074800750074680000c043c03145091214181040340120051054180d044042880003e0014814804841490489026000b01207985840d240400c09841e4244415030598224000345c98040c0340c040c2e00a0b4000103280110b402071001d80c10b41910104e01900c054400c800402d6204e18980c00c09555100134103480075504202d2403806800e40e40e13603442c41c01108200e013016100c0c0c51140a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 684870980 1250 684869730 684869737
    0x8010509061816021006082107140c0f09360303010f0504110708070b070c080d0e0708030426030f071b0509040b040204051b0a0201060e0f04031e05 65
    0x412082e9603082d05003620401009244281d000c0e01600410303e02c0b00e4800142e201c1c40040303541085c00303410440444d4070000700600c800c100130602010700b880700c4000714400c091400c1e060501c1740c0042134450b900c0c0007004408100b4080045c442c2d0a80010090711000440038084500c1412194449140345c13011040c44550060854299a00c004800025045032680c2420f04a80040e0340800114501c1031a8030307654803c1c184d01400c4240b04000e0800014075084000e80d00c1a218509440c44901c0d6503907008003075020813800c50307a8544940c10b4000c001c0703023808000001d1485000851805107003000c2071400e040c403030501c1005800c940d812102e031b200e011300c11603d40c6088400d0740c6039903038028508544110340701c0c0c98101051441c0c000106460a0000c266801250800010703007513980c4542c20403005e4a4000c150110960610041032010046000506079000c00340c4c0011905c2d034108140392070100070080040031a00c85000c04d10001c207070031051451401c2003803451001c5480c00b40300191850321 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 684872230 1250 684870980 684871009
    0x501030f020f040b2e020105010b03070c0c0b04030f0209070306230a05100c050f03070804090507020a0804080d0305090c06070b07090519090b040608030409020d09080307020708060c03070801050906 87
    0x217401065034030304090140b401d441c0b000058801c20b0f8003031301100803400ca400034040c00c03814620170004955094000d061410710103118042d1503080588070091141e40b03030403603403084415120400f058811440c160900b158042c07154a4100310340c034a80206d10f80f00c0010800d0200c804181341031124019180c0201180181202816208241c45003103c010304c030580070041501c840c02900203405400c5400f20844000b6600201c07140d0806080515040050130058510002c4d0310820b44148005070046028000900030301019000c0e4414401c00075058900040c0900c0309034200001c110031981c1ca40054031500e5130400491701045d5a0742c3e03410717a101101e079048035521a518031011070b01030b0702000504007561040c06007800708424030814003003950700c103010f0704842e0742051000b80030010305030b0b024040034504002c1c04901d503c101c1e1116a2036610664500c40180c03c5a5418060340c401001090b0704028031b8841f107403442c03500c1c040040040106002ea0f61040c4107000200b503655980c0c210066424 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 684873480 1250 684872230 684872239
    0x2040e010e1f0504120f0e030d0f0f141b0f1c0e09040b01060e040b18040308010f14011b1406010e09070e340806090105040501030f020f040b 62
    0x460003014159105802c00c645000c039540c006400521003058002c050095600001c91203642c1e00038641500c00d09404040300040200819100c00350341d6041042c01d0811600d03480710040d02c2c500c2c4000130300100181400c401407184110f25401416084011a12203500c01a6100016442c0c45c0c1500c0c100710280340784074a140300e050007e00c112216502c046007104665181e01c8207921804c0c0901c200c203041264007614056800004001070380c02124070b20380d40840104001030241c0c000b40010740b110031300312942e411100c440081004064000c2d0003603016013000c040c2d0204280c90320300740300806800c00380d08131f04008a01d603004a800004080c040e0f0200d5000002003d08850169250b6849000f40304448900044d4008100c041d18045925415101d12840a404590312205080b10f04041c0f40303010414000040e03000d000c841c0c1d007000c1d400c04000c01c1b59511a01e9050101c10480c07580d8040c0c01003407040340341034010400a5404040c1f580303407943c1a40c401040100400018006009649000703400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 684874730 1250 684873480 684873491
    0x30c07091508070609151b0201030f20070b07030203060a0603020c280201020c091012050f031309050106140d0504060f020406051c2705070b0f0306012601090902040e01 74
    0x2c4c0754208500c44d00f610100c0440303940540802004492090280d4401c40c00303082214241c0c40594881d0f003110494082e20800414042020f400391040304441c10300d03d2220403c00b0400c00b040058410480790032041c54601075045080c9080050b0a50003c3e1081805055000520001c0000284040a40111180c07a902c00c4d5104082040a841e07030f9020040b0b005014600c1ea84550349040605140125441d022013284641000c0281c440400910300130341d014401c5544141c0034000810080817682c40d21b0142e0350100c9d190220b4001910300c180c02580501516078003500c10200030906031205049040804111a141d070b06081004011103445902840e000060101f032598019000340320403203c1d025494941c03480d040700202141c180381c2c005015144a0a59404a108074950161610380104140c0c1d4903103551700e0816905501c400d900c500d40007004400c2011540c5c2140c50307403c1d80c2c41da0080060502801400e5003007058014041c02103416511044034041d5107070b0b603104c0d5420074040f034001c000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 684875980 1250 684874730 684874739
    0x110603101203120b10051b15042d02090f073b0105040302031c2115150206060120030f03010f05060c15070c052d030c0709150807 57
    0x300707008100c0510f08036060541c00741c000d0800465a02c03070707902c4d00d41e642400c00c900039494101101c0e00807440c0744a0b1103101040380c030403d9001c43c51801139114190320b084442c0707182c1c13400d18600900354442e00c1010590440c2e00140e00d944004540c011808184101503507642d0a084d10000004680548c848541d401c0007140004d01a6200c0071710240c81e0b100c2d01c086490140110b07103e10440c00000d425800000d031210502e0314115440d104c40541d0706050b812070200c144c014022403510452100701c283c8030500b2070000c808858103000a040c0141c00c8510809040300c0c081d5594001504183c1000000c0300440c101c1c04401481c191440300ba00140ca5445942c40e03039a5a0700c0d002070084811703c40b4113900c001a20320704241195500042840581300910040c03402e0610320000401c04001c0c000101e842c0800204140001980c0b410042d43c9400000800d0003d40d009200800c2e400901e51310401c03040042d10700024035030040b42d2840c08081041100031a031011540d00c00e910001d21841010400f15 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 684877230 1250 684875980 684875987
    0x30b150d0903080105060403030905040b0f060304110a0e060d110102100c02060619120605071701120b0f060a030b060402070c0e090f0c010c08280507031704110603101203 75
    0x1e0720680079568086040e600c0d2003c20800b1b01c44c03440010040386c4100d10400150034150020044400d004010300d46400489001ca480c0340d004480840d600e26609155003928a810603c50b00030740140300c0c1d559014502680400c1d5044802c0343d002d001c210700b4a4209109a1080081e480711050700b800a2040e0840210007a40d103000954039284aa000020000c1c4081d194403800000c079222102c0b41001c2000c0c9444a80c028a805442e84d41040351504044030303005030610504d402014401c07002002c00c0c9003410125000d01c00500720b4003004249030f0a00c00c2c0341d51070100c80e00c283e9801c40d5421260380c80340d00025009210f1158014051144070400103402c0c241c0c4403415224400110a407442e40300d05040054030f862030041d1280c0441d0f4a03412040100d600038001c0e000f20400c0034124907581c0c0815000880d40e480c80346c404030002d00700207924020540e000058581c000c0c0d0940041c0300906181d983c13031070940342044656024550101c000f850700c03041005141c00500b07500811043d403da242c10000c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 684878480 1250 684877230 684877241
    0x180b1306180c24112b02100e060610020c0301050a140c0c03040918060609020913060e01060503220c03061a1003150801110903071a0a030b150d 63
    0x291007030a02d004000841d503801e08000082c08100300b406041c0c4a0f0844010348040d0304c5009409450311031681c0c3c100301040070307110343d1800c000581d03100b02c2500358150340249400e683c031061210250900740700c1c03c00c09400041c8113070810340844900c465602d50700c500300d2805078101d8403039501d58204020303c0100344184d800b6401c0d00c40320f20100c508955841261640a120b540c0c130078202a802080b04014500c1207601c85040b2500300b14610052505075142c0c04150762090304081d985542c00507140074989404034074030030303c0e054601d010b000300e030b00d400e9100480842c1403040800340140080021028000d000c04da4950110a510301c0d289450039060120b0381851500085440e2032800c00e185032811510840d81e000c14030010400304d5601c044810840150101081ca00c101240320f0340c0105030a0300a0044080c0f46030f080402a403992046420545403c0b16940880c1e400b840c1c7c1f0140c0a10481044101c8031048414103001ca64000c4d0207000c01c035050400070022000310008500100c1c088a2074004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 684879730 1250 684878480 684878483
    0x501030203060f090d0c0c09051801051003030c020405040326091b0915030f0f0a110603040818061908070f0905030c150d020c070603050901180b130618 67
    0x866900e0b40d5104458805030809440300b0001d0740c824030400485c24030401c10303528000c2c414401000a40d0b555078054054400940301b092000541c040140b40d02c1d5424403c6540c0140e032407a0000c0711074a1500e000d40072590541002e40a142c86500040a0500541002e48004035100410181002e20042c015030f611064410240038010810741c100c8010000e0788c40c03039030440001d1905442da1a43d01d4880780c0030190210342034040c09070488408a666051080c40c4410200d800944495652490806101e50940014500c00c00381441808086100700b020307100c28040e101400076201400c1e000051590003411445203210501d401c40e01c0403254000c4565001d000b1726211440c2004c84e495040d0340f07200301c0340038944d0180c0c050760096500e071a01c80d18010008000f0712031245450007d1445c03030300742c2c1e00441c5400c0e080e5010302c008100c020f0b40341c810540e00c02a503400030019124102180405005030450180c07946d1000004140c100c414101d807140095403000003007080041d04ea18410450121020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 684880980 1250 684879730 684879733
    0x70e1e033a08010b0414040e061e180723060a03020a230a03020d0b0307120c0602060f0402100e1905190311190f030302061501020a03201207060501030203 68
    0x2004802680190042e5059401c0081e44a0400382486400002c030041c4402282e0f0054566549248102c028000071707000340000c030b18200381014044040700b82d160f006400446601401d04580c22891400320301a801e56807034010910b801d000e90840c13416214444105a45d011b8000103012031841c0d0194024904044035480f42d031586410401c541c096140103015486200c0e20401c042c00e8a94400c1e40109903091101c41c000481c0314240020038509100354100b05030503506185c5480074017014102000080000340b0040c02c803441c1004600b8820b05000d4002805502c3da10b258004640c0030f8910307401404c80c0500019501d0301c0040d0300008407070362442110301441001d03220701410300d07001c1507140031789400c0490061200c81040c10300c10001d0400d820340b20940200a0702181502c00d440309480110701944c003c2901c1d04003080c90301680d02d0310400c041e055501803184031002a8102c03550220001c4112000c0e60f144504200d02c6081480e800280c42c05000000380d034108000d0150300c0350b03042c0d074000d50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 684882230 1250 684880980 684881083
    0xf0112080f1306031d1020030406050a0506030610031e121e0e09180c060c030a090f1809110a06030f231603090f1a070e1e03 55
    0x101e05c1400d698540341011626001001805006041030b007148240c0806071041441210303030081c060269400c01c0c0d8084546940304c100344200455680a555080381d4100c014002c5ea0900380450740c030340c6c6402e00c801004141462480e505913084040c1182810b604240c0c80100b030301d0460700c02003203840302c0c0ba5862440818030240450701e41c80340d588540c0b00c7e0009044103859803524900c8543c0201304100720000d03031061214046a83e01c402c00500320440c80b2400450304e540458401a001810680140c81e0141140c1e908100c0da4000410070f000041202c0f0001940741c81609280380c078410340c05081038018040301c0000480c1c9506610500d003c004a01040103050f820b103140341d81d0f030542266001c2c14541c1100210717000d00050200100c200d1164100040c4900c502d0b50303103141074621400c4c180c070560801c6000501c07900d07071100c6899001c000b519211404c021954002001c044200e043c0c00801040400a40c400351820003449601d02c2d1740d41d46024180c0034400c40f000c002d03d8030001c1d503005080d034407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 684883480 1250 684882230 684882251
    0x10306051006110705010e13060608190506010507020402070203010b100507170a080105060d06150905091308030c0901030603080403060c02190203100c0507020904080a1103030f0112080f130603 85
    0x2560f420003905400400303080b0603450000115400180340c031100d42d000d030303030002c8078280a0380c7c0d846468010705284c0c41e40c00caa0f26200c1c0010b90446841003803154030504140030007240760781c002c0c00c4407100f0f41d0488005884030b249002090042c2a000e10741500007244c50b09002d01250050094010288558000c14441e010782c0182d4041d4011119100c02150720400107001514200b00940b95140c41544001049581e401d60114090301c0750240b10702003100e251003404182081110741d0340c011104104840301070010755441182d4440105592072020007c0f80090f420384c460341000005541009040d622182c603810305a0082000c03a000070058841d00101d005140d4040c5012025541c000f4064001e032240c0302515005000c03240004400c10200304110710050341d44216a90080c0e010310750042d110080c3d100c002e448000031031040c0e401c0d03503c00d1040201e0121007139801c03415580c4520811b01c40341407511f80840d90f4001c10101d040d06003c00701c0c491a00300c0340600715100701c0d049a40c0a00c1540400e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 684884730 1250 684883480 684883487
    0x306010e15030a350a030603110316060809030903030408010b0102011503150207081b07081002040e060d0c0302030a0812070807120c1e0908060711030d090206070b010306051006 78
    0x91000081c60781100c903001c60b0071400d0881604000c03414290302c03131900360001006801c456004601202c0800d9440009100b8840c030009149030a000c150010048041240407458420842d40300d800100b0a80c03c00050010009100755400014013804803901c640d103807460b60303020302a45080b090066203003c4411401d40b001c0075544089a80085c500b040e4070035203000c22806503218183c20303904640100301103206041c0c110142c1259030414800f40510340d045c885001c1c2048030402120020724010b01052201d41601da07500381d08032404840c89004e029107031801c1c0d480c441c040e90000e5414001c030640c4205102d600e00007007043c1c4440b14611b03805a51103000c20f40e880202034458800040180c0000702d1200c0c0c141d8030044c0340140c43d01b00701d1348900310b42e01c242440660007081c280c0007400f0300c1010000c0d42130070030019400100074180f181c400c5400030b9105689000c0d00450b282560340300c0842c030381552156005c494965401000746180c0c1d6850741000d00c041c1c0300035103a0f115640c44a82000400611 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 684885980 1250 684884730 684884743
    0x61e03140d080a02070602092e050f0a03090212190b01060201062301090503120a090f2916061a091006140c060403020f0601152307020306010e1503 65
    0x294485403510f450b8056810020f41180c181100ea1035420810019107540300144c550f17814034030310b0070704201100e007503050240c29608500340001e100d000e20070642200e03040c406072aa03000103450002180f0005000080d4042ca042d0446851406011000703a40c0403982030100c41924050b100710300c401c1e41d990604900b210b100d1300c52070068561109200c040d140b0416119035003100141340429a158513600068101080352021440403140016040242e940140c600c0d401810400c1803200131a1070f10303c01c042c0407400c074015442c400c641514140e103008042d206840300f071a0b107502008000c103031a1525000a052041602e40703c3d1140201c170b074101e8944180024030880d0703404642900a0300c4d281c0141c421008084a0102e040350500050021000c10030550344a1030181c0e00401714030940408035400c00c5410782048005040c142c42c1407003080c0c1c01c41d8441030307010843d10b08441d584c1185030b00d40d1158040d40703a000b545402040000148180600c07601401413054020070a000300c0000205503841c034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 684887230 1250 684885980 684886003
    0x10b0306120f1207050a06240f2402190503130905060117190e060609070923011b060b0a09060305151e01080a03120e03160204061e0314 60
    0x3440503440c0c00004100e04082d00c52241705004442c1c3c820300d640e855109a0f0851452001408205140c2d00c7d29240d030300301902c0c0281400b07542d059505003417035401008108480340c0c010a4007000c0e41d458115500c2007107480b06180c0c04420004c554680c1c0d01d0050340381e62003803100e0310a4050440c808680750f0300074031409004d408161110281e01c10785210741c4180000052080c2501c55500c0040c007203104160007000010113888000e04100d18040041161220000e011803040140d012002d0203c51000b400906007840c04401080005400b100100c0b100000344001d805100d0381d0701011000c011080c1c100402140d811507588000380d80b140c2d2a00121440c2d4880030b005a840381000c034260311200e1360b810b42c002c08002c4c00800e809140014441d0b4185007070307000400326400600e2130810305900c01002e0b80841701030402030118186240c2420380c4e0707000d40c007004801000340c101075004565880c2d02c400c00410311003c5416003041540302d2180103c55130310040e19555000b190000d4181000300712032800d135 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 684888480 1250 684887230 684887233
    0xb040914060306130201110d1206141c020418060f050117210409020c03030a050106180302011d0301230907050603070f0306050d08190c0c060e0612010b0306120f 71
    0xa98a244c1044d116521000302a41406000c24003454858001c0c04080b020658030340300c0000350340c01141c00b68129030556202e07003003480314808010299561042c07072481c0e116619052650314006400090001e00000301e014540480300c180010030801d680d003000c1e503030b5007580504003c0390783d80e480c8000c0c136001081d02282c2c1c1030300207042d01012155481c29640580444d82d40309800d040d1640401d4040b84d1013600700d820981e00102c10400100840e0080300d016120300d180c8079000c5110f04443e9800b010b03240c00001d0500c92101070b02004020640354000104000800900268049029540c401d1b0005014680540d011200044081c0d5000409800702d440180c030261071595040750440385050503814800801d501c60700c0019032a0784030020b945040e0f01410b0599960250300d4001c0540840d0314100c5014001c0c1074000e00049060309260408944990405810704101c950009502e0310031941e941c10210100070020520030713003200c0658032850b001d6401031002a01e8400300f503500d41e002076840005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 684889730 1250 684888480 684888493
    0x414010608010506071103030f13120c090207150c080601030b01021504061d011109010e091303120207050f070f0e040b0a09141b0103050c07021807050705070b0409140603 75
    0x581080030007021703840d0142513203074020580200000c2c15540180c0c51500003e101040703445c03160204010900007000441c241200c102c000b5a107200c24028030703108100c45658080b81c41c0c010712140f9002c0841114400108000010303200f100540400007d0b148240000d1070056201c1031540001400c085270011510503d0440c0d450780d483c04c0181400303000003150315001d0040e40b80c0d1b02409020f0082c092003860b1445441d0f258100004280008016195104440a41c10300441810a40300003603c1500341c80e020711240140d05402c000382c032907101c00908034407070080010038800005c9170240c00d5400511030404560350b6000380c002c00040544000c0c0004030044c0102c1c02882099000e110183e20905104040843ca004458200050300c43c80050420001c44190704541e4144100340c4d108030012049418101e82c0d401144c4000301042c460511042c500000c00c2480b03005005581100b94424201c50a16880708901c000039003180c801d074680c81e401d1130902d40c001c428404146200716070103001003c9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 684890980 1250 684889730 684889739
    0x1906060504180809010c051603060b0607020d06090611120906090102070b07081b0415230a0e060c07061119020d11130c030c11060736090b041401060801 67
    0x40f160f10001805043c00485113000000030814031007401200c3c0c0412210300c0e407900d94240541500d8030108954450301041000e200103039a08400020740790f8010400140c121110301d0420002c00540d0034085038580701082c100380c000c0220014500c208101001d8a1154903190401401c0c2c0c001c0110040140e4941c100040b5000e01c902e0705070303034040158084200320880e0003401c00005e5001e500142020003a804800040c2d5800c031003003010301e001c00081c4008030340d100340806034503018494610b020481e84051583c00703552201d00707075001c03030300c0d007031b0948656513682d01005d011010414a4803416005100c0a00310482403107031144140c54010341301012203c1c041c0d03100d6044041e140002a032000400d40d0a510440703551190000180c1640c5000500801404001d0220707400b400c425040396000d4020854a95400030b0225580740900d140c103024204000c20717500e03041542c900b800d61100209613001a0050300b917004103c12100c1920304001c440ca80711700d4400c45407024003600002c140c45000410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 684892086 1106 684890980 684890993
    0x910080c0909071505042310030b0d030f030e060103030e030f0a320105092107020f01050307031409030309070b190f030e190606050418 60
    0x21146881e61280b552070f9924010882d0743c070540b480c0c810745603001c0c4066070040d0003c205c0c0301d143c10004070020300700065907640461054240100406c1d0841c002e110340b01041102400c84504512191030070fa4112001d1294003042564940044130000c00500186019500c6903450405158100e01050314040555942404075080454041c00040d03450501e280901c161980414038000c00700303d1b000c1d0701071240071000c015508020030440b0400300801c40c40c0066010100480d450340e0303010341881281c020404002c0d00460510780d4581d8035070140000c5c0da800314503441c0204031020503545860041d142654a01038540c00401408025a41032080c00040c080c043c082030b0400b0243d00c4400d4070f5200041d210000d21100741c40140b51944260071001200007040202d607030301140300c099091000070802c002e17034806180c1000841c146c0b40902604040b07443d01c1e003000030700da56143c0b40d14 = true := by decide +kernel

theorem cover : BRFrame.Cov 684712230 684892086 := by
  have h0 := BRFrame.cov_init 684712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 684712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 684712230 ≤ n) (h2 : n < 684892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
