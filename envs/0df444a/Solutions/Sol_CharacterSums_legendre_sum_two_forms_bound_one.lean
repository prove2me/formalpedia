-- Prove2me | solution 1 for CharacterSums.legendre_sum_two_forms_bound_one
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T12:35:19.124668+00:00
-- url     : https://prove2.me/submissions/a4669bde-13b3-43e9-b4b7-fc23e37ef446

import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

set_option maxHeartbeats 2000000

-- ===== Salt.HB.QuadCharSum =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Complete quadratic character sums (Heath-Brown 1983, p.217 omitted lemma)

Heath-Brown's *Prime Twins and Siegel Zeros* (Proc. London Math. Soc. (3) **47** (1983)
193–224), at p.217, states without proof: for a real, primitive character
`χ (mod q)`,
`∑_{t=1}^{q} χ(u t + u') χ(v t + v') ≪ (q, u v' − v u')`,
remarking only that "the proof of this is straightforward. We shall omit it."

This file supplies the proof at the heart of the estimate: the *prime* case, where `χ`
is the quadratic (Legendre) character on `ZMod p` for an odd prime `p`.

## Main results

* `quadraticChar_sum_mul_shift` — the keystone identity (QCS-1): for a finite field `F`
  of odd characteristic and `e ≠ 0`,
  `∑ t : F, quadraticChar F t * quadraticChar F (t + e) = -1`.
* `legendre_sum_mul_shift` — the same, specialized to the Legendre character on `ZMod p`.
* `quadraticChar_sum_two_forms_bound` — the general two-linear-forms bound (QCS-2):
  `‖∑ t, χ (a t + b) * χ (c t + d)‖ ≤ 2` when the forms are non-proportional
  (`a d - b c ≠ 0`), together with the trivial bound `≤ Fintype.card F` always.
* `quadraticChar_sum_two_forms_eq` — QCS-2 *evaluated* (node WEIL-TRIO-W4-c0): under the same
  hypothesis the sum is either `0` (one form constant) or exactly `-(χ a · χ c)`.
* `quadraticChar_sum_two_forms_bound_one` — the sharp constant: `|∑| ≤ 1`.  This is the
  per-prime input of the composite bound (`Salt/HB/RealPrimitive.lean`), where constant `2`
  would cost a spurious `2 ^ ω(q)`.

## Proof of the keystone

For `χ` the quadratic character, `χ⁻¹ = χ`, so mathlib's Jacobi-sum identity
`jacobiSum χ χ⁻¹ = -χ (-1)` (`jacobiSum_nontrivial_inv`) gives `jacobiSum χ χ = -χ (-1)`.
The substitution `t = -e x` (a bijection of `F`, since `e ≠ 0`) turns the target sum into
`χ (-1) · jacobiSum χ χ`, because (using `χ(e)² = 1`)
`χ(-e x)·χ(-e x + e) = χ(-1)·χ(e)²·χ(x)·χ(1-x) = χ(-1)·χ(x)·χ(1-x)`.
Hence the sum equals `χ(-1)·(-χ(-1)) = -(χ(-1)²) = -1`.

## References

* D. R. Heath-Brown, *Prime Twins and Siegel Zeros*, Proc. London Math. Soc. (3) **47**
  (1983) 193–224, p.217.
* K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, §8.3.
-/

namespace Salt.HB

open Finset

section KeystonePrime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **QCS-1 (keystone).** For a finite field `F` of odd characteristic and any `e ≠ 0`,
the complete two-shift quadratic character sum is `-1`:
`∑ t : F, quadraticChar F t * quadraticChar F (t + e) = -1`.

Classically (Ireland–Rosen §8.3): after normalizing, `∑_t χ(t(t+e)) = -1`.  We route the
argument through mathlib's Jacobi sum `jacobiSum χ χ = -χ(-1)`. -/
theorem quadraticChar_sum_mul_shift (hF : ringChar F ≠ 2) {e : F} (he : e ≠ 0) :
    ∑ t : F, quadraticChar F t * quadraticChar F (t + e) = -1 := by
  set χ := quadraticChar F with hχ
  have hq : χ.IsQuadratic := quadraticChar_isQuadratic F
  have hne : χ ≠ 1 := quadraticChar_ne_one hF
  -- Jacobi sum of the quadratic character with itself.
  have hjac : jacobiSum χ χ = -χ (-1) := by
    have h := jacobiSum_nontrivial_inv (R := ℤ) hne
    rwa [hq.inv] at h
  -- `χ e * χ e = 1` since `e ≠ 0`.
  have hee : χ e * χ e = 1 := by
    rw [← map_mul, ← pow_two]; exact quadraticChar_sq_one' he
  -- The summand transforms under `t ↦ -e·x`.
  have hsummand : ∀ x : F,
      χ (-1) * (χ x * χ (1 - x)) = χ (-e * x) * χ (-e * x + e) := by
    intro x
    have e1 : (-e * x) = (-1) * (e * x) := by ring
    have e2 : (-e * x + e) = e * (1 - x) := by ring
    rw [e2, e1]
    simp only [map_mul]
    -- χ(-1)·(χ x·χ(1-x)) = χ(-1)·(χ e·χ x)·(χ e·χ(1-x))
    rw [show χ (-1) * (χ e * χ x) * (χ e * χ (1 - x))
          = χ (-1) * (χ x * χ (1 - x)) * (χ e * χ e) by ring, hee, mul_one]
  -- Reindex: `∑ t f(t) = χ(-1) · jacobiSum χ χ`.
  have hkey : ∑ t : F, χ t * χ (t + e) = χ (-1) * jacobiSum χ χ := by
    rw [jacobiSum, Finset.mul_sum]
    exact (Fintype.sum_bijective (fun x => -e * x) (mulLeft_bijective₀ (-e)
      (neg_ne_zero.mpr he)) (fun x => χ (-1) * (χ x * χ (1 - x)))
      (fun t => χ t * χ (t + e)) hsummand).symm
  rw [hkey, hjac]
  -- `χ(-1) · (-χ(-1)) = -(χ(-1)²) = -1`.
  have hsq : χ (-1) ^ 2 = 1 := quadraticChar_sq_one (neg_ne_zero.mpr one_ne_zero)
  rw [mul_neg, ← pow_two, hsq]

end KeystonePrime

section TwoForms

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A single linear form sums to zero over the whole field when its leading coefficient is
nonzero: `∑ t, χ (a t + b) = 0`, since `t ↦ a t + b` is a bijection and `∑ s, χ s = 0`. -/
lemma quadraticChar_sum_linear (hF : ringChar F ≠ 2) {a b : F} (ha : a ≠ 0) :
    ∑ t : F, quadraticChar F (a * t + b) = 0 := by
  have hbij : Function.Bijective (fun t : F => a * t + b) := by
    refine ⟨fun x y hxy => mul_left_cancel₀ ha (add_right_cancel hxy),
      fun y => ⟨(y - b) / a, ?_⟩⟩
    change a * ((y - b) / a) + b = y
    rw [mul_div_cancel₀ _ ha, sub_add_cancel]
  exact (Fintype.sum_bijective (fun t => a * t + b) hbij
    (fun t => quadraticChar F (a * t + b)) (fun s => quadraticChar F s)
    (fun _ => rfl)).trans (quadraticChar_sum_zero hF)

/-- **Trivial bound.** The two-linear-forms sum is always bounded in absolute value by the
number of terms, `Fintype.card F`. Holds unconditionally (even for proportional forms). -/
theorem quadraticChar_sum_two_forms_trivial (a b c d : F) :
    |∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)|
      ≤ (Fintype.card F : ℤ) := by
  have hq : (quadraticChar F).IsQuadratic := quadraticChar_isQuadratic F
  have hle : ∀ x : F, |quadraticChar F x| ≤ 1 := fun x => by
    rcases hq x with h | h | h <;> rw [h] <;> norm_num
  calc |∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)|
      ≤ ∑ t : F, |quadraticChar F (a * t + b) * quadraticChar F (c * t + d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : F, (1 : ℤ) := Finset.sum_le_sum fun t _ => by
        rw [abs_mul]; exact mul_le_one₀ (hle _) (abs_nonneg _) (hle _)
    _ = (Fintype.card F : ℤ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **QCS-2 (the main bound).** For non-proportional linear forms (`a d - b c ≠ 0`) over a
finite field of odd characteristic, the two-form quadratic character sum is `O(1)`:
`|∑ t, χ (a t + b) · χ (c t + d)| ≤ 2`.

In fact the sum is `0` when one form is constant, and `-χ(a)·χ(c)` (absolute value `1`) when
both are genuinely linear; the reduction of the latter to QCS-1 is via `t ↦ t + b/a`. -/
theorem quadraticChar_sum_two_forms_bound (hF : ringChar F ≠ 2) {a b c d : F}
    (h : a * d - b * c ≠ 0) :
    |∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)| ≤ 2 := by
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · exact absurd (by rw [ha, hc]; ring) h
    · -- `a = 0`: the first form is the constant `b`, the sum factors and vanishes.
      have hsum : ∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)
          = quadraticChar F b * ∑ t : F, quadraticChar F (c * t + d) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [ha, zero_mul, zero_add]
      rw [hsum, quadraticChar_sum_linear hF hc, mul_zero, abs_zero]; norm_num
  · by_cases hc : c = 0
    · -- `c = 0`: the second form is the constant `d`, the sum factors and vanishes.
      have hsum : ∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)
          = (∑ t : F, quadraticChar F (a * t + b)) * quadraticChar F d := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun t _ => by rw [hc, zero_mul, zero_add]
      rw [hsum, quadraticChar_sum_linear hF ha, zero_mul, abs_zero]; norm_num
    · -- Both forms genuinely linear: normalize to leading coefficient `1` and use QCS-1.
      have e_ne : d / c - b / a ≠ 0 := by
        refine sub_ne_zero.mpr fun heq => h ?_
        field_simp at heq
        linear_combination heq
      have step1 : ∀ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)
          = quadraticChar F a * quadraticChar F c
            * (quadraticChar F (t + b / a) * quadraticChar F (t + d / c)) := by
        intro t
        rw [show a * t + b = a * (t + b / a) by field_simp,
            show c * t + d = c * (t + d / c) by field_simp, map_mul, map_mul]
        ring
      have hbij : Function.Bijective (fun t : F => t + b / a) :=
        ⟨fun x y hxy => add_right_cancel hxy, fun y => ⟨y - b / a, by simp⟩⟩
      have step2 : ∑ t : F, quadraticChar F (t + b / a) * quadraticChar F (t + d / c)
          = ∑ u : F, quadraticChar F u * quadraticChar F (u + (d / c - b / a)) :=
        Fintype.sum_bijective (fun t => t + b / a) hbij _ _
          (fun t => by rw [show t + b / a + (d / c - b / a) = t + d / c by ring])
      have hval : ∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)
          = -(quadraticChar F a * quadraticChar F c) := by
        rw [Finset.sum_congr rfl fun t _ => step1 t, ← Finset.mul_sum, step2,
            quadraticChar_sum_mul_shift hF e_ne]
        ring
      have hq : (quadraticChar F).IsQuadratic := quadraticChar_isQuadratic F
      have hqa : |quadraticChar F a| ≤ 1 := by
        rcases hq a with h' | h' | h' <;> rw [h'] <;> norm_num
      have hqc : |quadraticChar F c| ≤ 1 := by
        rcases hq c with h' | h' | h' <;> rw [h'] <;> norm_num
      rw [hval, abs_neg, abs_mul]
      exact le_trans (mul_le_one₀ hqa (abs_nonneg _) hqc) (by norm_num)

/-- **QCS-2 evaluated (node WEIL-TRIO-W4-c0).**  Under the non-proportionality hypothesis
`a d - b c ≠ 0`, the two-form quadratic character sum takes one of exactly two values: it is
`0` when one of the forms is constant, and `-(χ a · χ c)` when both are genuinely linear.

This is `quadraticChar_sum_two_forms_bound`'s proof with the final collapse to `≤ 2` dropped;
the sharp corollary `quadraticChar_sum_two_forms_bound_one` follows.  N7/`RealPrimitive`
quote it as the per-prime input of the composite `gcd` bound. -/
theorem quadraticChar_sum_two_forms_eq (hF : ringChar F ≠ 2) {a b c d : F}
    (h : a * d - b * c ≠ 0) :
    (∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)) = 0 ∨
      (∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d))
        = -(quadraticChar F a * quadraticChar F c) := by
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · exact absurd (by rw [ha, hc]; ring) h
    · -- `a = 0`: the first form is the constant `b`, the sum factors and vanishes.
      refine Or.inl ?_
      have hsum : ∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)
          = quadraticChar F b * ∑ t : F, quadraticChar F (c * t + d) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by rw [ha, zero_mul, zero_add]
      rw [hsum, quadraticChar_sum_linear hF hc, mul_zero]
  · by_cases hc : c = 0
    · -- `c = 0`: the second form is the constant `d`, the sum factors and vanishes.
      refine Or.inl ?_
      have hsum : ∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)
          = (∑ t : F, quadraticChar F (a * t + b)) * quadraticChar F d := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun t _ => by rw [hc, zero_mul, zero_add]
      rw [hsum, quadraticChar_sum_linear hF ha, zero_mul]
    · -- Both forms genuinely linear: normalize to leading coefficient `1` and use QCS-1.
      refine Or.inr ?_
      have e_ne : d / c - b / a ≠ 0 := by
        refine sub_ne_zero.mpr fun heq => h ?_
        field_simp at heq
        linear_combination heq
      have step1 : ∀ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)
          = quadraticChar F a * quadraticChar F c
            * (quadraticChar F (t + b / a) * quadraticChar F (t + d / c)) := by
        intro t
        rw [show a * t + b = a * (t + b / a) by field_simp,
            show c * t + d = c * (t + d / c) by field_simp, map_mul, map_mul]
        ring
      have hbij : Function.Bijective (fun t : F => t + b / a) :=
        ⟨fun x y hxy => add_right_cancel hxy, fun y => ⟨y - b / a, by simp⟩⟩
      have step2 : ∑ t : F, quadraticChar F (t + b / a) * quadraticChar F (t + d / c)
          = ∑ u : F, quadraticChar F u * quadraticChar F (u + (d / c - b / a)) :=
        Fintype.sum_bijective (fun t => t + b / a) hbij _ _
          (fun t => by rw [show t + b / a + (d / c - b / a) = t + d / c by ring])
      rw [Finset.sum_congr rfl fun t _ => step1 t, ← Finset.mul_sum, step2,
          quadraticChar_sum_mul_shift hF e_ne]
      ring

/-- **QCS-2 at the sharp constant `1` (node WEIL-TRIO-W4-c0).**  For non-proportional linear
forms over a finite field of odd characteristic,
`|∑ t, χ (a t + b) · χ (c t + d)| ≤ 1`.

The constant matters: the composite assembly multiplies one such bound per odd prime factor
of the modulus, so any constant `> 1` would accumulate a factor `2 ^ ω(q)` that
Heath-Brown's `≪ (q, u v' - v u')` does not carry. -/
theorem quadraticChar_sum_two_forms_bound_one (hF : ringChar F ≠ 2) {a b c d : F}
    (h : a * d - b * c ≠ 0) :
    |∑ t : F, quadraticChar F (a * t + b) * quadraticChar F (c * t + d)| ≤ 1 := by
  have hq : (quadraticChar F).IsQuadratic := quadraticChar_isQuadratic F
  rcases quadraticChar_sum_two_forms_eq hF h with hz | hv
  · rw [hz, abs_zero]; norm_num
  · have hqa : |quadraticChar F a| ≤ 1 := by
      rcases hq a with h' | h' | h' <;> rw [h'] <;> norm_num
    have hqc : |quadraticChar F c| ≤ 1 := by
      rcases hq c with h' | h' | h' <;> rw [h'] <;> norm_num
    rw [hv, abs_neg, abs_mul]
    exact mul_le_one₀ hqa (abs_nonneg _) hqc

end TwoForms

section ZModSpecialization

variable {p : ℕ} [Fact p.Prime]

/-- **QCS-1 for the Legendre character.** For an odd prime `p` and `e ≢ 0 (mod p)`,
`∑ t : ZMod p, quadraticChar (ZMod p) t * quadraticChar (ZMod p) (t + e) = -1`. -/
theorem legendre_sum_mul_shift (hp : p ≠ 2) {e : ZMod p} (he : e ≠ 0) :
    ∑ t : ZMod p, quadraticChar (ZMod p) t * quadraticChar (ZMod p) (t + e) = -1 :=
  quadraticChar_sum_mul_shift ((ZMod.ringChar_zmod_n p).substr hp) he

/-- **QCS-2 for the Legendre character (main bound).** For an odd prime `p` and linear forms
with `a d - b c ≠ 0` in `ZMod p` (i.e. `p ∤ a d - b c`), the two-form Legendre sum satisfies
`|∑ t, χ (a t + b) · χ (c t + d)| ≤ 2`. -/
theorem legendre_sum_two_forms_bound (hp : p ≠ 2) {a b c d : ZMod p}
    (h : a * d - b * c ≠ 0) :
    |∑ t : ZMod p, quadraticChar (ZMod p) (a * t + b) * quadraticChar (ZMod p) (c * t + d)|
      ≤ 2 :=
  quadraticChar_sum_two_forms_bound ((ZMod.ringChar_zmod_n p).substr hp) h

/-- **QCS-2 for the Legendre character at the sharp constant `1`** (node WEIL-TRIO-W4-c0).
For an odd prime `p` and `p ∤ a d - b c`,
`|∑ t : ZMod p, χ (a t + b) · χ (c t + d)| ≤ 1`. -/
theorem legendre_sum_two_forms_bound_one (hp : p ≠ 2) {a b c d : ZMod p}
    (h : a * d - b * c ≠ 0) :
    |∑ t : ZMod p, quadraticChar (ZMod p) (a * t + b) * quadraticChar (ZMod p) (c * t + d)|
      ≤ 1 :=
  quadraticChar_sum_two_forms_bound_one ((ZMod.ringChar_zmod_n p).substr hp) h

/-- **QCS-2 for the Legendre character (trivial bound).** Unconditionally, the two-form
Legendre sum is bounded in absolute value by `p`. -/
theorem legendre_sum_two_forms_trivial (a b c d : ZMod p) :
    |∑ t : ZMod p, quadraticChar (ZMod p) (a * t + b) * quadraticChar (ZMod p) (c * t + d)|
      ≤ (p : ℤ) := by
  have hcard := quadraticChar_sum_two_forms_trivial a b c d
  rwa [ZMod.card p] at hcard

end ZModSpecialization

/-!
## Residuals (QCS-3 and beyond)

The prime case above is the load-bearing content of Heath-Brown's omitted lemma. Two
extensions remain, recorded here as named residuals.

**QCS-3 — multiplicativity over coprime odd moduli (squarefree case).**  **LANDED** in
`Salt/HB/RealPrimitive.lean` (node WEIL-TRIO-W4-c), and at constant `1`, not `2 ^ ω(q)`:
`quadraticChar_sum_two_forms_bound_one` above supplies the per-prime input at the sharp
constant, so the coprime product telescopes into `gcd(q, u v' - v u')` alone.  The sketch
below is the original (pre-W4) reading of the step and is kept for orientation.  For coprime
odd `q₁, q₂` the sum at modulus `q₁ q₂` factors as a product of the sums at `q₁` and `q₂`. This is
*not* a direct corollary of the results here: for composite `q` the ring `ZMod q` is not a
field, so `quadraticChar (ZMod q)` is not the relevant object. The correct character is the
Jacobi symbol `jacobiSym · q` (a real Dirichlet character mod `q`), and the factorization
runs through the CRT ring isomorphism `ZMod.chineseRemainder` reindexing
`∑_{t : ZMod (q₁ q₂)}` into `∑_{(t₁, t₂)}`, together with the multiplicativity of
`jacobiSym` in its modulus. Landing it needs: (i) the CRT reindex of the sum into a product of
sums; (ii) `jacobiSym (n) (q₁ q₂) = jacobiSym n q₁ * jacobiSym n q₂`; (iii) the per-prime
input, which is exactly `legendre_sum_two_forms_bound` above (bound `2`) versus the trivial
bound `p` when `p ∣ a d - b c`, assembled into the `gcd` factor.

**Prime-power case.**  Split by the modulus, as the structure lemma
`q = 2^a · m` (`a ∈ {0, 2, 3}`, `m` odd squarefree) demands:

* the `2`-power components (`mod 4` and `mod 8`, for `χ₄`, `χ₈`, `χ₈'`) are **LANDED** in
  `Salt/HB/RealPrimitive.lean` (node WEIL-TRIO-W4-b) — with at most `8^4 = 4096` quadruples
  of coefficients these are *finite decision problems*, closed by `decide`, and they come out
  at the sharp gcd form `|∑| ≤ (2^a, u v' - v u')`;
* the odd prime-power components `mod p^k` with `k ≥ 2` remain OUT OF SCOPE (class C).  They
  do not occur on the Heath-Brown road at all: a real primitive character has odd conductor
  part squarefree, which is exactly why the structure lemma above is the right statement.
  There the analogue of QCS-1 is a Ramanujan/Kloosterman-type evaluation rather than a Jacobi
  sum, and the `≪ gcd(q, a d - b c)` bound requires a separate stationary-phase / completion
  argument.  Not attempted.
-/

end Salt.HB

end




theorem solution {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a b c d : ZMod p}
    (h : a * d - b * c ≠ 0) :
    |∑ t : ZMod p, quadraticChar (ZMod p) (a * t + b) * quadraticChar (ZMod p) (c * t + d)| ≤ 1 :=
  Salt.HB.legendre_sum_two_forms_bound_one hp h

