-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.opt_delta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:14.210844+00:00
-- url     : https://prove2.me/submissions/117d8f60-6ce4-4009-92d9-1a5c5d81cf8c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (x A Bb : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ Bb)
    (h : ∀ δ : ℝ, 0 < δ → x ≤ (A / δ + δ * Bb) / 2) : x ≤ √A * √Bb := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 ≤ a ∧ A = a ^ 2 := ⟨√A, Real.sqrt_nonneg _, (Real.sq_sqrt hA).symm⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 ≤ b ∧ Bb = b ^ 2 := ⟨√Bb, Real.sqrt_nonneg _, (Real.sq_sqrt hB).symm⟩
  rw [Real.sqrt_sq ha, Real.sqrt_sq hb]
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h1 := h (a / b) (div_pos ha' hb')
      have hane : a ≠ 0 := ha'.ne'
      have hbne : b ≠ 0 := hb'.ne'
      have e : (a ^ 2 / (a / b) + a / b * b ^ 2) / 2 = a * b := by
        field_simp <;> ring
      linarith
    · subst hb'
      by_contra hx
      push_neg at hx
      have hx0 : 0 < x := by simpa using hx
      have hδ : 0 < 2 * a ^ 2 / x := div_pos (mul_pos two_pos (pow_pos ha' 2)) hx0
      have h1 := h _ hδ
      have hane : a ≠ 0 := ha'.ne'
      have hxne : x ≠ 0 := hx0.ne'
      have e : a ^ 2 / (2 * a ^ 2 / x) = x / 2 := by
        field_simp <;> ring
      have e3 : 2 * a ^ 2 / x * (0:ℝ) ^ 2 = 0 := by simp
      linarith
  · subst ha'
    by_contra hx
    push_neg at hx
    have hx0 : 0 < x := by simpa using hx
    have hne : b ^ 2 + 1 ≠ 0 := by positivity
    have hδ : 0 < x / (b ^ 2 + 1) := div_pos hx0 (by positivity)
    have h1 := h _ hδ
    have e : x / (b ^ 2 + 1) * (b ^ 2 + 1) = x := by field_simp
    have e2 : x / (b ^ 2 + 1) * b ^ 2 ≤ x / (b ^ 2 + 1) * (b ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    have e3 : (0:ℝ) ^ 2 / (x / (b ^ 2 + 1)) = 0 := by simp
    linarith
end Formalism.FourierDecayAlt.P.LEx1
