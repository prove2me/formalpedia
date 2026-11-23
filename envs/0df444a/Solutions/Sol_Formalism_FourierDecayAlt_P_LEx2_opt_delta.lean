-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.opt_delta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:19.525636+00:00
-- url     : https://prove2.me/submissions/245042c6-5136-4750-8fc0-051746561f0b

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (x A Bb : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ Bb)
    (h : ∀ δ : ℝ, 0 < δ → x ≤ (A / δ + δ * Bb) / 2) : x ≤ √A * √Bb := by
  rcases hA.eq_or_lt with hA0 | hA0
  · subst hA0
    simp only [Real.sqrt_zero, zero_mul]
    by_contra hx
    have hx' : 0 < x := not_le.1 hx
    rcases hB.eq_or_lt with hB0 | hB0
    · have := h 1 one_pos
      rw [← hB0] at this; simp at this; linarith
    · have := h (x / Bb) (by positivity)
      have e : x / Bb * Bb = x := by field_simp
      rw [e] at this; simp at this; linarith
  · rcases hB.eq_or_lt with hB0 | hB0
    · subst hB0
      simp only [Real.sqrt_zero, mul_zero]
      by_contra hx
      have hx' : 0 < x := not_le.1 hx
      have := h (A / x) (by positivity)
      have e : A / (A / x) = x := by field_simp
      rw [e] at this; simp at this; linarith
    · have hsA := Real.sqrt_pos.2 hA0
      have hsB := Real.sqrt_pos.2 hB0
      have := h (√A / √Bb) (by positivity)
      have a2 : √A * √A = A := Real.mul_self_sqrt hA
      have b2 : √Bb * √Bb = Bb := Real.mul_self_sqrt hB
      have e1 : A / (√A / √Bb) = √A * √Bb := by
        rw [div_div_eq_mul_div, div_eq_iff hsA.ne']; nlinarith
      have e2 : √A / √Bb * Bb = √A * √Bb := by
        rw [div_mul_eq_mul_div, div_eq_iff hsB.ne']; nlinarith
      rw [e1, e2] at this; linarith
end Formalism.FourierDecayAlt.P.LEx2
