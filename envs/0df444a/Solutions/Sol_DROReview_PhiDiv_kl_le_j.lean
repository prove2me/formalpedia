-- Prove2me | solution 1 for DROReview.PhiDiv.kl_le_j
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:13:49.715632+00:00
-- url     : https://prove2.me/submissions/3ac95608-eabc-4ff9-9240-78e6d211453f

import Mathlib
import Definitions.Def_DROReview_PhiDiv_phiDiv
import Definitions.Def_DROReview_PhiDiv_generators

set_option autoImplicit false

open MeasureTheory Filter DROReview.PhiDiv

lemma drp_mono {Ξ : Type*} [MeasurableSpace Ξ] (φ₁ φ₂ : NNReal → ENNReal)
    (h : ∀ t, φ₁ t ≤ φ₂ t) (P Q : ProbabilityMeasure Ξ) :
    phiDiv φ₁ P Q ≤ phiDiv φ₂ P Q := by
  unfold phiDiv
  refine lintegral_mono (fun x => ?_)
  dsimp only
  split_ifs with hq
  · refine mul_le_mul_right ?_ _
    unfold phiSlope
    exact limsup_le_limsup (Eventually.of_forall (fun t => ENNReal.div_le_div_right (h t) _))
  · exact mul_le_mul_right (h _) _

theorem solution {Ξ : Type*} [MeasurableSpace Ξ]
    (P P₀ : ProbabilityMeasure Ξ) :
    phiDiv phiKL P P₀ ≤
      phiDiv phiJ P P₀ := by
  refine drp_mono _ _ (fun t => ?_) P P₀
  unfold phiKL phiJ
  by_cases h0 : t = 0
  · simp [h0]
  · rw [if_neg h0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : (0 : ℝ) < t := by exact_mod_cast pos_iff_ne_zero.2 h0
    have h1 := Real.log_le_sub_one_of_pos hpos
    nlinarith
