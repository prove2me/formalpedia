-- Prove2me | solution 1 for DROReview.PhiDiv.hellinger_le_kl
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:15:40.363581+00:00
-- url     : https://prove2.me/submissions/2fd1c2ac-4354-4d00-99d4-f9b41b9e7d8c

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
    phiDiv phiH P P₀ ≤
      phiDiv phiKL P P₀ := by
  refine drp_mono _ _ (fun t => ?_) P P₀
  unfold phiH phiKL
  refine ENNReal.ofReal_le_ofReal ?_
  set s : ℝ := Real.sqrt (t : ℝ) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hts : (t : ℝ) = s ^ 2 := (Real.sq_sqrt t.2).symm
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0] at hts ⊢
    rw [hts]; simp
  · have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at h1
    have h2 : s - 1 ≤ s * Real.log s := by
      have := mul_le_mul_of_nonneg_left h1 hs0
      field_simp at this
      linarith
    rw [hts, Real.log_pow]
    push_cast
    nlinarith [mul_nonneg hs0 (sub_nonneg.2 h2)]
