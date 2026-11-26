-- Prove2me | solution 1 for ClassicalComplexWPT.exists_radius_normalizedOrigin_close_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:24.751851+00:00
-- url     : https://prove2.me/submissions/81910e80-707c-49b3-987a-7baaef752b89

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_exists_scale_normalized_close_half
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_low_eq_zero
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_top_ne_zero
import Theorems.Thm_ClassicalComplexWPT_scaleSeq_originWeightedCoeffs
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {f : Ambient n → ℂ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (hp : HasFPowerSeriesAt f p 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (r : ℝ≥0) (hr : (r : ℝ≥0∞) < p.radius),
      0 < r ∧ originWeightedCoeffs p r hr d ≠ 0 ∧
        ‖normalizedOriginCoeffs p r hr d - monomialSeq d‖ < (1 : ℝ) / 2 := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hp.radius_pos with ⟨R, hR0E, hR⟩
  have hR0 : 0 < R := by exact_mod_cast hR0E
  let B : OriginSeq := originWeightedCoeffs p R hR
  have hBlow : ∀ j < d, B j = 0 := by
    intro j hj
    exact originWeightedCoeffs_low_eq_zero p hp horder R hR hj
  have hBd : B d ≠ 0 := originWeightedCoeffs_top_ne_zero p hp horder R hR0 hR
  obtain ⟨t, ht, ht0, ht1, hclose⟩ :=
    exists_scale_normalized_close_half B d hBlow hBd
  let r : ℝ≥0 := t * R
  have hr : (r : ℝ≥0∞) < p.radius := mul_radius_lt_of_le_one p R t hR ht
  have hr0 : 0 < r := mul_pos ht0 hR0
  have hscale : scaleSeq t ht B = originWeightedCoeffs p r hr := by
    dsimp only [B, r, hr]
    exact scaleSeq_originWeightedCoeffs p R t hR ht
  have hnorm : normalizedScale t ht B d = normalizedOriginCoeffs p r hr d := by
    unfold normalizedScale normalizedOriginCoeffs
    rw [hscale]
  refine ⟨r, hr, hr0,
    originWeightedCoeffs_top_ne_zero p hp horder r hr0 hr, ?_⟩
  rw [← hnorm]
  exact hclose
end ClassicalComplexWPT
