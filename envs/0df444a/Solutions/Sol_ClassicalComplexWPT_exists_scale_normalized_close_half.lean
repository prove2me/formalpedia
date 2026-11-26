-- Prove2me | solution 1 for ClassicalComplexWPT.exists_scale_normalized_close_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:05.793444+00:00
-- url     : https://prove2.me/submissions/e5e273d3-f0fa-4fd2-bfc6-fd9d76b931ca

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_norm_normalizedScale_sub_monomial_le
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply



set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (f : OriginSeq) (d : ℕ)
    (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ∃ (t : ℝ≥0) (ht : t ≤ 1), 0 < t ∧ t < 1 ∧
      ‖normalizedScale t ht f d - monomialSeq d‖ < (1 : ℝ) / 2 := by
  let a : ℝ := ‖f d‖
  let b : ℝ := ‖f‖
  have ha : 0 < a := by exact norm_pos_iff.mpr hfd
  have hb : 0 ≤ b := norm_nonneg _
  have hden : 0 < 4 * (b + a) := by positivity
  let tr : ℝ := a / (4 * (b + a))
  have htr0 : 0 < tr := div_pos ha hden
  have htr1 : tr < 1 := by
    rw [div_lt_one hden]
    nlinarith
  let t : ℝ≥0 := ⟨tr, htr0.le⟩
  have ht0 : 0 < t := by exact_mod_cast htr0
  have ht1 : t < 1 := by exact_mod_cast htr1
  refine ⟨t, ht1.le, ht0, ht1, ?_⟩
  calc
    ‖normalizedScale t ht1.le f d - monomialSeq d‖ ≤
        ((t : ℝ) / ‖f d‖) * ‖f‖ :=
      norm_normalizedScale_sub_monomial_le ht1.le ht0 f d hlow hfd
    _ = b / (4 * (b + a)) := by
      change (tr / a) * b = b / (4 * (b + a))
      dsimp only [tr]
      field_simp
    _ < (1 : ℝ) / 2 := by
      rw [div_lt_iff₀ hden]
      nlinarith
end ClassicalComplexWPT
