-- Prove2me | solution 4 for AvramDividend.Classical.vcstar_unrestricted_verification_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:13:47.174803+00:00
-- url     : https://prove2.me/submissions/e5e92c5c-7806-4fbd-ac8b-ed34a6507d6f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_vcstar_zero_basic_verification_boundary
import Theorems.Thm_AvramDividend_Classical_vcstar_smooth_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C1_bv_positive_barrier
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected
import Theorems.Thm_AvramDividend_Classical_gaussian_vcstar_global_C2_of_corrected_exit_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Global regularity, conditional on the canonical corrected two-sided-exit identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      (∀ y < 0, vcstar W y = 0) ∧
      ((¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) ∧
       (X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W) (Ioi 0))) := by
  by_cases hzero : cstar W = 0
  · obtain ⟨hcont, hnonneg, hneg⟩ :=
      vcstar_zero_basic_verification_boundary X hX q hq W hW hzero
    have hc2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0) :=
      vcstar_smooth_of_zero_cstar W hzero
    refine ⟨hcont, hnonneg, hneg, ?_, ?_⟩
    · intro _
      exact hc2
    · intro _
      exact hc2.of_le (by norm_num)
  · have hpos : 0 < cstar W := pos_iff_ne_zero.mpr hzero
    obtain ⟨hcont, hnonneg, hneg⟩ :=
      vcstar_basic_boundary_regular_of_positive_cstar
        X hX q hq W hW hc hpos
    refine ⟨hcont, hnonneg, hneg, ?_, ?_⟩
    · intro hnotBV
      rcases h_smooth with hσ | hbv | hC2
      · have hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
            twoSidedExitExpectationCorrected X q a x =
              ENNReal.ofReal (W x / W a) := by
          intro a x ha hx hxa
          exact two_sided_exit_before_ruin_identity_corrected
            X hX q hq W hW a x ha (le_of_lt hx) hxa
        exact gaussian_vcstar_global_C2_of_corrected_exit_identity
          X hX q hq W hW hc hpos hσ hExit
      · exact False.elim (hnotBV hbv)
      · exact hC2
    · intro hbv
      exact vcstar_global_C1_bv_positive_barrier
        X hX q hq W hW hc hpos hbv
