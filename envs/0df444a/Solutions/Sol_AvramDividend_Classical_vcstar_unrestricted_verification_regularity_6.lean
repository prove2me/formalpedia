-- Prove2me | solution 6 for AvramDividend.Classical.vcstar_unrestricted_verification_regularity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T05:56:43.38829+00:00
-- url     : https://prove2.me/submissions/85aa1f4a-a041-4e63-933d-2b2a02821b2b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_zero_basic_verification_boundary
import Theorems.Thm_AvramDividend_Classical_vcstar_smooth_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C1_bv_positive_barrier
import Theorems.Thm_AvramDividend_Classical_gaussian_vcstar_global_C2_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_identity_corrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

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
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ cstar W) with hc0 | hcpos
  · have hc0eq : (0 : ℝ≥0∞) = cstar W := hc0
    have hBound :=
      vcstar_zero_basic_verification_boundary X hX q hq W hW hc0eq.symm
    have hC2 := vcstar_smooth_of_zero_cstar W hc0eq.symm
    exact ⟨hBound.1, hBound.2.1, hBound.2.2,
      ⟨fun _ => hC2, fun _ => hC2.of_le (by norm_num)⟩⟩
  · have hcposlt : (0 : ℝ≥0∞) < cstar W := hcpos
    have hBound :=
      vcstar_basic_boundary_regular_of_positive_cstar X hX q hq W hW hc hcposlt
    have hBVimp : X.BoundedVariation → ContDiffOn ℝ 1 (vcstar W) (Ioi 0) := by
      intro hbv
      exact vcstar_global_C1_bv_positive_barrier X hX q hq W hW hc hcposlt hbv
    have hNBVimp : ¬ X.BoundedVariation → ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by
      intro hnbv
      rcases h_smooth with hσ | hBV | hC2hyp
      · have hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
            twoSidedExitExpectationCorrected X q a x =
              ENNReal.ofReal (W x / W a) := by
          intro a x ha hx hxa
          exact two_sided_exit_before_ruin_identity_corrected
            X hX q hq W hW a x ha (le_of_lt hx) hxa
        exact gaussian_vcstar_global_C2_of_corrected_exit_identity
          X hX q hq W hW hc hcposlt hσ hExit
      · exact absurd hBV hnbv
      · exact hC2hyp
    exact ⟨hBound.1, hBound.2.1, hBound.2.2, ⟨hNBVimp, hBVimp⟩⟩
