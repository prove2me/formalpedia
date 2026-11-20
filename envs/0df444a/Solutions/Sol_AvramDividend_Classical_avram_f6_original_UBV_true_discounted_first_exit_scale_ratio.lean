-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_true_discounted_first_exit_scale_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T21:59:57.259709+00:00
-- url     : https://prove2.me/submissions/d8277905-ae92-4219-9353-7726a48cc9f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_min_killed_scale_harmonicity_one_to_barrier
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_killed_min_harmonicity_to_exit_ratio
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ b : ℝ, 1 ≤ b →
      twoSidedExitExpectation X q b 1 =
        ENNReal.ofReal (W 1 / W b) := by
  intro b hb
  have hpos : 0 < b := by linarith
  apply avram_root29_03_ubv_killed_min_harmonicity_to_exit_ratio
    X hBV q hq W hW b 1 hpos (by norm_num) hb
  exact avram_p4_f6_original_min_killed_scale_harmonicity_one_to_barrier
    X hX q hq W hW b hb
