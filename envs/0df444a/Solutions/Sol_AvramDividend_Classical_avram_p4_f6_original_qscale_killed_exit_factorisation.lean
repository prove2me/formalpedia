-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_original_qscale_killed_exit_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:36:15.000135+00:00
-- url     : https://prove2.me/submissions/61903763-f8e3-4fb4-9803-a511ce505325

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_stopped_scale_balance_one_to_barrier
import Theorems.Thm_AvramDividend_Classical_chat04_exit_ratio_of_stopped_balance
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWone : 0 < W 1) :
    ∀ b : ℝ, 1 ≤ b →
      W 1 = (twoSidedExitExpectationCorrected X q b 1).toReal * W b := by
  intro b hb
  have hbpos : 0 < b := by linarith
  have hBalance :=
    avram_p4_f6_original_stopped_scale_balance_one_to_barrier
      X hX q hq W hW b hb
  have hratio :=
    chat04_exit_ratio_of_stopped_balance
      X hX q hq W hW b 1 hbpos (by norm_num) hb hBalance
  have hcorrected :
      twoSidedExitExpectationCorrected X q b 1 =
        ENNReal.ofReal (W 1 / W b) := by
    rw [← chat04_twoSidedExitExpectation_eq_corrected X q b 1]
    exact hratio
  have hWb : 0 < W b :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW b hbpos
  rw [hcorrected]
  rw [ENNReal.toReal_ofReal (div_nonneg (le_of_lt hWone) (le_of_lt hWb))]
  field_simp
