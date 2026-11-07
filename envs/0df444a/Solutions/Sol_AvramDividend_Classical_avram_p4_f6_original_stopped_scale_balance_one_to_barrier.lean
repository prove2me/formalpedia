-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_original_stopped_scale_balance_one_to_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:38:36.050103+00:00
-- url     : https://prove2.me/submissions/07cbb0ba-da8c-41cd-bdb5-c14ebb76f5dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_min_killed_scale_harmonicity_one_to_barrier
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_stopped_min_terminal_exit_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
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
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ b : ℝ, 1 ≤ b →
      twoSidedExitExpectation X q b 1 * ENNReal.ofReal (W b) =
        ENNReal.ofReal (W 1) := by
  intro b hb
  have hbpos : 0 < b := by linarith
  have hterminal :=
    avram_p4_f6_original_min_killed_scale_harmonicity_one_to_barrier
      X hX q hq W hW b hb
  by_cases hBV : X.BoundedVariation
  · have hfactor :=
      avram_root29_03_bv_stopped_min_terminal_exit_factorisation
        X hX q hq W hW hBV b 1 hbpos (by norm_num) hb
    exact hfactor.symm.trans hterminal
  · have hfactor :=
      avram_root29_03_ubv_stopped_min_terminal_exit_factorisation
        X hBV q hq W hW b 1 hbpos hb
    exact hfactor.symm.trans hterminal
