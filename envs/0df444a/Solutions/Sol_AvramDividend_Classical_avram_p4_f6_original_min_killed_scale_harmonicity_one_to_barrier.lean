-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_original_min_killed_scale_harmonicity_one_to_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:02:40.314688+00:00
-- url     : https://prove2.me/submissions/7a538d08-1b7c-4011-b948-53bb846547d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_terminal_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_payoff_to_named_balance
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_payoff_balance
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_expectation_scale_identity

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
      (∫⁻ ω, if min (twoSidedExitUpTime X (b - 1) ω) (twoSidedExitDownTime X (-1) ω) < ⊤ then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (b - 1) ω) (twoSidedExitDownTime X (-1) ω))))) *
          ENNReal.ofReal
            (W (1 + X.X (min (twoSidedExitUpTime X (b - 1) ω) (twoSidedExitDownTime X (-1) ω)).toNNReal ω))
        else 0 ∂P) = ENNReal.ofReal (W 1) := by
  intro b hb
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hb
  have h10 : (0 : ℝ) ≤ 1 := by norm_num
  have hratio :
      twoSidedExitExpectation X q b 1 * ENNReal.ofReal (W b) =
        ENNReal.ofReal (W 1) := by
    by_cases hBV : X.BoundedVariation
    · have hpayoff :=
        bv_stopped_scale_ost_payoff_balance X hX q hq W hW hBV b 1 hb0 h10 hb
      exact avram_root29_03_bv_payoff_to_named_balance
        X hX q hq W hW hBV b 1 hb0 h10 hb hpayoff
    · exact chat04_unbounded_two_sided_exit_expectation_scale_identity
        X q hq W hW hBV b 1 hb0 h10 hb
  exact (avram_root29_03_standing_stopped_min_terminal_factorisation
    X hX q hq W hW b 1 hb0 h10 hb).trans hratio
