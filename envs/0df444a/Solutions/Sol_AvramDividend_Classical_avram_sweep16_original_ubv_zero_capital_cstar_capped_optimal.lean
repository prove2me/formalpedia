-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ubv_zero_capital_cstar_capped_optimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:50:24.126211+00:00
-- url     : https://prove2.me/submissions/71331283-ef3c-447d-ba26-9a44f286b806

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_enlarged_cap_barrier_lower
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_cstar_original_capped_optimality

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- An unconditional exact original UBV capped value at initial reserve zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : ¬ X.BoundedVariation)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    valueFunctionLe X q (cstar W) 0 = ENNReal.ofReal (vcstar W 0) := by
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  by_cases hc0 : cstar W = 0
  · exact avram_sweep16_zero_cstar_original_capped_optimality
      X hX q hq W hW hc0 0 (le_refl 0)
  · have hcpos : (0 : ℝ≥0∞) < cstar W := by
      exact lt_of_le_of_ne bot_le (Ne.symm hc0)
    obtain ⟨hcont, hzero, _hneg, hsmooth⟩ :=
      vcstar_local_verification_regular_of_positive_cstar
        X hX q hq W hW hc hcpos h_smooth
    have hhjb := vcstar_hjb_below_cstar X hX q hq W hW hc hcpos h_smooth
    have hUpper :
        valueFunctionLe X q (cstar W) 0 ≤ ENNReal.ofReal (vcstar W 0) :=
      avram_wave6_10_ubv_original_zero_start_capped_valueFunctionLe_upper
        X hBV q (vcstar W) (cstar W) hzero hcont (hsmooth.1 hBV) hhjb
    have hLower :
        ENNReal.ofReal (vcstar W 0) ≤ valueFunctionLe X q (cstar W) 0 :=
      avram_sweep16_original_enlarged_cap_barrier_lower
        X hX q hq W hW (cstar W) le_rfl 0 (le_refl 0)
    exact le_antisymm hUpper hLower
