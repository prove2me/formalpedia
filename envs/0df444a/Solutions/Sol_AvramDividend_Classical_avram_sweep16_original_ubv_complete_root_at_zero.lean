-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ubv_complete_root_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:16:47.952074+00:00
-- url     : https://prove2.me/submissions/84b43def-d62a-47ab-b472-c85bcc26466c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_zero_reserve_full_root_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Both original optimality conjunctions at x=0 under unbounded variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    IsAdmissibleLe X 0 (cstar W) (barrierStrategy X 0 (cstar W).toReal) ∧
    dividendValue X q 0 (barrierStrategy X 0 (cstar W).toReal) =
      ENNReal.ofReal (vcstar W 0) ∧
    valueFunctionLe X q (cstar W) 0 = ENNReal.ofReal (vcstar W 0) ∧
    IsAdmissible X 0 (barrierStrategy X 0 (cstar W).toReal) ∧
    valueFunction X q 0 = ENNReal.ofReal (vcstar W 0) := by
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  obtain ⟨hAdmissible, hDividend⟩ :=
    barrier_cstar_attains_value_all_capital
      X hX q hq W hW hc 0 (le_refl 0)
  have hValues :=
    avram_sweep16_original_ubv_zero_reserve_full_root_value X hBV q hq W hW
  exact ⟨hAdmissible, hDividend, hValues.1 (cstar W),
    hAdmissible.1, hValues.2⟩
