-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_bv_smoothfit_of_standing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:49:27.413974+00:00
-- url     : https://prove2.me/submissions/ab8d198d-5263-487b-90fb-57558286c16d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) :
    deriv (vcstar W) (cstar W).toReal = 1 := by
  have hac : X.ν ≪ MeasureTheory.volume := by
    rcases hX.2.2 with h | h | h
    · rw [hbv.1] at h; exact absurd h (lt_irrefl 0)
    · exact absurd h hbv.2.ne
    · exact h
  exact vcstar_deriv_one_of_bv_contDiff_one X hX q hq W hW hc hcpos hbv
    (scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy X hX q hq W hW hbv hac)
