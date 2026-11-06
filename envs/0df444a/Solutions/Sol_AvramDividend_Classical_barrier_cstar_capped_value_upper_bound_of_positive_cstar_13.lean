-- Prove2me | solution 13 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:20:08.053582+00:00
-- url     : https://prove2.me/submissions/2cde9c72-d690-4b17-ac99-bc9be26c624c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
import Theorems.Thm_AvramDividend_Classical_vcstar_smooth_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_cstar
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_capped_value_all_capital_without_smoothness
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Positive finite barrier: interior local verification and the all-capital bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  obtain ⟨hcont, hzero, hneg, _, _⟩ :=
    vcstar_unrestricted_verification_regularity
      X hX q hq W hW hc h_smooth
  have hsmooth :=
    vcstar_smooth_below_positive_cstar X hX q hq W hW hc hcpos h_smooth
  have hhjb :=
    vcstar_hjb_below_cstar X hX q hq W hW hc hcpos h_smooth
  have hinside :=
    (local_verification X hX q hq (vcstar W) (cstar W)
      hcpos hcont hzero hneg hsmooth hhjb).1
  exact avram_sweep17_cstar_capped_value_all_capital_without_smoothness
    X hX q hq W hW hc hinside
