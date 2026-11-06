-- Prove2me | solution 12 for AvramDividend.Classical.barrier_cstar_capped_value_upper_bound_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:53:11.21064+00:00
-- url     : https://prove2.me/submissions/a996c2cf-51df-45cc-91f1-a4117d3d05af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  obtain ⟨hcont, hw0, hwneg, hsmooth⟩ :=
    vcstar_local_verification_regular_of_positive_cstar
      X hX q hq W hW hc hcpos h_smooth
  have hHJB := vcstar_hjb_below_positive_cstar
    X hX q hq W hW hc h_smooth hcpos
  have hVerify := local_verification X hX q hq (vcstar W) (cstar W)
    hcpos hcont hw0 hwneg hsmooth hHJB
  exact avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
    X hX q hq W hW hc h_smooth hVerify.1
