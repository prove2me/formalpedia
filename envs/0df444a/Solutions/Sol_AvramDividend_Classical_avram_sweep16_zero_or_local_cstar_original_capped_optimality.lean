-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_zero_or_local_cstar_original_capped_optimality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:59:27.369303+00:00
-- url     : https://prove2.me/submissions/6627dfb0-c2d2-41e6-b6d7-c1965015c940

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_cstar_original_capped_optimality
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality

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
    (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hEither :
      cstar W = 0 ∨
        (∀ x : ℝ, 0 ≤ x → x ≤ (cstar W).toReal →
          valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x))) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) := by
  intro x hx
  rcases hEither with hzero | hInterior
  · exact avram_sweep16_zero_cstar_original_capped_optimality
      X hX q hq W hW hzero x hx
  · exact avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality
      X hX q hq W hW hc h_smooth hInterior x hx
