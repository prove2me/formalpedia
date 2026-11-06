-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_capped_upper_bound_all_capital
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:07:48.927378+00:00
-- url     : https://prove2.me/submissions/90ac2c44-7311-494c-a557-be07d43ec762
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_capped_value_upper_bound_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_zero_cap_boundary_value_package
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound_of_zero_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
  by_cases hcpos : 0 < cstar W
  · exact barrier_cstar_capped_value_upper_bound_of_positive_cstar
      X hX q hq W hW hc hcpos h_smooth
  · have hzero : cstar W = 0 :=
      le_antisymm (le_of_not_gt hcpos) bot_le
    obtain ⟨hval, hzeroValue⟩ := zero_cap_boundary_value_package
      X hX q hq W hW
    intro x hx
    have hBound := zero_cap_value_upper_bound_of_zero_bound
      X q W hzeroValue hval x hx
    simpa [vcstar, hzero] using hBound
