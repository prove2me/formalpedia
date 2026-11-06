-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_cstar_capped_optimality_above_barrier_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:55:45.400846+00:00
-- url     : https://prove2.me/submissions/67edb36e-b702-4ff9-9d89-c77f114a7f50

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_nonnegative_all_capital
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_cstar_boundary_to_above_cap
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_barrier_cstar_lower_bounds_from_attainment

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth :
      0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hBoundary :
      valueFunctionLe X q (cstar W) (cstar W).toReal ≤
        ENNReal.ofReal (vcstar W (cstar W).toReal)) :
    ∀ x : ℝ, (cstar W).toReal ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) := by
  have hbarrierNonneg : 0 ≤ vcstar W (cstar W).toReal :=
    avram_sweep17_vcstar_nonnegative_all_capital
      X hX q hq W hW hc h_smooth (cstar W).toReal (by positivity)
  intro x hx
  have hx0 : 0 ≤ x :=
    le_trans (show 0 ≤ (cstar W).toReal by positivity) hx
  have hUpper :=
    avram_sweep17_cstar_boundary_to_above_cap
      X q W hc hbarrierNonneg hBoundary x hx
  have hLower :=
    (avram_sweep16_barrier_cstar_lower_bounds_from_attainment
      X hX q hq W hW hc x hx0).1
  exact le_antisymm hUpper hLower
