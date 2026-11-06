-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_interior_cstar_capped_upper_yields_global_capped_optimality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:56:25.824658+00:00
-- url     : https://prove2.me/submissions/e94eb6b0-48de-486f-b2ab-67c607b5b3b6

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
    (hInterior :
      ∀ x : ℝ, 0 ≤ x → x ≤ (cstar W).toReal →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x) := by
  have hc0 : 0 ≤ (cstar W).toReal := by positivity
  have hBoundary :
      valueFunctionLe X q (cstar W) (cstar W).toReal ≤
        ENNReal.ofReal (vcstar W (cstar W).toReal) :=
    hInterior _ hc0 (le_refl _)
  have hbarrierNonneg : 0 ≤ vcstar W (cstar W).toReal :=
    avram_sweep17_vcstar_nonnegative_all_capital
      X hX q hq W hW hc h_smooth (cstar W).toReal hc0
  have hAbove :=
    avram_sweep17_cstar_boundary_to_above_cap
      X q W hc hbarrierNonneg hBoundary
  intro x hx
  have hUpper :
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x) := by
    rcases le_total x (cstar W).toReal with hle | hge
    · exact hInterior x hx hle
    · exact hAbove x hge
  have hLower :=
    (avram_sweep16_barrier_cstar_lower_bounds_from_attainment
      X hX q hq W hW hc x hx).1
  exact le_antisymm hUpper hLower
