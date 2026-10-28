-- Prove2me | solution 1 for FiniteEnergyPlane.isRemovablePuncture_of_tendsto_loopAction_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T17:49:54.815526+00:00
-- url     : https://prove2.me/submissions/30a8c785-e541-4a4c-a965-51ebff32d9a9

import Theorems.Thm_FiniteEnergyPlane_exists_abs_aCoord_le_of_tendsto_loopAction_zero
import Theorems.Thm_FiniteEnergyPlane_isRemovablePuncture_of_abs_aCoord_le

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 0)) :
    IsRemovablePuncture H J u 0 1 :=
  isRemovablePuncture_of_abs_aCoord_le H hH J hJ u hu
    (exists_abs_aCoord_le_of_tendsto_loopAction_zero H hH J hJ u hu hG hQ)
