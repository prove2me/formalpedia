-- Prove2me | solution 2 for FiniteEnergyPlane.isRemovablePuncture_of_tendsto_loopAction_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-26T20:07:52.327919+00:00
-- url     : https://prove2.me/submissions/88bc3ac9-35a3-490d-bcf6-8d9378c991b5

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_isRemovablePuncture_of_abs_aCoord_le
import Theorems.Thm_FiniteEnergyPlane_exists_abs_aCoord_le_of_tendsto_loopAction_zero



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isRemovablePuncture_of_tendsto_loopAction_zero_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 0)) :
    IsRemovablePuncture H J u 0 1 :=
  isRemovablePuncture_of_abs_aCoord_le H hH J hJ u hu
    (exists_abs_aCoord_le_of_tendsto_loopAction_zero H hH J hJ u hu hG hQ)

end FiniteEnergyPlane

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
  isRemovablePuncture_of_tendsto_loopAction_zero_aux H hH J hJ u hu hG hQ
