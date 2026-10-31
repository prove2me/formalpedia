-- Prove2me | solution 1 for FiniteEnergyPlane.isAsymptoticallyCylindricalEnd_of_isNondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T20:44:36.950483+00:00
-- url     : https://prove2.me/submissions/802968cd-fa35-47e5-81e0-f5353fcb8f55

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_isIsolated_of_isNondegenerate
import Theorems.Thm_FiniteEnergyPlane_tendstoCInfty_of_isIsolated
import Theorems.Thm_FiniteEnergyPlane_not_isRemovablePuncture_of_tendstoCInfty_loop
import Theorems.Thm_FiniteEnergyPlane_cylEnd_tendsto_of_loops_tendsto_mod_phase
import Theorems.Thm_FiniteEnergyPlane_exists_tendsto_cylEnd_of_isNondegenerate
import Theorems.Thm_FiniteEnergyPlane_tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isAsymptoticallyCylindricalEnd_of_isNondegenerate_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (c : ℝ) (hconv : TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ k)))
      (fun t => P.x (σ * P.T * t + c))) :
    IsAsymptoticallyCylindricalEnd H u cylEnd P σ := by
  have hnr := not_isRemovablePuncture_of_tendstoCInfty_loop H hH J u P σ hσ ρ hρ hρ0 c hconv
  have hiso := isIsolated_of_isNondegenerate H hH P hP
  have hloop := tendstoCInfty_of_isIsolated H hH J hJ u hu hnr P hiso σ hσ ρ hρ hρ0 c hconv
  obtain ⟨hsm, hA, hW⟩ := cylEnd_tendsto_of_loops_tendsto_mod_phase H hH J hJ u hu P σ hσ hloop
  obtain ⟨d, c₀, hA0, hW0⟩ :=
    exists_tendsto_cylEnd_of_isNondegenerate H hH J hJ u hu P hP σ hσ hA hW
  exact ⟨d, c₀, tendstoZeroCInfty_of_tendstoZeroUnif_mod_phase H hH P σ hσ _ _ hsm hA hW d c₀
    hA0 hW0⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k) (hρ0 : Tendsto ρ atTop (𝓝 0))
    (c : ℝ) (hconv : TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ k)))
      (fun t => P.x (σ * P.T * t + c))) :
    IsAsymptoticallyCylindricalEnd H u cylEnd P σ :=
  isAsymptoticallyCylindricalEnd_of_isNondegenerate_aux H hH J hJ u hu P hP σ hσ ρ hρ hρ0 c hconv
