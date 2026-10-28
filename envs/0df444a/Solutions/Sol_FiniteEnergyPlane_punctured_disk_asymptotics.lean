-- Prove2me | solution 1 for FiniteEnergyPlane.punctured_disk_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-26T15:02:38.633216+00:00
-- url     : https://prove2.me/submissions/50b9e473-53ad-4210-9959-e7376e222660

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_tendsto_loopAction_cwLoop
import Theorems.Thm_FiniteEnergyPlane_exists_norm_mul_gradNorm_le_near_puncture
import Theorems.Thm_FiniteEnergyPlane_isRemovablePuncture_of_tendsto_loopAction_zero
import Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInfty_cwLoop
import Theorems.Thm_FiniteEnergyPlane_tendsto_aCoord_of_tendsto_loopAction



open FiniteEnergyPlane MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    IsRemovablePuncture H J u 0 1 ∨
      ∃ Q : ℝ, Q ≠ 0 ∧ Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q) ∧
        (0 < Q → Tendsto (fun z => aCoord H (u z)) (𝓝[≠] 0) atTop) ∧
        (Q < 0 → Tendsto (fun z => aCoord H (u z)) (𝓝[≠] 0) atBot) ∧
        ∀ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) → Tendsto ρ atTop (𝓝 0) →
          ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ReebOrbit H, P.T = |Q| ∧ ∃ c : ℝ,
            TendstoCInfty (fun k => loopInS H u (cwLoop 0 (ρ (φ k))))
              (fun t => P.x (Q * t + c)) := by
  obtain ⟨Q, hQ⟩ := exists_tendsto_loopAction_cwLoop H hH J hJ u hu
  have hG := exists_norm_mul_gradNorm_le_near_puncture H hH J hJ u hu
  by_cases h0 : Q = 0
  · subst h0
    exact Or.inl (isRemovablePuncture_of_tendsto_loopAction_zero H hH J hJ u hu hG hQ)
  · have ha := tendsto_aCoord_of_tendsto_loopAction H hH J hJ u hu hG Q hQ
    exact Or.inr ⟨Q, h0, hQ, ha.1, ha.2, fun ρ hρ hρ0 =>
      exists_subseq_tendstoCInfty_cwLoop H hH J hJ u hu hG Q h0 hQ ρ hρ hρ0⟩


