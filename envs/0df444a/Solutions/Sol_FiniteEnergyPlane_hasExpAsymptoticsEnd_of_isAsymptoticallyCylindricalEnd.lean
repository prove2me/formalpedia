-- Prove2me | solution 1 for FiniteEnergyPlane.hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T20:22:18.64284+00:00
-- url     : https://prove2.me/submissions/936e790c-1053-4210-a0f0-da29e6cc9c5f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_expDecay_of_isAsymptoticallyCylindricalEnd
import Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_of_tendstoZeroCInfty



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hac : IsAsymptoticallyCylindricalEnd H u cylEnd P ε) :
    ∃ b > 0, HasExpAsymptoticsEnd H u cylEnd P ε b := by
  obtain ⟨d, c, ha, hw⟩ := hac
  obtain ⟨δ, hδ, C, s₀, hdec⟩ :=
    exists_expDecay_of_isAsymptoticallyCylindricalEnd H hH J hJ u hu P hP ε hε d c ha hw
  refine ⟨δ / 2, by positivity, d, c, ?_, ?_⟩
  · refine expDecayCInfty_of_tendstoZeroCInfty _ ha δ C s₀ (fun s hs t => ?_) (δ / 2) (by linarith)
    rw [Real.norm_eq_abs]
    exact (hdec s hs t).1
  · exact expDecayCInfty_of_tendstoZeroCInfty _ hw δ C s₀ (fun s hs t => (hdec s hs t).2)
      (δ / 2) (by linarith)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H) (hP : P.IsNondegenerate)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (hac : IsAsymptoticallyCylindricalEnd H u cylEnd P ε) :
    ∃ b > 0, HasExpAsymptoticsEnd H u cylEnd P ε b :=
  hasExpAsymptoticsEnd_of_isAsymptoticallyCylindricalEnd_aux H hH J hJ u hu P hP ε hε hac
