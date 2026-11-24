-- Prove2me | solution 1 for FiniteEnergyPlane.isFiniteEnergyCurve_comp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T22:30:16.096445+00:00
-- url     : https://prove2.me/submissions/f7c06ad5-fa5b-49b8-91f4-dfab6191f49d

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_contDiffAt_aCoord_proj
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_isJHolomorphicOn_comp_of_differentiableAt
import Theorems.Thm_FiniteEnergyPlane_energy_comp_mul



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem isFiniteEnergyCurve_comp_mul_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (A : ℂ) (hA : A ≠ 0) :
    IsFiniteEnergyCurve H J Set.univ (fun z => u (A * z)) := by
  have hs : ContDiff ℝ ∞ u := contDiffOn_univ.1 hu.1
  have hm : ContDiff ℝ ∞ (fun z : ℂ => A * z) := contDiff_const.mul contDiff_id
  have ha : Differentiable ℝ (fun z => aCoord H (u z)) := fun z =>
    ((contDiffAt_aCoord_proj H hH (u z) (hu.2.1 z trivial)).1.comp z hs.contDiffAt).differentiableAt
      (by simp)
  have hp : Differentiable ℝ (fun z => proj H (u z)) := fun z =>
    ((contDiffAt_aCoord_proj H hH (u z) (hu.2.1 z trivial)).2.comp z hs.contDiffAt).differentiableAt
      (by simp)
  refine ⟨contDiffOn_univ.2 (hs.comp hm), fun z _ => hu.2.1 _ trivial, ?_, ?_⟩
  · exact isJHolomorphicOn_comp_of_differentiableAt (Jtilde H J) Set.univ Set.univ u hu.2.2.1
      (fun z hz => (jtilde_isAlmostComplexOn H hH J hJ).1.2.2 _ (hu.2.1 z hz)) (fun z => A * z)
      (fun z _ => ⟨by fun_prop, trivial⟩)
  · rw [energy_comp_mul H u A hA ha hp _ MeasurableSet.univ]
    refine lt_of_le_of_lt ?_ hu.2.2.2
    unfold energy
    exact iSup_mono fun φ => iSup_mono fun _ => lintegral_mono_set (Set.subset_univ _)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J Set.univ u) (A : ℂ) (hA : A ≠ 0) :
    IsFiniteEnergyCurve H J Set.univ (fun z => u (A * z)) :=
  isFiniteEnergyCurve_comp_mul_aux H hH J hJ u hu A hA
