-- Prove2me | solution 1 for Eden.singularValues_fderiv_evolution_fifth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:11.523046+00:00
-- url     : https://prove2.me/submissions/8fca9b6e-3916-497f-adee-4a9efd900017

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_SingularValues
import Definitions.Def_Eden_FactorBounds
import Theorems.Thm_Eden_derivativeFactors_ge_fifth
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValues_fderiv_evolution
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) :
    (fderiv ℝ (evolution c t) p).toLinearMap.singularValues 4 = Real.exp (-c * t) := by
  let A := (fderiv ℝ (evolution c t) p).toLinearMap
  have hm := singularValues_fderiv_evolution c ht p
  have hf : Real.exp (-c * t) ∈
      Finset.univ.val.map (fun i : Fin 5 => derivativeFactors c t p i) := by
    exact Multiset.mem_map.mpr ⟨4, by simp, rfl⟩
  rw [← hm] at hf
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hf
  have hle : A.singularValues 4 ≤ Real.exp (-c * t) := by
    rw [← hi]
    exact A.singularValues_antitone (by omega)
  have hs : A.singularValues 4 ∈
      Finset.univ.val.map (fun i : Fin 5 => A.singularValues i) :=
    Multiset.mem_map.mpr ⟨4, by simp, rfl⟩
  change A.singularValues 4 ∈ _ at hs
  rw [hm] at hs
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hs
  exact le_antisymm hle (hj ▸ derivativeFactors_ge_fifth hc ht hp j)
end Eden
