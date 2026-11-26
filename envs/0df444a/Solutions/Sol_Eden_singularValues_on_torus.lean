-- Prove2me | solution 1 for Eden.singularValues_on_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:57.054311+00:00
-- url     : https://prove2.me/submissions/b5071beb-d4e1-47b6-b223-80329591034f

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_SingularValues
import Mathlib.Data.List.Sort
import Mathlib.Order.Fin.Basic
import Definitions.Def_Eden_OrderedStationarySpectrum
import Theorems.Thm_Eden_antitone_eq_of_multiset_eq
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_derivativeFactors_on_torus
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
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus) :
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      ![Real.exp (2 * t), Real.exp (2 * t), 1, 1, Real.exp (-c * t)] := by
  let A := (fderiv ℝ (evolution c t) p).toLinearMap
  have hhigh : 1 ≤ Real.exp (2 * t) := Real.one_le_exp_iff.mpr (by positivity)
  have hlow : Real.exp (-c * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  apply antitone_eq_of_multiset_eq
  · exact fun i j hij => A.singularValues_antitone hij
  · rw [Fin.antitone_iff_succ_le]
    intro i
    fin_cases i <;> simp_all
  · rw [singularValues_fderiv_evolution c ht p, derivativeFactors_on_torus c ht hp]
    simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Multiset.coe_eq_coe.mpr
    exact (List.Perm.swap _ _ _).cons _
end Eden
