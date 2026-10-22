-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.positive_tangential_hessian_of_radial_and_det
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:58:09.718986+00:00
-- url     : https://prove2.me/submissions/38a917b8-fe6e-4e13-8cd3-18ed16bbc385

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tangential_positive_of_tHess
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_left_energy_component_barrier_ball
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_quadPos_tHess_of_det_pos
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_smoothAt_of_secondCollisionFree
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Filter Topology

noncomputable section

theorem sq_one_sub_two_zNormSq_le (s : Phase) :
    (1 - 2 * zNormSq s) ^ 2 ≤ secondCollisionDistanceSq s := by
  unfold zNormSq secondCollisionDistanceSq
  nlinarith [sq_nonneg (s 1)]

theorem mem_U_of_two_zNormSq_le {s : Phase} (hz : 2 * zNormSq s ≤ 3 / 5) : s ∈ U := by
  show 0 < secondCollisionDistanceSq s
  have h1 : (2 : ℝ) / 5 ≤ 1 - 2 * zNormSq s := by linarith
  nlinarith [sq_one_sub_two_zNormSq_le s]

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (μ c : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2) (hc0 : 21 / 10 ≤ c)
    (hrad : ∀ s ∈ leftEnergyComponent μ c, 0 < ∑ i, s i * kGrad μ c s i)
    (hdet : ∀ s ∈ leftEnergyComponent μ c, 0 < (tHess μ c s).det) :
    HasPositiveTangentialHessianOn (leviCivitaHamiltonian μ c) (leftEnergyComponent μ c) := by
  have memU : ∀ {s}, s ∈ leftEnergyComponent μ c → s ∈ U := fun hs =>
    mem_U_of_two_zNormSq_le (by
      linarith [left_energy_component_barrier_ball μ c hμ0 hμhalf hc0 _ hs])
  refine ⟨fun s hs => (leviCivita_smoothAt_of_secondCollisionFree μ c s (memU hs)).of_le
    (WithTop.coe_le_coe.mpr le_top), ?_⟩
  intro s hs v hv hker
  have hg : kGrad μ c s ≠ 0 := by
    intro h0
    have h := hrad s hs
    simp [h0] at h
  exact tangential_positive_of_tHess μ c s (memU hs) hg
    (quadPos_tHess_of_det_pos μ c hμ0 hμhalf hc0 hdet s hs) v hv hker
