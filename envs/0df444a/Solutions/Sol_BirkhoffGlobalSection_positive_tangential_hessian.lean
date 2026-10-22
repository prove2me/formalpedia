-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_tangential_hessian
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T18:31:07.248879+00:00
-- url     : https://prove2.me/submissions/f5a21024-0244-4ddd-8c30-a2aee0603892

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_positive_tangential_hessian_of_radial_and_det
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_left_energy_component_barrier_ball
import Theorems.Thm_BirkhoffGlobalSection_momentum_bound
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_radial_derivative_pos_of_reduced
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_radial_poly_pos
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHess_det_pos
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

/-- `R² = (1-μ) - 2 zᵀ B z`, the squared radius of the momentum fiber of `K = 0`. -/
def radR2 (μ c Z u r : ℝ) : ℝ :=
  (1 - μ) - 2 * c * Z + 2 * μ * Z / r + (4 * Z ^ 2 + μ ^ 2) * Z - 4 * μ * Z * u

/-- `v = w + A(z) z = w - cen`. -/
def fibV1 (μ : ℝ) (s : Phase) : ℝ := s 2 - (2 * zNormSq s + μ) * s 1

def fibV2 (μ : ℝ) (s : Phase) : ℝ := s 3 + (2 * zNormSq s - μ) * s 0

theorem secondCollisionDistanceSq_eq (s : Phase) :
    secondCollisionDistanceSq s = 4 * zNormSq s ^ 2 - 4 * uCoord s + 1 := by
  unfold secondCollisionDistanceSq zNormSq uCoord; ring

theorem fiber_normSq (μ c r : ℝ) (hr : r ≠ 0) (s : Phase) :
    fibV1 μ s ^ 2 + fibV2 μ s ^ 2 =
      radR2 μ c (zNormSq s) (uCoord s) r + 2 * (pP μ c s - μ * (zNormSq s / r)) := by
  unfold fibV1 fibV2 radR2 pP wNormSq zNormSq uCoord
  field_simp
  ring

theorem radrR2_eq (μ c Z u r : ℝ) (hr : r ≠ 0) :
    radrR2 μ c Z u r = r * radR2 μ c Z u r := by
  unfold radrR2 radR2; field_simp; ring

theorem rD_pos {s : Phase} (hs : s ∈ U) : 0 < rD s := Real.sqrt_pos.mpr hs

theorem leviCivitaHamiltonian_eq_pP (μ c : ℝ) (s : Phase) :
    leviCivitaHamiltonian μ c s = pP μ c s - μ * (zNormSq s / rD s) := by
  unfold leviCivitaHamiltonian pP rD; ring

theorem sq_one_sub_two_zNormSq_le (s : Phase) :
    (1 - 2 * zNormSq s) ^ 2 ≤ secondCollisionDistanceSq s := by
  unfold zNormSq secondCollisionDistanceSq
  nlinarith [sq_nonneg (s 1)]

theorem mem_U_of_two_zNormSq_le {s : Phase} (hz : 2 * zNormSq s ≤ 3 / 5) : s ∈ U := by
  show 0 < secondCollisionDistanceSq s
  have h1 : (2 : ℝ) / 5 ≤ 1 - 2 * zNormSq s := by linarith
  nlinarith [sq_one_sub_two_zNormSq_le s]

theorem rD_sq {s : Phase} : rD s ^ 2 = secondCollisionDistanceSq s :=
  Real.sq_sqrt (by unfold secondCollisionDistanceSq; positivity)

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (μ c : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000) :
    HasPositiveTangentialHessianOn
      (leviCivitaHamiltonian μ c) (leftEnergyComponent μ c) := by
  have hz : ∀ s ∈ leftEnergyComponent μ c, 2 * zNormSq s ≤ (3 - 2 * μ) / 5 := fun s hs =>
    (left_energy_component_barrier_ball μ c hμ0 hμhalf hc0 s hs).le
  have hU : ∀ s ∈ leftEnergyComponent μ c, s ∈ U := fun s hs =>
    mem_U_of_two_zNormSq_le (by linarith [hz s hs])
  have hK : ∀ s ∈ leftEnergyComponent μ c, pP μ c s - μ * (zNormSq s / rD s) = 0 := fun s hs => by
    rw [← leviCivitaHamiltonian_eq_pP]; exact (connectedComponentIn_subset _ _ hs).1
  refine positive_tangential_hessian_of_radial_and_det μ c hμ0 hμhalf hc0 ?_ ?_
  · -- (C): the radial derivative, from the reduced polynomial inequalities
    intro s hs
    have hr := rD_pos (hU s hs)
    have hfib := fiber_normSq μ c (rD s) hr.ne' s
    rw [hK s hs, mul_zero, add_zero] at hfib
    have hR2 : 0 ≤ radR2 μ c (zNormSq s) (uCoord s) (rD s) := by rw [← hfib]; positivity
    have hR : 0 ≤ radrR2 μ c (zNormSq s) (uCoord s) (rD s) := by
      rw [radrR2_eq μ c _ _ _ hr.ne']; positivity
    have hZ : 0 ≤ zNormSq s := by unfold zNormSq; positivity
    have hu1 : uCoord s ≤ zNormSq s := by unfold uCoord zNormSq; nlinarith [sq_nonneg (s 1)]
    have hu2 : -zNormSq s ≤ uCoord s := by unfold uCoord zNormSq; nlinarith [sq_nonneg (s 0)]
    have hr2 : rD s ^ 2 = 4 * zNormSq s ^ 2 - 4 * uCoord s + 1 := by
      rw [rD_sq, secondCollisionDistanceSq_eq]
    exact radial_derivative_pos_of_reduced μ c (rD s) s hr (hK s hs)
      (radial_poly_pos μ c _ _ _ hμ0 hμhalf hc0 hc1 hZ (hz s hs) hu1 hu2 hr hr2 hR)
  · -- (D): the determinant of the tangential Hessian
    intro s hs
    exact tHess_det_pos μ c (rD s) s hμ0 hμhalf hc0 hc1 (rD_pos (hU s hs)) rD_sq (hK s hs) (hz s hs)
      (by
        have h := momentum_bound μ c hμ0 hμhalf hc0 s hs
        have hw0 : 0 ≤ wNormSq s := by unfold wNormSq; positivity
        nlinarith [Real.sq_sqrt hw0, Real.sqrt_nonneg (wNormSq s)])
