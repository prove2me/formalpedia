-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.left_energy_component_barrier_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:40:48.9332+00:00
-- url     : https://prove2.me/submissions/cae0256c-d866-40d5-a314-2f9879770f5b

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_lc_barrier_positive
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

/-- The left collision point lies on the selected component for `0 ≤ μ ≤ 1`,
so in particular at the `μ = 0` edge of Proposition 4.4 (the platform lemma
`leftCollisionPoint_mem_leftEnergyComponent` needs `0 < μ`). -/
theorem leftCollisionPoint_mem_of_le (μ c : ℝ) (hμ1 : μ ≤ 1) :
    leftCollisionPoint μ ∈ leftEnergyComponent μ c := by
  apply mem_connectedComponentIn
  refine ⟨?_, ?_⟩
  · have h : Real.sqrt (1 - μ) ^ 2 = 1 - μ := Real.sq_sqrt (by linarith)
    simp [leviCivitaHamiltonian, leftCollisionPoint, wNormSq, zNormSq,
      secondCollisionDistanceSq, h]
  · simp [leftCollisionPoint, secondCollisionDistanceSq]

theorem leviCivitaHamiltonian_eq_pP (μ c : ℝ) (s : Phase) :
    leviCivitaHamiltonian μ c s = pP μ c s - μ * (zNormSq s / rD s) := by
  unfold leviCivitaHamiltonian pP rD; ring

theorem continuous_zNormSq : Continuous zNormSq := by unfold zNormSq; fun_prop

theorem sq_one_sub_two_zNormSq_le (s : Phase) :
    (1 - 2 * zNormSq s) ^ 2 ≤ secondCollisionDistanceSq s := by
  unfold zNormSq secondCollisionDistanceSq
  nlinarith [sq_nonneg (s 1)]

theorem one_sub_two_zNormSq_le_rD (s : Phase) : 1 - 2 * zNormSq s ≤ rD s :=
  Real.le_sqrt_of_sq_le (sq_one_sub_two_zNormSq_le s)

theorem rD_ge_two_fifths {s : Phase} (hz : 2 * zNormSq s ≤ 3 / 5) : 2 / 5 ≤ rD s := by
  linarith [one_sub_two_zNormSq_le_rD s]

theorem rD_sq {s : Phase} : rD s ^ 2 = secondCollisionDistanceSq s :=
  Real.sq_sqrt (by unfold secondCollisionDistanceSq; positivity)

/-- `K = ½|w + A z|² + b₁ z₁² + b₂ z₂² - (1-μ)/2`, Joung--van Koert (4.1). -/
theorem leviCivitaHamiltonian_eq_AB_rD (μ c : ℝ) (s : Phase) :
    leviCivitaHamiltonian μ c s =
      ((s 2 - (2 * zNormSq s + μ) * s 1) ^ 2 + (s 3 + (2 * zNormSq s - μ) * s 0) ^ 2) / 2
        + (c - (2 * zNormSq s - μ) ^ 2 / 2 - μ / rD s) * s 0 ^ 2
        + (c - (2 * zNormSq s + μ) ^ 2 / 2 - μ / rD s) * s 1 ^ 2 - (1 - μ) / 2 := by
  rw [leviCivitaHamiltonian_eq_pP]
  unfold pP wNormSq zNormSq
  ring

theorem leviCivitaHamiltonian_pos_of_barrier {μ c : ℝ} (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) {s : Phase} (hz : 2 * zNormSq s = (3 - 2 * μ) / 5) :
    0 < leviCivitaHamiltonian μ c s := by
  have hz' : 2 * zNormSq s ≤ 3 / 5 := by linarith
  have hr : 0 < rD s := by linarith [rD_ge_two_fifths hz']
  have hA := lc_barrier_positive μ c (s 0) (s 1) (rD s) hμ0 hμhalf hc0 hz hr rD_sq
  rw [leviCivitaHamiltonian_eq_AB_rD]
  simp only [zNormSq] at hA ⊢
  nlinarith [sq_nonneg (s 2 - (2 * (s 0 ^ 2 + s 1 ^ 2) + μ) * s 1),
    sq_nonneg (s 3 + (2 * (s 0 ^ 2 + s 1 ^ 2) - μ) * s 0)]

theorem component_subset_ball' {μ c : ℝ} (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) :
    leftEnergyComponent μ c ⊆ {s | 2 * zNormSq s < (3 - 2 * μ) / 5} := by
  intro s hs
  by_contra hlt
  rw [Set.mem_ofPred_eq, not_lt] at hlt
  have hs₀ := leftCollisionPoint_mem_of_le μ c (by linarith)
  have hcont : ContinuousOn (fun x : Phase => 2 * zNormSq x) (leftEnergyComponent μ c) :=
    (continuous_const.mul continuous_zNormSq).continuousOn
  have hmem : (3 - 2 * μ) / 5 ∈ Set.Icc (2 * zNormSq (leftCollisionPoint μ)) (2 * zNormSq s) :=
    ⟨by simp [zNormSq, leftCollisionPoint]; linarith, hlt⟩
  obtain ⟨t, ht, htz⟩ :=
    (isPreconnected_connectedComponentIn (F := regularEnergyLocus μ c)).intermediate_value
      hs₀ hs hcont hmem
  have hpos := leviCivitaHamiltonian_pos_of_barrier hμ0 hμhalf hc0 htz
  have hzero := (connectedComponentIn_subset _ _ ht).1
  linarith

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (μ c : ℝ) (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) :
    ∀ s ∈ leftEnergyComponent μ c, 2 * zNormSq s < (3 - 2 * μ) / 5 := by
  exact fun s hs => component_subset_ball' hμ0 hμhalf hc0 hs
