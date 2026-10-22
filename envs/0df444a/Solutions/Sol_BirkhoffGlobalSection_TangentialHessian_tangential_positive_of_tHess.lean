-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.tangential_positive_of_tHess
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-26T17:56:45.896386+00:00
-- url     : https://prove2.me/submissions/ec2edab2-2e68-4e6a-8a25-ccb8a4af5602

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tangential_positive_of_frame
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

theorem quadForm_symmetrize (M : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    ∑ i, ∑ j, a i * a j * ((M i j + M j i) / 2) = ∑ i, ∑ j, a i * a j * M i j := by
  simp only [Fin.sum_univ_three]
  ring

theorem quadForm_transpose (M : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) :
    ∑ i, ∑ j, a i * a j * M j i = ∑ i, ∑ j, a i * a j * M i j := by
  simp only [Fin.sum_univ_three]
  ring

/-- `D²F(s)` read off from the iterated directional derivative. -/
theorem fderiv_apply_const_eq {F : Phase → ℝ} {s : Phase} (hF : ContDiffAt ℝ 2 F s)
    (u v : Phase) :
    fderiv ℝ (fun x => fderiv ℝ F x u) s v = fderiv ℝ (fderiv ℝ F) s v u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) s :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const u)]
  simp

theorem grad_eq_kGrad' (μ c : ℝ) {s : Phase} (hs : s ∈ U) :
    grad (leviCivitaHamiltonian μ c) s = kGrad μ c s :=
  funext ((leviCivita_explicit_derivatives μ c).1 s hs)

theorem contDiffAt_two_of_mem_U (μ c : ℝ) {s : Phase} (hs : s ∈ U) :
    ContDiffAt ℝ 2 (leviCivitaHamiltonian μ c) s :=
  (leviCivita_smoothAt_of_secondCollisionFree μ c s hs).of_le
    (WithTop.coe_le_coe.mpr le_top)

end

end BirkhoffGlobalSection.TangentialHessian.Sol

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian BirkhoffGlobalSection.TangentialHessian.Sol

theorem solution (μ c : ℝ) (s : Phase) (hs : s ∈ U)
    (hg : kGrad μ c s ≠ 0) (hQ : QuadPos (tHess μ c s))
    (v : Phase) (hv : v ≠ 0)
    (hker : fderiv ℝ (leviCivitaHamiltonian μ c) s v = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ (leviCivitaHamiltonian μ c) x v) s v := by
  have hF := contDiffAt_two_of_mem_U μ c hs
  refine tangential_positive_of_frame _ s hF (by rwa [grad_eq_kGrad' μ c hs]) ?_ v hv hker
  intro a ha
  have h := hQ a ha
  have hsym : ∑ i, ∑ j, a i * a j * tHess μ c s i j =
      ∑ i, ∑ j, a i * a j * frameHess (kGrad μ c s) (kHess μ c s) i j :=
    quadForm_symmetrize _ a
  rw [hsym, ← quadForm_transpose] at h
  convert h using 4 with i _ j _
  rw [grad_eq_kGrad' μ c hs, ← fderiv_apply_const_eq hF,
    (leviCivita_explicit_derivatives μ c).2.1 s hs]
  simp only [frameHess]
