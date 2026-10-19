-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qg3D_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:37:10.288401+00:00
-- url     : https://prove2.me/submissions/8db31029-d481-4684-b5b5-fa62806ca351

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgMom_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionOps_symmetricOn
-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qg3D_quadForm
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {D : Submodule ℂ (L2d 84)}
theorem h42_cast (a : Fin 84 → ℝ) (b : Fin 64 → ℝ) :
    (((1 / 2 : ℝ)) : ℂ) * (∑ j, ((a j : ℝ) : ℂ) + ∑ m, ((b m : ℝ) : ℂ))
      = (((1 / 2 * ∑ j, a j + 1 / 2 * ∑ m, b m : ℝ)) : ℂ) := by
  push_cast; ring

theorem solution (Φ : CoreRep 84 D) (x : D) :
    quadForm (qg3DHamiltonian Φ) x
      = 1 / 2 * (∑ j, qgKappa j * ‖((qgMom Φ j x : D) : L2d 84)‖ ^ 2)
        + 1 / 2 * ∑ m, ‖((torsionOps Φ m x : D) : L2d 84)‖ ^ 2 := by
  have hinner : (inner ℂ ((x : D) : L2d 84) (qg3DHamiltonian Φ x) : ℂ)
      = (((1 / 2 * (∑ j, qgKappa j * ‖((qgMom Φ j x : D) : L2d 84)‖ ^ 2)
          + 1 / 2 * ∑ m, ‖((torsionOps Φ m x : D) : L2d 84)‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [qg3DHamiltonian, signedOp, signedOpDom, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply,
      Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sum]
    rw [inner_smul_right, inner_add_right, inner_sum, inner_sum]
    have h1 : ∀ j, (inner ℂ ((x : D) : L2d 84) (((((qgKappa j : ℝ) : ℂ) • qgMom Φ j (qgMom Φ j x) : D)) : L2d 84) : ℂ)
        = ((qgKappa j * ‖((qgMom Φ j x : D) : L2d 84)‖ ^ 2 : ℝ) : ℂ) := by
      intro j
      rw [Submodule.coe_smul, inner_smul_right,
        BookProof.YangMillsFriedrichs.inner_sq_eq_normSq (BookProof.QuantumGravity3DGauge.qgMom_symmetricOn Φ j) x]
      push_cast; ring
    have h2 : ∀ m, (inner ℂ ((x : D) : L2d 84) ((torsionOps Φ m (torsionOps Φ m x) : D) : L2d 84) : ℂ)
        = ((‖((torsionOps Φ m x : D) : L2d 84)‖ ^ 2 : ℝ) : ℂ) := fun m =>
      BookProof.YangMillsFriedrichs.inner_sq_eq_normSq (BookProof.QuantumGravity3DGauge.torsionOps_symmetricOn Φ m) x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul] at h1 ⊢
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_congr rfl fun m _ => h2 m]
    exact h42_cast (fun j => qgKappa j * ‖((qgMom Φ j x : D) : L2d 84)‖ ^ 2)
      (fun m => ‖((torsionOps Φ m x : D) : L2d 84)‖ ^ 2)
  exact (congrArg Complex.re hinner).trans (Complex.ofReal_re _)

