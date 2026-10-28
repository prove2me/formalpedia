-- Prove2me | solution 1 for CoherenceUncertainty.Qubit.relEntCoh_eq_shannon_sub
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:29:04.705716+00:00
-- url     : https://prove2.me/submissions/140ce5cd-fcf3-4d9e-af90-7c3dc53eb830

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_CoherenceUncertainty_Qubit_Model

namespace Aux_CU_rel

open CoherenceUncertainty.Qubit Matrix

lemma dephase_entropy (ρ : Mat2) (U : MBasis) :
    ShadowTomography.QuantumLB.vnEntropy (dephase U ρ) = shannon (prob U ρ) := by
  set p := prob U ρ with hp
  set D : Mat2 := Matrix.diagonal (fun i => ((p i : ℝ) : ℂ)) with hD
  have hDh : D.IsHermitian := by
    rw [hD, Matrix.isHermitian_diagonal_iff]
    intro i; simp [IsSelfAdjoint]
  have hdeph : dephase U ρ = (U : Mat2) * D * (U : Mat2)ᴴ := by
    unfold dephase; rw [← hp, ← hD, star_eq_conjTranspose]
  have hA : (dephase U ρ).IsHermitian := by
    rw [hdeph]; exact isHermitian_mul_mul_conjTranspose _ hDh
  have hU1 : star (U : Mat2) * (U : Mat2) = 1 := Matrix.mem_unitaryGroup_iff'.mp U.2
  have hU2 : (U : Mat2) * star (U : Mat2) = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
  -- trace and determinant
  have htr : (dephase U ρ).trace = ((p 0 + p 1 : ℝ) : ℂ) := by
    rw [hdeph, ← star_eq_conjTranspose, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1,
      Matrix.one_mul, hD, Matrix.trace_diagonal, Fin.sum_univ_two]
    push_cast; ring
  have hdet : (dephase U ρ).det = ((p 0 * p 1 : ℝ) : ℂ) := by
    rw [hdeph, ← star_eq_conjTranspose, Matrix.det_mul, Matrix.det_mul, hD, Matrix.det_diagonal,
      Fin.prod_univ_two]
    have : (U : Mat2).det * (star (U : Mat2)).det = 1 := by
      rw [← Matrix.det_mul, hU2, Matrix.det_one]
    push_cast
    linear_combination (↑(p 0) * ↑(p 1) : ℂ) * this
  have hsum := hA.trace_eq_sum_eigenvalues
  have hprod := hA.det_eq_prod_eigenvalues
  rw [htr, Fin.sum_univ_two] at hsum
  rw [hdet, Fin.prod_univ_two] at hprod
  set l0 := hA.eigenvalues 0
  set l1 := hA.eigenvalues 1
  have hs : l0 + l1 = p 0 + p 1 := by
    have : ((p 0 + p 1 : ℝ) : ℂ) = ((l0 + l1 : ℝ) : ℂ) := by rw [hsum]; push_cast; rfl
    exact_mod_cast this.symm
  have hpr : l0 * l1 = p 0 * p 1 := by
    have : ((p 0 * p 1 : ℝ) : ℂ) = ((l0 * l1 : ℝ) : ℂ) := by rw [hprod]; push_cast; rfl
    exact_mod_cast this.symm
  have hq : (l0 - p 0) * (l0 - p 1) = 0 := by
    have : l1 = p 0 + p 1 - l0 := by linarith
    rw [this] at hpr
    linear_combination -hpr
  unfold ShadowTomography.QuantumLB.vnEntropy shannon
  rw [dif_pos hA, Fin.sum_univ_two, Fin.sum_univ_two]
  rcases mul_eq_zero.mp hq with h | h
  · have h0 : l0 = p 0 := by linarith
    have h1 : l1 = p 1 := by linarith
    rw [show hA.eigenvalues 0 = p 0 from h0, show hA.eigenvalues 1 = p 1 from h1]
  · have h0 : l0 = p 1 := by linarith
    have h1 : l1 = p 0 := by linarith
    rw [show hA.eigenvalues 0 = p 1 from h0, show hA.eigenvalues 1 = p 0 from h1]
    ring

end Aux_CU_rel

open CoherenceUncertainty.Qubit in
theorem solution (ρ : Mat2) (hρ : IsDensity ρ) (U : MBasis) :
    relEntCoh U ρ = shannon (prob U ρ) - ShadowTomography.QuantumLB.vnEntropy ρ := by
  unfold relEntCoh
  rw [Aux_CU_rel.dephase_entropy]
