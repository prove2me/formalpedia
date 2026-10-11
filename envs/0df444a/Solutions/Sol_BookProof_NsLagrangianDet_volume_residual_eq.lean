-- Prove2me | solution 1 for BookProof.NsLagrangianDet.volume_residual_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:25.516451+00:00
-- url     : https://prove2.me/submissions/21f65e7d-c31e-46db-bcd7-711d0f9329c8

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.volume_residual_eq
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
import Theorems.Thm_BookProof_NsLagrangianDet_phase_zero
import Theorems.Thm_BookProof_NsLagrangianDet_det_deformation_eq
import Theorems.Thm_BookProof_NsLagrangianDet_zero_mem_waveSet
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) :
    (1 + dispGrad kv y a).det - 1 = ∑ q ∈ waveSet kv, ev y (volCoef kv q) * phase q a := by

  classical
  simp only [volCoef, map_sub, sub_mul, Finset.sum_sub_distrib, det_deformation_eq]
  congr 1
  have : ∀ q : Fin 3 → ℝ, ev y (if q = 0 then 1 else 0) * phase q a
      = if q = 0 then 1 else 0 := by
    intro q
    split_ifs with h
    · subst h; simp [phase_zero]
    · simp
  rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_ite_eq' , if_pos (zero_mem_waveSet kv)]
