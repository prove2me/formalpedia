-- Prove2me | solution 1 for BookProof.NsLagrangianDet.phase_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:16.383294+00:00
-- url     : https://prove2.me/submissions/dc991e55-fec9-4375-a451-2ec632aafb37

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.phase_sum
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} (s : Finset ι) (w : ι → Fin 3 → ℝ) (a : Fin 3 → ℝ) :
    ∏ i ∈ s, phase (w i) a = phase (∑ i ∈ s, w i) a := by

  simp only [phase]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, ← Complex.ofReal_sum]
  congr 2
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul]
