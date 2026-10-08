-- Prove2me | solution 1 for BookProof.BookBrstYangMills.vecComb_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:47:06.103069+00:00
-- url     : https://prove2.me/submissions/cb4c41c0-53a8-4209-b151-b744aa1615be

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.vecComb_sum
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (κ : Fin n → ℝ) (α : Fin n → ℝ) (β : Fin n → Fin N → ℝ)
    (μ : Fin 4) :
    (∑ h, ((κ h : ℝ) : ℂ) • vecComb (α h) (β h) μ)
      = vecComb (∑ h, κ h * α h) (fun g => ∑ h, κ h * β h g) μ := by

  simp only [vecComb, smul_add, Finset.smul_sum, smul_smul, ← Complex.ofReal_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Complex.ofReal_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_smul, ← Complex.ofReal_sum]
