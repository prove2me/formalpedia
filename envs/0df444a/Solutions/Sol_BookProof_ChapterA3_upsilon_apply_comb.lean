-- Prove2me | solution 1 for BookProof.ChapterA3.upsilon_apply_comb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:11:46.294701+00:00
-- url     : https://prove2.me/submissions/b1c78e4e-f21a-4fc0-b2f8-7cfa2743e87c

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.upsilon_apply_comb
import Mathlib
import Definitions.Def_ChapterA3h
import Theorems.Thm_BookProof_ChapterA3_upsilon_recon
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (T : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℂ) :
    Tᴴ * (∑ ν, x ν • pauliσ ν) * T = ∑ μ, (∑ ν, UpsilonC T μ ν * x ν) • pauliσ μ := by

  set v : Fin 4 → ℂ := fun ν => x ν;
  -- By definition of $U$, we know that $Tᴴ * pauliσ ν * T = ∑ μ, U μ ν • pauliσ μ$.
  have hU : ∀ ν, Tᴴ * pauliσ ν * T = ∑ μ, UpsilonC T μ ν • pauliσ μ := fun ν => upsilon_recon T ν
  convert congr_arg ( fun m => ∑ ν, v ν • m ν ) ( funext hU ) using 1;
  · simp [ Matrix.sum_mul, mul_assoc, Finset.mul_sum _ _ _ ];
    rfl;
  · simp only [mul_comm, Finset.sum_smul, Finset.smul_sum, smul_smul];
    exact Finset.sum_comm
