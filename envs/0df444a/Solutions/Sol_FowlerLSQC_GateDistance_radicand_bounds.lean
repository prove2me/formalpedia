-- Prove2me | solution 1 for FowlerLSQC.GateDistance.radicand_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:33:26.238209+00:00
-- url     : https://prove2.me/submissions/cc38ac51-e87f-4eaa-9d70-73d903705fa9

import Mathlib

open scoped Matrix

theorem solution {m : ℕ} (hm : 0 < m) (U V : Matrix.unitaryGroup (Fin m) ℂ) :
    0 ≤ ((m : ℝ) - ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)).trace‖) /
        (m : ℝ) ∧
      ((m : ℝ) - ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)).trace‖) /
        (m : ℝ) ≤ 1 := by
  have hW : (U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ) ∈
      Matrix.unitaryGroup (Fin m) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Submonoid.mul_mem _ (Unitary.star_mem U.2) V.2
  have htr : ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)).trace‖ ≤ m := by
    rw [Matrix.trace]
    calc ‖∑ i, Matrix.diag ((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)) i‖
        ≤ ∑ i, ‖Matrix.diag ((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)) i‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => entry_norm_bound_of_unitary hW i i)
      _ = m := by simp
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 := norm_nonneg ((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)).trace
  refine ⟨div_nonneg (by linarith) hm'.le, ?_⟩
  rw [div_le_one hm']
  linarith
