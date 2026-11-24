-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.uni_nset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:50:24.306315+00:00
-- url     : https://prove2.me/submissions/d8bb83d3-75c0-4703-8136-4ea19d842b17

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_first_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_middle_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_last_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (hU : (blk3 1 A12 A13 0 1 A23 0 0 1)ᴴ * Hpk k (j + ρ) * blk3 1 A12 A13 0 1 A23 0 0 1 = Hpk k (j + ρ)) :
    blk3 1 A12 A13 0 1 A23 0 0 1 ∈ Nset k (j + ρ) := by
  refine ⟨hU, ?_, ?_⟩
  · intro a i hai
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, hy⟩ := (eB k j ρ).surjective (eI k (j + ρ) a)
    rw [← hy, block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    have hv := congrArg Fin.val hy
    have ha := a.isLt
    simp only [eI] at hv
    rw [← hv] at hai
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [block_index_first_val, block_index_middle_val, block_index_last_val] at hv hai <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)
  · intro i c hc1 hc2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective c
    rw [block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [block_index_first_val, block_index_middle_val, block_index_last_val] at hc1 hc2 hi <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)
end Formalism.FourierDecayAlt.P.Ux3
