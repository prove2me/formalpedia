-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.block3_lower_blocks_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:31:11.161429+00:00
-- url     : https://prove2.me/submissions/68e532af-70d9-401d-a626-55e90f49856e

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_index_first_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_index_middle_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_index_last_val_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (h21 : A21 = 0) (h31 : A31 = 0) (i b : Fin (2 * (j + ρ) + k + 1)) (hb : b.val < j) (hi : j ≤ i.val) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 i b = 0 := by
  obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
  obtain ⟨y, rfl⟩ := (eB k j ρ).surjective b
  rw [block3_apply]
  rcases y with ((c | c) | c)
  · rcases x with ((a | a) | a)
    · rw [block_index_first_val_eq] at hi
      exact absurd hi (not_le.2 a.isLt)
    · simp [h21]
    · simp [h31]
  · rw [block_index_middle_val_eq] at hb
    omega
  · rw [block_index_last_val_eq] at hb
    omega
end Formalism.FourierDecayAlt.P.Ux4
