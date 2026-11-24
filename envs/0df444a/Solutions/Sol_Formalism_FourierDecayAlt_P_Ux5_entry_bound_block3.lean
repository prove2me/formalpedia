-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.entry_bound_block3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:45:24.720989+00:00
-- url     : https://prove2.me/submissions/b3b89028-ce18-462c-9d98-03a9785defe7

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_aux_statement_16

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {c : ℝ} {A11 : Matrix (Fin j) (Fin j) ℂ} {A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : Matrix (Fin j) (Fin j) ℂ} {A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : B.Mat k ρ}
    {A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : Matrix (Fin j) (Fin j) ℂ}
    {A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : EB A11 c) (h12 : EB A12 c) (h13 : EB A13 c) (h21 : EB A21 c) (h22 : EB A22 c) (h23 : EB A23 c)
    (h31 : EB A31 c) (h32 : EB A32 c) (h33 : EB A33 c) : EB (blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33) c := by
  intro x y
  obtain ⟨x', rfl⟩ := (eB k j ρ).surjective x
  obtain ⟨y', rfl⟩ := (eB k j ρ).surjective y
  rw [aux_statement_16]
  rcases x' with ((a | a) | a) <;> rcases y' with ((b | b) | b) <;> simp only [fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, fromRows_apply_inl, fromRows_apply_inr,
    fromCols_apply_inl, fromCols_apply_inr] <;>
    first | exact h11 _ _ | exact h12 _ _ | exact h13 _ _ | exact h21 _ _ | exact h22 _ _ | exact h23 _ _ | exact h31 _ _ | exact h32 _ _ | exact h33 _ _
end Formalism.FourierDecayAlt.P.Ux5
