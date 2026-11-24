-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.block3_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:17:16.230409+00:00
-- url     : https://prove2.me/submissions/e9e99993-c96b-4e4a-b4da-2d62bcb4985c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_ext_eB

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
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 + blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 + ToralGalois) (A12 + cocyclesToWachVectorsExponent) (A13 + B13) (A21 + B21) (A22 + B22) (A23 + B23) (A31 + B31) (A32 + B32) (A33 + B33) := by
  apply ext_eB
  intro x y
  rw [Matrix.add_apply, block3_apply, block3_apply, block3_apply]
  rcases x with ((a | a) | a) <;> rcases y with ((b | b) | b) <;> simp
end Formalism.FourierDecayAlt.P.Ux4
