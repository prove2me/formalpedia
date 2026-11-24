-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.rn_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:10:59.279862+00:00
-- url     : https://prove2.me/submissions/6bbf54ae-f8ea-4b26-a5b4-3f7a4a3687de

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_coords

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
theorem _root_.solution (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (S : Matrix (Fin j) (Fin j) ℂ) (hS : Sᴴ = -S) :
    Rn k j ρ (Matrix.of.symm c, skewCoords S) = blk3 1 (-(G.wMat j * cᴴ * Hpk k ρ))
      (G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * Hpk k ρ * c) + S)) 0 1 c 0 0 1 := by
  rw [rn_eq]
  simp only [Equiv.apply_symm_apply, skewOf_coords S hS]
end Formalism.FourierDecayAlt.P.Ux3
