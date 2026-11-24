-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.det_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:51.664049+00:00
-- url     : https://prove2.me/submissions/860a1b4f-0f9d-471b-be75-87a678b61dc8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.of fun a b => star (M a b)).det = star M.det := by
  have e : (Matrix.of fun a b => star (M a b)) = M.conjTranspose.transpose := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.det_transpose, Matrix.det_conjTranspose]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
