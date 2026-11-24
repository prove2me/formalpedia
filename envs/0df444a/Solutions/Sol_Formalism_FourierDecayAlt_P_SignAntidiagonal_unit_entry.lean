-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.unit_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:23:39.322618+00:00
-- url     : https://prove2.me/submissions/8e47d506-aa0c-4502-b0d3-143e5f68628d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hU : Xᴴ * Hpk k r + Hpk k r * X = 0) (i j : Fin (2 * r + k + 1)) :
    (∑ l, star (X l i) * Hpk k r l j) + ∑ l, Hpk k r i l * X l j = 0 := by
  have h := congrFun (congrFun hU i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
end Formalism.FourierDecayAlt.P.SignAntidiagonal
