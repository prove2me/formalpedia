-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.keyS_wI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:08:31.653887+00:00
-- url     : https://prove2.me/submissions/b5477deb-dd72-420c-8c82-d09dd21a340c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarInverseSimplification
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthExpansionIdentity
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
theorem _root_.solution (k r : ℕ) (w : Fin (k + 1)) : keyS k r (wI k r w) = r + w.val + r := by
  have := w.isLt
  unfold keyS wI; simp only; rw [if_neg (by omega)]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
