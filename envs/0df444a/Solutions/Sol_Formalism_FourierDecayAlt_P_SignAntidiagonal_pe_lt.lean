-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:43:37.792998+00:00
-- url     : https://prove2.me/submissions/7a5613f7-24bb-4a6b-8e08-323ffad902d0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {k r p : ℕ} (h : p < 2 * r + k + 1) : (pe k r p).val = p := by
  rw [pe_val]
  omega
end Formalism.FourierDecayAlt.P.SignAntidiagonal
