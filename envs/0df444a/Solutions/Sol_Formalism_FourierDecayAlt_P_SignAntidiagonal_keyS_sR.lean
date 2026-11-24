-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.keyS_sR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:46.002123+00:00
-- url     : https://prove2.me/submissions/7073a6e6-1d9f-4f73-a0cf-3b0e52b1d01b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_keyS_esI
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
theorem _root_.solution (k r m : ℕ) (hm : m ≤ r) (l : Fin m) : keyS k r (sR k r m hm l) = l.val := by
  simp only [sR]
  rw [keyS_esI]
  rfl
end Formalism.FourierDecayAlt.P.SignAntidiagonal
