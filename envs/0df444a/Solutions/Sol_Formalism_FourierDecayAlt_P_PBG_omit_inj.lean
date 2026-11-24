-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.omit_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:42:49.413394+00:00
-- url     : https://prove2.me/submissions/f769f936-cb80-4640-8027-0fcfd8c3920a

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution {k r m : ℕ} (hm : m + 1 ≤ r) :
    Function.Injective (fun l0 : Fin (m + 1) => xR k r (m + 1) hm ∘ l0.succAbove) := by
  intro l0 l1 h
  apply Fin.succAbove_left_injective
  funext l
  have h2 := congrArg Fin.val (congrFun h l)
  exact Fin.ext (by simpa [C3.xR, eI] using h2)
end Formalism.FourierDecayAlt.P.PBG
