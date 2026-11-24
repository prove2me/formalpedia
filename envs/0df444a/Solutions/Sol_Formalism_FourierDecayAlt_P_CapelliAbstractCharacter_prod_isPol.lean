-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.prod_isPol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:26:00.572798+00:00
-- url     : https://prove2.me/submissions/dd4198e4-cbe3-480c-b008-a83c9bbb2830

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_IsPol_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (t : ℕ) (α β : Fin t → A) :
    IsPol (t + 1) (fun u : ℂ => (List.ofFn fun k : Fin t => u • α k + β k).prod) := by
  induction t with
  | zero => simpa using IsPol.const (1 : A)
  | succ t ih =>
    have h1 := ih (fun k => α k.succ) (fun k => β k.succ)
    have h2 := (h1.map (LinearMap.mulLeft ℂ (α 0))).shift
    have h3 := (h1.map (LinearMap.mulLeft ℂ (β 0))).up
    have h4 := h2.add h3
    convert h4 using 1
    funext u
    simp only [List.ofFn_succ, List.prod_cons, LinearMap.mulLeft_apply, add_mul, smul_mul_assoc]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
