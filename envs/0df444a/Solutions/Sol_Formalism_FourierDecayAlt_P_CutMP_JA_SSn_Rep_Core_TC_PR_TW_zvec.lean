-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.zvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:23.049657+00:00
-- url     : https://prove2.me/submissions/a14db36a-bdf7-4f3a-9d10-2946b94a597e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_Rep_Core_TC_PR_TW_qdet_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
theorem _root_.solution {n : ℕ} {F : Fin n → Fin n → Module.End ℂ V} {y : Fin n → Module.End ℂ V} (hF : GlRel F) (hy : IsVec F y)
    (u : ℂ) : IsVec F (fun x => qdet F u * y x) := by
  intro a b c
  have e1 : F a b * (qdet F u * y c) = qdet F u * (F a b * y c) := by
    rw [← mul_assoc, ← qdet_comm hF u a b, mul_assoc]
  rw [e1, mul_assoc, ← mul_sub, hy a b c]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
