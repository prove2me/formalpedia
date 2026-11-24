-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.restriction_good_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:48:01.180197+00:00
-- url     : https://prove2.me/submissions/1f8c35f4-ce46-4062-bd21-5eabd0750963

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_fam_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cd_normPow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_wlist_glev
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_wlist_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_wlist_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.ResGFam := by
  intro Wp Wq _ _ _ _ k r z z' π π' D _ _ _ J hJ i
  have hρ : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
      ((∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ)) (OmX r) := by
    have h1 : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
        ∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1)) (OmX r) := by
      refine contDiffOn_prod fun a _ => ?_
      split_ifs
      · exact Qx3.cd_normPow a _
      · exact contDiffOn_const
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
  exact Qx3.fam_res (Fin.zero_le i) (w := fun c => wCell k r i c) (Qx3.wlist_smooth _) hρ
    (fun c hc => Qx3.wlist_glev hc _)
    (fun c _ g hg => Qx3.wlist_comm i c _ (fun a ha => by simpa using (List.mem_filter.1 ha).2) hg) hJ
end Formalism.FourierDecayAlt.P
