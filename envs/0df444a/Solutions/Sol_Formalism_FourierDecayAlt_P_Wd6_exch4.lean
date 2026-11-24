-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.exch4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:52.811359+00:00
-- url     : https://prove2.me/submissions/8ee0ba1f-8b48-4009-afbc-91ca6c0d6501

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transp_exch
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_Xp_EC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_Xp_lift0_d0_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution (σ : Site A) (w : List (Letter K S)) (Y : K) (hσ : IsSite σ)
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    lift0 (Ts σ Y)ᵀ * (Xp w Y)ᵀ * d0 (bT σ w) = d0 (bT σ w) * (Xp w Y)ᵀ * lift0 (Ts σ Y)ᵀ := by
  have hc : ∀ i j, EC ((Xp w Y : M2 (SlopeTestRemainingChoices S A)) i j) (lift0 (Ts σ Y)) := fun i j k l =>
    (Xp_EC (z := io (Ts σ Y k l)) w Y (fun l _ r s => (eU_io l.intersection_update_fsHerm_neg_one r s _).symm) i j).symm
  exact transp_exch hc (Xp_lift0_d0_comm σ w Y hσ hw)
end Formalism.FourierDecayAlt.P.Wd6
