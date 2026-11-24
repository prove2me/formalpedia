-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.exch3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:10.108674+00:00
-- url     : https://prove2.me/submissions/2ee5f959-3f6e-409e-9b17-b0924f9be7ca

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_transp_exch
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_Xm_EC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_exch2

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
    (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hr : ∀ l ∈ w, star l.pt = l.pt) (hY : star Y = Y) :
    (Xm w Y)ᵀ * lift0 ((Ts σ Y).map star) * d0 (bT σ w) =
      d0 (bT σ w) * lift0 ((Ts σ Y).map star) * (Xm w Y)ᵀ := by
  have hc : ∀ i j, EC ((lift0 (Ts σ Y)ᴴ : M2 (SlopeTestRemainingChoices S A)) i j) (Xm w Y) := fun i j =>
    Xm_EC w Y fun l _ r s => (eU_io l.intersection_update_fsHerm_neg_one r s _).symm
  exact transp_exch hc (exch2 σ w Y hσ hw hr hY)
end Formalism.FourierDecayAlt.P.Wd6
