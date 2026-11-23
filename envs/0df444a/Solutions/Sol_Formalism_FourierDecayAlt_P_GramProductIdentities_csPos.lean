-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.csPos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:19.441402+00:00
-- url     : https://prove2.me/submissions/65561364-530a-4b91-ab6b-287edca145b4

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_frmS_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_cs_of_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : CSPos := by
  intro A S V _ _ _ _ _ _ _ _ _ ρ M X X' hP
  have := cs_of_pos (frmS ρ M) (fun m => hP m) X X'
  simpa [frmS_apply] using this
end Formalism.FourierDecayAlt.P.GramProductIdentities
