-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.lemmaQOfParts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:21.291719+00:00
-- url     : https://prove2.me/submissions/0a18a71a-623d-4c83-a732-77375d751158

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_lemmaQ

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
theorem _root_.solution : LemmaQOfParts := fun _ _ => lemmaQ
end Formalism.FourierDecayAlt.P.GramProductIdentities
