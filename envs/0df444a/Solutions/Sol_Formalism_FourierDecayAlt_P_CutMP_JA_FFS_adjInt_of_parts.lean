-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjInt_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:55:09.533987+00:00
-- url     : https://prove2.me/submissions/2e184cfc-d0b8-4733-8100-e5f6cd12b594

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjIntCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.FFS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
theorem _root_.solution (hA : AdjIntAsm) (hU : RhoUni) (hF : FormAdj) : AdjInt := hA hU hF
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
