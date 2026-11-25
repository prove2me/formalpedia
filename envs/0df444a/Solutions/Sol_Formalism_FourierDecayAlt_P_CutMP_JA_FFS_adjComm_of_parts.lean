-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjComm_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:29:16.191799+00:00
-- url     : https://prove2.me/submissions/19f92224-1963-4230-9724-22a9726840ed

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAdjCut

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
theorem _root_.solution (hF : FundG) (hC : AdjCont) (hI : AdjInt) : AdjComm := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs hc f hf hfc hfs p hp g hg
  obtain ⟨c1, c2⟩ := hC k r Wp Wq D Θ hs f hf hfc hfs p hp
  exact hF k r Wp Wq D _ _ c1 c2 (fun φ h1 h2 h3 => hI k r Wp Wq D Θ hs hc f hf hfc hfs p hp φ h1 h2 h3) g hg
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
