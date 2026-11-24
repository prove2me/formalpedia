-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.wsum_flatMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:18.131966+00:00
-- url     : https://prove2.me/submissions/f42af5b7-2d34-44e0-890d-f5fbd132ac6d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_wsum_append

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution {ι : Type*} (l : List ι) (F : ι → List (ℂ × List (Mat k r))) (f : Mat k r → E) (g : Mat k r) :
    wsum (l.flatMap F) f g = (l.map fun i => wsum (F i) f g).sum := by
  induction l with
  | nil => simp [wsum]
  | cons i l ih => simp [List.flatMap_cons, wsum_append, ih]
end Formalism.FourierDecayAlt.P.JFxB
