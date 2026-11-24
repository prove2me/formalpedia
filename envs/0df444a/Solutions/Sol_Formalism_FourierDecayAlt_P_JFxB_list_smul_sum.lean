-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.list_smul_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:29:23.640055+00:00
-- url     : https://prove2.me/submissions/985c7c84-9580-4231-b802-54ce9e427ab4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts

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
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {ι : Type*} (a : ℂ) (l : List ι)
    (c : ι → ℂ) (φ : ι → V) :
    a • (l.map fun i => c i • φ i).sum = (l.map fun i => c i • (a • φ i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [smul_add, ih, smul_comm a (c i)]
end Formalism.FourierDecayAlt.P.JFxB
