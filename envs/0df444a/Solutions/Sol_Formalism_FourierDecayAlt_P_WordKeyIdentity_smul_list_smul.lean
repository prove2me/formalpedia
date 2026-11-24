-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordKeyIdentity.smul_list_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:38.11585+00:00
-- url     : https://prove2.me/submissions/c096dbb4-bca5-49ff-a54c-149046ee92aa

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordKeyIdentity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.WordKeyIdentity
theorem _root_.solution {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (l : List ι) (a : ι → ℂ)
    (x : ι → E) : c • (l.map fun i => a i • x i).sum = (l.map fun i => a i • (c • x i)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [smul_add, ih, smul_comm c (a i)]
end Formalism.FourierDecayAlt.P.WordKeyIdentity
