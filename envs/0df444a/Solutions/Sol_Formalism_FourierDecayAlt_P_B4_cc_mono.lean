-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.cc_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:38:36.381994+00:00
-- url     : https://prove2.me/submissions/1516d483-24ae-4c88-8bdb-1acac3da3e35

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {F : Mat k r → E} {A c c' : ℝ} {m : ℕ} (h : CCle A m F c) (hc : c ≤ c') : CCle A m F c' := by
  unfold CCle at *
  exact ⟨h.1, fun u v hu hv hl g hg => (h.2 u v hu hv hl g hg).trans hc⟩
end Formalism.FourierDecayAlt.P.B4
