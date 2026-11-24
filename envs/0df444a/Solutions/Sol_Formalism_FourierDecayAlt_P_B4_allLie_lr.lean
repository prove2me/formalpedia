-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.allLie_lr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:30:23.952371+00:00
-- url     : https://prove2.me/submissions/08259487-49b9-47b6-a990-04dcf424e5ab

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
theorem _root_.solution {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    AllLie (lr u v) := by
  unfold AllLie
  intro x hx
  simp only [lr, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact (hu X hX).1
  · exact (hv X hX).1
end Formalism.FourierDecayAlt.P.B4
