-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.cv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:27:48.826799+00:00
-- url     : https://prove2.me/submissions/252089bc-85df-48af-95cc-a1ddab59d959

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
theorem _root_.solution (b : Bool) (X g : Mat k r) (s t : ℝ) : cv b X (s + t) g = cv b X t (cv b X s g) := by
  cases b
  · simp only [cv]
    rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)]
    congr 2
    push_cast
    rw [add_smul]
  · simp only [cv]
    rw [← Matrix.mul_assoc,
      ← Matrix.exp_add_of_commute _ _ ((((Commute.refl X).smul_left _).smul_right _).neg_left.neg_right)]
    congr 2
    push_cast
    rw [add_smul, neg_add, add_comm]
end Formalism.FourierDecayAlt.P.B4
