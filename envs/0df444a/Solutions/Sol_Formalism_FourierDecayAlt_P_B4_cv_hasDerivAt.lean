-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.cv_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:32:23.508949+00:00
-- url     : https://prove2.me/submissions/db35326b-47b9-4548-afe0-15a06ec6ccbd

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero


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
theorem _root_.solution (b : Bool) (X g : Mat k r) :
    HasDerivAt (fun t : ℝ => cv b X t g) (vf b X g) 0 := by
  cases b
  · exact hasDerivAt_mul_exp_smul_zero g X
  · have h := hasDerivAt_mul_exp_smul_zero (1 : Mat k r) (-X)
    have h2 := (mulR g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    · show (1 * -X) * g = -(X * g)
      simp
    · show NormedSpace.exp (-((t : ℂ) • X)) * g = (1 * NormedSpace.exp ((t : ℂ) • -X)) * g
      simp
end Formalism.FourierDecayAlt.P.B4
