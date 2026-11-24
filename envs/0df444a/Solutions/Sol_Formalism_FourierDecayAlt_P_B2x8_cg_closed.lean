-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.cg_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:04:53.296858+00:00
-- url     : https://prove2.me/submissions/6bc0dc47-4781-454b-b7eb-8a24093aaa69

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (R : ℝ) : IsClosed (cgS k r' R) := by
  show IsClosed ({p : ℂ × HPar k r' | ‖p.1‖ ≤ R} ∩ ({p | ‖p.2.1‖ ≤ R} ∩ {p | |p.2.2| ≤ R * ‖p.1‖}))
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_) <;> exact isClosed_le (by fun_prop) (by fun_prop)
end Formalism.FourierDecayAlt.P.B2x8
