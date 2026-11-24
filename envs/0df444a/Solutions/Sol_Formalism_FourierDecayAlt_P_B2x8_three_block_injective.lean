-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.three_block_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:55.655854+00:00
-- url     : https://prove2.me/submissions/2b76308c-644a-4a4b-b0a7-50f03c8405a4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_three_block_middle

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
theorem _root_.solution {a a' b b' : ℂ} {y y' : Fin (2 * r' + k + 1) → ℂ} (h : mk3 k r' a y b = mk3 k r' a' y' b') :
    a = a' ∧ y = y' ∧ b = b' := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg cF h; rwa [three_block_first, three_block_first] at this
  · have := congrArg mid h; rwa [three_block_middle, three_block_middle] at this
  · have := congrArg cL h; rwa [three_block_last, three_block_last] at this
end Formalism.FourierDecayAlt.P.B2x8
