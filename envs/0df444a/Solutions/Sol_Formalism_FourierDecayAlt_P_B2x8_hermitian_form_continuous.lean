-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.hermitian_form_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:55.039101+00:00
-- url     : https://prove2.me/submissions/4b1dcb03-b5b0-402b-a273-4e0bd1c2ca80

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
theorem _root_.solution {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) :
    Continuous fun p : (ι → ℂ) × (ι → ℂ) => herm H p.1 p.2 := by
  unfold herm
  exact (continuous_star.comp continuous_snd).dotProduct (continuous_const.matrix_mulVec continuous_fst)
end Formalism.FourierDecayAlt.P.B2x8
