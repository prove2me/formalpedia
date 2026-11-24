-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.mulM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:30:55.717868+00:00
-- url     : https://prove2.me/submissions/c3981553-870a-47fa-be19-7d17f85267ce

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement

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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  first
    | (show Continuous fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r)
       exact continuous_fst.matrix_mul continuous_snd)
    | (unfold mulM; fun_prop)
end Formalism.FourierDecayAlt.P.LongWeylElement
