-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.lmulM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:37:04.559911+00:00
-- url     : https://prove2.me/submissions/0f83b80b-c005-4819-80a8-f28945da490e

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
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  first
    | (show Continuous fun x : Mt k r => (a * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
       exact continuous_const.matrix_mul continuous_id)
    | (unfold lmulM; fun_prop)
end Formalism.FourierDecayAlt.P.LongWeylElement
