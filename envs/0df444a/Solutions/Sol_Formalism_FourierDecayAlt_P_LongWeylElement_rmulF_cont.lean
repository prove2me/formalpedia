-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.rmulF_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:10.082972+00:00
-- url     : https://prove2.me/submissions/eaf889e8-2b15-4c3c-b951-af83039eccba

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
theorem _root_.solution {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulF a) := by
  first
    | (show Continuous fun x : Fin n → Fin n → ℂ => (Matrix.of x * a : Matrix (Fin n) (Fin n) ℂ)
       exact continuous_id.matrix_mul continuous_const)
    | (unfold rmulF; fun_prop)
end Formalism.FourierDecayAlt.P.LongWeylElement
