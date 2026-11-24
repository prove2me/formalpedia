-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.conjM_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:03:25.144746+00:00
-- url     : https://prove2.me/submissions/f56b4e7c-5702-47d4-bc14-b8dd4d4b64e1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open B2x7
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x7
theorem _root_.solution (k r : ℕ) : (conjM (1 : Mat k r) : Mt k r → Mt k r) = id := by
  funext x
  unfold conjM
  rw [inv_one, Matrix.mul_one, Matrix.one_mul]
  rfl
end Formalism.FourierDecayAlt.P.B2x7
