-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x7.conjM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:56:37.73125+00:00
-- url     : https://prove2.me/submissions/47773e54-7f78-40b6-a2f1-a83c31e25df2

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
theorem _root_.solution {k r : ℕ} (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact ((continuous_const (y := a)).matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const
end Formalism.FourierDecayAlt.P.B2x7
