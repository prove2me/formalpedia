-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.smooth_iterated_left_right_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:18:21.341377+00:00
-- url     : https://prove2.me/submissions/bd2f7cf6-2897-4f96-9f50-238c7bd98519

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_smooth_on_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_smooth_iterated_right_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_smooth_iterated_left_derivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {n i j : ℕ} {f : Mat k r → E} (h : CkOn ((4 : ℕ) : ℕ∞) (GV k r) f) (hn : n + i + j ≤ 4) :
    CkOn (n : ℕ∞) (GV k r) (Ll^[i] (Rr^[j] f)) :=
  smooth_iterated_left_derivative i (smooth_iterated_right_derivative j (smooth_on_mono (by exact_mod_cast hn) h))
end Formalism.FourierDecayAlt.P.B6
