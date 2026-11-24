-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.hs_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:04:56.103199+00:00
-- url     : https://prove2.me/submissions/8ab465d4-fb9e-4c9d-9576-f98c8429f8d8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_hsL_apply

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution {a b : ℝ → (Wq →L[ℂ] Wp)} {a' b' : Wq →L[ℂ] Wp} {x : ℝ} (ha : HasDerivAt a a' x)
    (hb : HasDerivAt b b' x) :
    HasDerivAt (fun t => hsInner (a t) (b t)) (hsInner a' (b x) + hsInner (a x) b') x := by
  have hA : HasDerivAt (fun t => hsVec (a t)) (hsVec a') x := by
    have := ((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x ha
    simpa [Function.comp_def, hsL_apply] using this
  have hB : HasDerivAt (fun t => hsVec (b t)) (hsVec b') x := by
    have := ((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hb
    simpa [Function.comp_def, hsL_apply] using this
  simpa only [hsInner] using HasDerivAt.inner ℂ hB hA
end Formalism.FourierDecayAlt.P.B5
