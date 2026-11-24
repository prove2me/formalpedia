-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.hs_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:04:55.257538+00:00
-- url     : https://prove2.me/submissions/1cf19133-c083-4d16-b2c0-80f57b0f7327

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
theorem _root_.solution {a b : ℝ → (Wq →L[ℂ] Wp)} (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (fun t => hsInner (a t) (b t)) := by
  have hA : ContDiff ℝ 1 (fun t => hsVec (a t)) := by
    simpa [Function.comp_def, hsL_apply] using
      ((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).contDiff.comp ha
  have hB : ContDiff ℝ 1 (fun t => hsVec (b t)) := by
    simpa [Function.comp_def, hsL_apply] using
      ((hsL (Wp := Wp) (Wq := Wq)).restrictScalars ℝ).contDiff.comp hb
  simpa only [hsInner] using hB.inner ℂ hA
end Formalism.FourierDecayAlt.P.B5
