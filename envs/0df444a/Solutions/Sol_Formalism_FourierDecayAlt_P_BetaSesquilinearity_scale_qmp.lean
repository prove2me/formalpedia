-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.scale_qmp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:37:17.751077+00:00
-- url     : https://prove2.me/submissions/bb31bab5-3048-4e36-a70d-890a31ad01d0

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Measure.QuasiMeasurePreserving (fun t : ℝ × ℝ => (a * t.1, b * t.2)) volume volume := by
  let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
    LinearEquiv.prodCongr (LinearEquiv.smulOfNeZero ℝ ℝ a ha) (LinearEquiv.smulOfNeZero ℝ ℝ b hb)
  have := Measure.LinearMap.quasiMeasurePreserving (volume : Measure (ℝ × ℝ)) (e : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (LinearEquiv.isUnit_det' e).ne_zero
  exact this
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
