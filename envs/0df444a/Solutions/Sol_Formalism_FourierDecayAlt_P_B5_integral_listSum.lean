-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.integral_listSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:06:03.547002+00:00
-- url     : https://prove2.me/submissions/efa07159-0aee-485f-b584-033c4213fb44

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase

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
theorem _root_.solution {ι α : Type*} [MeasurableSpace α] (μ : Measure α) (l : List ι) (φ : ι → α → ℂ)
    (h : ∀ T ∈ l, Integrable (φ T) μ) :
    Integrable (fun g => (l.map fun T => φ T g).sum) μ ∧
      (∫ g, (l.map fun T => φ T g).sum ∂μ) = (l.map fun T => ∫ g, φ T g ∂μ).sum := by
  induction l with
  | nil => simp
  | cons T l ih =>
    have hT := h T (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun T' hT' => h T' (by simp [hT']))
    simp only [List.map_cons, List.sum_cons]
    exact ⟨hT.add ih1, by rw [integral_add hT ih1, ih2]⟩
end Formalism.FourierDecayAlt.P.B5
