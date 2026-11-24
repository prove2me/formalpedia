-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.norm_hilbertSchmidt_inner_contraction_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:27:52.155868+00:00
-- url     : https://prove2.me/submissions/a04d8d5a-a759-4631-b34a-752a01814456

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_norm_le

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (hL : ∀ T, ‖L T‖ ≤ ‖T‖) {a b : Wq →L[ℂ] Wp}
    {C t : ℝ} (ha : ‖a‖ ≤ C * t) (hb : ‖b‖ ≤ C * t) :
    ‖hsInner (L a) b‖ ≤ (Module.finrank ℂ Wq : ℝ) * C ^ 2 * (t * t) := by
  have hd0 : (0 : ℝ) ≤ (Module.finrank ℂ Wq : ℝ) := by positivity
  have h0 : 0 ≤ C * t := le_trans (norm_nonneg _) ha
  calc ‖hsInner (L a) b‖ ≤ (Module.finrank ℂ Wq : ℝ) * ‖L a‖ * ‖b‖ := hsInner_norm_le _ _
    _ ≤ (Module.finrank ℂ Wq : ℝ) * (C * t) * (C * t) := by
        have h1 : ‖L a‖ ≤ C * t := le_trans (hL a) ha
        have : (Module.finrank ℂ Wq : ℝ) * ‖L a‖ ≤ (Module.finrank ℂ Wq : ℝ) * (C * t) :=
          mul_le_mul_of_nonneg_left h1 hd0
        exact mul_le_mul this hb (norm_nonneg _) (mul_nonneg hd0 h0)
    _ = (Module.finrank ℂ Wq : ℝ) * C ^ 2 * (t * t) := by ring
end Formalism.FourierDecayAlt.P.B6
