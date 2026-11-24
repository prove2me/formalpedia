-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.pairing_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:17:58.169795+00:00
-- url     : https://prove2.me/submissions/0393bc63-b544-47c3-9b27-4738157a3317

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_XX_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_xi_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Gt_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_weight_dominated_near_quadrant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aestronglyMeasurable_beta_integrand

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
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') {τ : ℝ × ℝ} (hτ : τ ∈ Quad) : Integrable (Gt D F F' τ) D.μSS := by
  obtain ⟨K, hK, hb⟩ := Gt_bound H
  obtain ⟨M, hM, hw⟩ := weight_dominated_near_quadrant D hτ
  have a1 : 0 < τ.1 := hτ.1
  have a2 : 0 < τ.2 := hτ.2
  refine Integrable.mono' ((xi_integrable H).const_mul (M * (K * c * c'))) (aestronglyMeasurable_beta_integrand H hF hF' τ) ?_
  refine Filter.Eventually.of_forall fun p => ?_
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hX := XX_nonneg Ξ p
  calc ‖Gt D F F' τ p‖ ≤ wt D τ p * (K * c * c' * XX Ξ p) := hb F F' c c' hF hF' τ p
    _ ≤ (M * LL D p) * (K * c * c' * XX Ξ p) := by
        apply mul_le_mul_of_nonneg_right (hw τ (by linarith) (by linarith) p)
        positivity
    _ = M * (K * c * c') * (XX Ξ p * LL D p) := by ring
end Formalism.FourierDecayAlt.P.B6
