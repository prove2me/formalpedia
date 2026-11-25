-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.locally_bounded_betaInfTau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:35:21.309715+00:00
-- url     : https://prove2.me/submissions/1e1eaa62-c1a4-4790-a542-4583d66d2ea4

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_weighted_of_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_XX_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_xi_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_betaInfTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Gt_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_weight_dominated_near_quadrant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_half_quadrant_neighbourhood

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
theorem _root_.solution (H : Hyp D Ξ α) {τ₀ : ℝ × ℝ} (h₀ : τ₀ ∈ Quad) :
    ∃ C : ℝ, ∃ U ∈ 𝓝 τ₀, ∀ τ ∈ U, ∀ (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ),
      CCle α 4 F c → CCle α 4 F' c' → ‖betaInfTau D τ F F'‖ ≤ C * c * c' := by
  obtain ⟨K, hK, hb⟩ := Gt_bound H
  obtain ⟨M, hM, hw⟩ := weight_dominated_near_quadrant D h₀
  refine ⟨M * K * ∫ p, XX Ξ p * LL D p ∂D.μSS, _, half_quadrant_neighbourhood h₀, ?_⟩
  intro τ hτ F F' c c' hcF hcF'
  have hF := admissible_weighted_of_bound hcF
  have hF' := admissible_weighted_of_bound hcF'
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  rw [betaInfTau_eq H hF hF' τ]
  have key : ‖∫ p, Gt D F F' τ p ∂D.μSS‖ ≤ ∫ p, M * (K * c * c') * (XX Ξ p * LL D p) ∂D.μSS := by
    apply norm_integral_le_of_norm_le ((xi_integrable H).const_mul (M * (K * c * c')))
    refine Filter.Eventually.of_forall fun p => ?_
    have hX := XX_nonneg Ξ p
    calc ‖Gt D F F' τ p‖ ≤ wt D τ p * (K * c * c' * XX Ξ p) := hb F F' c c' hF hF' τ p
      _ ≤ (M * LL D p) * (K * c * c' * XX Ξ p) := by
          apply mul_le_mul_of_nonneg_right (hw τ hτ.1 hτ.2 p)
          positivity
      _ = M * (K * c * c') * (XX Ξ p * LL D p) := by ring
  refine key.trans (le_of_eq ?_)
  rw [integral_const_mul]
  ring
end Formalism.FourierDecayAlt.P.B6
