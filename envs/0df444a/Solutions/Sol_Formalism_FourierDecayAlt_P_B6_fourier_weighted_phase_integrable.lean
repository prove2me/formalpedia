-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.fourier_weighted_phase_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:45:12.076533+00:00
-- url     : https://prove2.me/submissions/c6d5e94a-a1d2-45a5-bc40-5f1652be8469

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_XX_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_xi_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_fourier_transform_quadratic_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aestronglyMeasurable_dilation_pair_integrand

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : admitted α c F)
    (hF' : admitted α c' F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fourierWeightedPhase D F F' w₁ w₂) D.μSS := by
  obtain ⟨C₁, hC₁, d₁⟩ := fourier_transform_quadratic_decay h₁
  obtain ⟨C₂, hC₂, d₂⟩ := fourier_transform_quadratic_decay h₂
  obtain ⟨K, hK, hb⟩ := ph_bound H
  have hc := admissible_constant_nonneg hF
  have hc' := admissible_constant_nonneg hF'
  refine Integrable.mono' ((xi_integrable H).const_mul (C₁ * C₂ * (K * c * c'))) (aestronglyMeasurable_dilation_pair_integrand H hF hF' h₁ h₂) ?_
  filter_upwards [ae_inSS D] with p hp
  unfold fourierWeightedPhase
  rw [norm_mul, norm_mul]
  have e1 := d₁ (lam k r D.z (Matrix.of p.1.2))
  have e2 := d₂ (-lam k r D.z' (Matrix.of p.2.2))
  rw [abs_neg] at e2
  have e3 := hb F F' c c' hF hF' p hp
  have hX := XX_nonneg Ξ p
  calc ‖om w₁ (lam k r D.z (Matrix.of p.1.2))‖ * ‖om w₂ (-lam k r D.z' (Matrix.of p.2.2))‖ * ‖Ph D F F' p‖
      ≤ (C₁ * (1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-2 : ℝ)) *
          (C₂ * (1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-2 : ℝ)) * (K * c * c' * XX Ξ p) := by
        gcongr
    _ = C₁ * C₂ * (K * c * c') * (XX Ξ p * LL D p) := by unfold LL; ring
end Formalism.FourierDecayAlt.P.B6
