-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.second_integrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:36.651903+00:00
-- url     : https://prove2.me/submissions/d9d77279-9d38-4d90-9f6c-399fd4ac8764

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_sigmaFinite__SS_1f0045a81b6a
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_XX_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_xi_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_test_function_fourier_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_fourier_transform_quadratic_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_scaled_decay_weight_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_first_eigenvalue_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_lambda_second_coordinate

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (weightedPhaseJointIntegrand D F F' w₁ w₂) (D.μSS.prod volume) := by
  have := sigmaFinite_μSS D
  obtain ⟨C₁, hC₁, d₁⟩ := fourier_transform_quadratic_decay h₁
  obtain ⟨C₂, hC₂, d₂⟩ := fourier_transform_quadratic_decay h₂
  obtain ⟨K, hK, hb⟩ := Bt_bound H
  have hc := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hbox : Integrable (Set.indicator (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) (fun _ : ℝ × ℝ => (1 : ℝ))) :=
    (continuousOn_const.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  have hdom := ((xi_integrable H).const_mul (16 * (C₁ * C₂) * (K * c * c'))).mul_prod hbox
  have hmeas : AEStronglyMeasurable (weightedPhaseJointIntegrand D F F' w₁ w₂) (D.μSS.prod volume) := by
    unfold weightedPhaseJointIntegrand
    refine ((Bt_measurable H hF hF').mul (Continuous.stronglyMeasurable ?_)).aestronglyMeasurable
    exact ((test_function_fourier_continuous h₁).comp ((continuous_fst.comp continuous_snd).mul
        ((first_eigenvalue_continuous D).comp continuous_fst))).mul
      ((test_function_fourier_continuous h₂).comp ((continuous_snd.comp continuous_snd).mul
        ((continuous_lambda_second_coordinate D).comp continuous_fst)).neg)
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨p, t⟩ := q
  have hX := XX_nonneg Ξ p
  by_cases ht : t ∈ Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2
  · simp only [Set.indicator_of_mem ht, mul_one]
    unfold weightedPhaseJointIntegrand
    rw [norm_mul, norm_mul]
    have e1 := (d₁ (t.1 * lam k r D.z (Matrix.of p.1.2))).trans
      (mul_le_mul_of_nonneg_left (scaled_decay_weight_bound ht.1.1 _) hC₁)
    have e2 := d₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2)))
    rw [abs_neg] at e2
    have e2' := e2.trans (mul_le_mul_of_nonneg_left (scaled_decay_weight_bound ht.2.1 _) hC₂)
    have e3 := hb F F' c c' hF hF' p t
    calc ‖Bt D F F' (p, t)‖ * (‖om w₁ (t.1 * lam k r D.z (Matrix.of p.1.2))‖ *
          ‖om w₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2)))‖)
        ≤ (K * c * c' * XX Ξ p) * ((C₁ * (4 * (1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-2 : ℝ))) *
            (C₂ * (4 * (1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-2 : ℝ)))) := by
          gcongr
      _ = 16 * (C₁ * C₂) * (K * c * c') * (XX Ξ p * LL D p) := by unfold LL; ring
  · have ht' : t ∉ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2 := fun h =>
      ht ⟨Set.Ioo_subset_Icc_self h.1, Set.Ioo_subset_Icc_self h.2⟩
    simp only [Set.indicator_of_notMem ht, mul_zero]
    unfold weightedPhaseJointIntegrand
    rw [Bt_zero D F F' p ht', zero_mul, norm_zero]
end Formalism.FourierDecayAlt.P.B6
