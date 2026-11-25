-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.joint_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:55:28.711844+00:00
-- url     : https://prove2.me/submissions/48f5355c-d4d4-4b18-88ae-660537123b97

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_LL_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_wt_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_xi_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Gt_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Gt_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exists_bound_isTest_support
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_product_test_integrable

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
    (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun x : (ℝ × ℝ) × SS k r => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) * Gt D F F' x.1 x.2)
      ((volume : Measure (ℝ × ℝ)).prod D.μSS) := by
  have := sigmaFinite_μSS D
  obtain ⟨K, hK0, hK⟩ := Gt_bound H
  obtain ⟨M₁, hM₁0, hM₁⟩ := exists_bound_isTest_support h₁
  obtain ⟨M₂, hM₂0, hM₂⟩ := exists_bound_isTest_support h₂
  have hc : 0 ≤ c := admissible_constant_nonneg (admissible_of_weighted hF)
  have hc' : 0 ≤ c' := admissible_constant_nonneg (admissible_of_weighted hF')
  have hb : Integrable (fun x : (ℝ × ℝ) × SS k r => (|w₁ x.1.1| * |w₂ x.1.2|) *
      ((4 * M₁ * M₂ * (K * c * c')) * (XX Ξ x.2 * LL D x.2))) ((volume : Measure (ℝ × ℝ)).prod D.μSS) :=
    Integrable.mul_prod (f := fun τ : ℝ × ℝ => |w₁ τ.1| * |w₂ τ.2|)
      (g := fun p : SS k r => (4 * M₁ * M₂ * (K * c * c')) * (XX Ξ p * LL D p))
      (product_test_integrable h₁ h₂) ((xi_integrable H).const_mul _)
  have hmeas : AEStronglyMeasurable
      (fun x : (ℝ × ℝ) × SS k r => ((w₁ x.1.1 * w₂ x.1.2 : ℝ) : ℂ) * Gt D F F' x.1 x.2)
      ((volume : Measure (ℝ × ℝ)).prod D.μSS) := by
    apply AEStronglyMeasurable.mul _ (Gt_measurable H hF hF').aestronglyMeasurable
    have h1c := h₁.1.continuous
    have h2c := h₂.1.continuous
    exact ((by fun_prop : Continuous fun τ : ℝ × ℝ =>
      ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)).stronglyMeasurable.comp_measurable measurable_fst).aestronglyMeasurable
  refine hb.mono' hmeas (ae_of_all _ fun x => ?_)
  have hXX := XX_nonneg Ξ x.2
  have hLL := LL_nonneg D x.2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  by_cases ha : w₁ x.1.1 = 0
  · rw [ha]; simp
  by_cases hb' : w₂ x.1.2 = 0
  · rw [hb']; simp
  obtain ⟨p1, q1⟩ := hM₁ _ ha
  obtain ⟨p2, q2⟩ := hM₂ _ hb'
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hB : 0 ≤ K * c * c' * XX Ξ x.2 := by positivity
  calc ‖Gt D F F' x.1 x.2‖ ≤ wt D x.1 x.2 * (K * c * c' * XX Ξ x.2) := hK F F' c c' hF hF' x.1 x.2
    _ ≤ (4 * max 1 (x.1.1 ^ 2)⁻¹ * max 1 (x.1.2 ^ 2)⁻¹ * LL D x.2) * (K * c * c' * XX Ξ x.2) :=
        mul_le_mul_of_nonneg_right (wt_le D p1 p2 x.2) hB
    _ ≤ (4 * M₁ * M₂ * LL D x.2) * (K * c * c' * XX Ξ x.2) := by
        apply mul_le_mul_of_nonneg_right _ hB
        apply mul_le_mul_of_nonneg_right _ hLL
        have : (0:ℝ) ≤ max 1 (x.1.2 ^ 2)⁻¹ := le_trans zero_le_one (le_max_left _ _)
        calc 4 * max 1 (x.1.1 ^ 2)⁻¹ * max 1 (x.1.2 ^ 2)⁻¹ ≤ 4 * M₁ * max 1 (x.1.2 ^ 2)⁻¹ := by
              apply mul_le_mul_of_nonneg_right _ this
              linarith
          _ ≤ 4 * M₁ * M₂ := by
              apply mul_le_mul_of_nonneg_left q2 (by positivity)
    _ = 4 * M₁ * M₂ * (K * c * c') * (XX Ξ x.2 * LL D x.2) := by ring
end Formalism.FourierDecayAlt.P.B6
