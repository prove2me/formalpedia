-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.translated_product_integrable_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:23.881998+00:00
-- url     : https://prove2.me/submissions/889a0b4c-1609-4385-b13b-0b5c2ac69fb2

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_two_sided_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_ae_strongly_measurable
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv


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
theorem _root_.solution (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
    admitted α cA A → admitted α cB B → ∀ x ∈ GV k r, ∀ y ∈ GV k r,
      Integrable (fun g : Mt k r => ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖) D.μG ∧
      (∫ g : Mt k r, ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖ ∂D.μG) ≤
        K * cA * cB * ((Ξ x : ℝ) * (Ξ y : ℝ)) := by
  obtain ⟨C, hC⟩ := H.coef
  refine ⟨max C 0, le_max_right _ _, fun A B cA cB hA hB x hx y hy => ?_⟩
  have hcA := admissible_constant_nonneg hA
  have hcB := admissible_constant_nonneg hB
  have hL := hC A B cA cB (admissible_ae_strongly_measurable hA D.haarG) (admissible_ae_strongly_measurable hB D.haarG) hA.2 hB.2 x hx y hy
  have hAt : AEStronglyMeasurable (fun g : Mt k r => A (x⁻¹ * Matrix.of g * y)) D.μG :=
    admissible_ae_strongly_measurable (admissible_two_sided_translate H.α_nonneg hA (WeylGroupFacts.uh_inv hx) hy) D.haarG
  have hm : AEStronglyMeasurable (fun g : Mt k r => ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖) D.μG :=
    hAt.norm.mul (admissible_ae_strongly_measurable hB D.haarG).norm
  have he : ∀ g : Mt k r, ENNReal.ofReal (‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖) =
      ‖A (x⁻¹ * Matrix.of g * y)‖ₑ * ‖B (Matrix.of g)‖ₑ := fun g => by
    rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  have hfin : ENNReal.ofReal (C * cA * cB) * (Ξ x : ℝ≥0∞) * (Ξ y : ℝ≥0∞) < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top) ENNReal.coe_lt_top
  have hnn : ∀ g : Mt k r, 0 ≤ ‖A (x⁻¹ * Matrix.of g * y)‖ * ‖B (Matrix.of g)‖ := fun g => by positivity
  constructor
  · refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)]
    simp only [he]
    exact lt_of_le_of_lt hL hfin
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hm]
    simp only [he]
    refine (ENNReal.toReal_mono hfin.ne hL).trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal, mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [ENNReal.toReal_ofReal']
    refine max_le ?_ (by positivity)
    have : C ≤ max C 0 := le_max_left _ _
    gcongr
end Formalism.FourierDecayAlt.P.B6
