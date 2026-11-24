-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.integrand_slice_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:27.44988+00:00
-- url     : https://prove2.me/submissions/fc5a35e4-701b-494b-8fde-38463907f20d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_lam_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_integral_dilation_pair_integrand_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_vanishes_outside_interval

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
theorem _root_.solution (H : Hyp D Ξ α) (hJ : DilJac D) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂)
    (t : ℝ × ℝ) :
    (∫ p, weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t) ∂D.μSS) =
      ((D.χ t.1 * D.χ t.2 : ℝ) : ℂ) * ∫ p, fourierWeightedPhase D F F' w₁ w₂ p ∂D.μSS := by
  by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
  · have h1 : 0 < t.1 := lt_trans (by norm_num) ht.1.1
    have h2 : 0 < t.2 := lt_trans (by norm_num) ht.2.1
    have e : ∀ᵐ p ∂D.μSS, weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t) =
        ((D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ) : ℂ) * fourierWeightedPhase D F F' w₁ w₂ (dilation₂ t p) := by
      filter_upwards [ae_inSS D] with p hp
      obtain ⟨l1, l2⟩ := lam_dil H.dilN D hp h1 h2
      have l1' : lam k r D.z (Matrix.of (dilation₂ t p).1.2) = t.1 * lam k r D.z (Matrix.of p.1.2) := l1
      have l2' : lam k r D.z' (Matrix.of (dilation₂ t p).2.2) = t.2 * lam k r D.z' (Matrix.of p.2.2) := l2
      unfold weightedPhaseJointIntegrand fourierWeightedPhase
      rw [Bt_eq D F F' hp, l1', l2']
      unfold regBracket
      ring
    rw [integral_congr_ae e, integral_const_mul,
      integral_dilation_pair_integrand_eq H hJ (admissible_of_weighted hF) (admissible_of_weighted hF') h₁ h₂ h1 h2, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    have hpos : (t.1 * t.2) ^ kap k r ≠ 0 := by positivity
    field_simp
  · have hz : D.χ t.1 * D.χ t.2 = 0 := by
      by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
      · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h => ht ⟨h1, h⟩
        rw [cutoff_vanishes_outside_interval D h2, mul_zero]
      · rw [cutoff_vanishes_outside_interval D h1, zero_mul]
    have e : ∀ p, weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t) = 0 := fun p => by
      unfold weightedPhaseJointIntegrand
      rw [Bt_zero D F F' p ht, zero_mul]
    simp only [e, integral_zero, hz, Complex.ofReal_zero, zero_mul]
end Formalism.FourierDecayAlt.P.B6
