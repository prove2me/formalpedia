-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.betaInfTau_additive_of_pairing_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:50.326151+00:00
-- url     : https://prove2.me/submissions/d0b5fdff-905a-4569-9ead-3ff33f62407e

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_oneMinusDD_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_E_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_E_reg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Et_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_betaInfTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_pairing_kernel_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_integrable_pairing_times_phase_exp
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_regularized_bracket_additive

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
theorem _root_.solution (H : Hyp D Ξ α) {X Y X₁ Y₁ X₂ Y₂ : Mat k r → (Wq →L[ℂ] Wp)} {c₁ c₁' c₂ c₂' : ℝ}
    (hX₁ : AdmW α c₁ 2 2 X₁) (hY₁ : AdmW α c₁' 2 2 Y₁) (hX₂ : AdmW α c₂ 2 2 X₂) (hY₂ : AdmW α c₂' 2 2 Y₂)
    (h : ∀ q, D.inSS q → Ph D X Y q = Ph D X₁ Y₁ q + Ph D X₂ Y₂ q) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) :
    betaInfTau D τ X Y = betaInfTau D τ X₁ Y₁ + betaInfTau D τ X₂ Y₂ := by
  rw [betaInfTau_eq H hX₁ hY₁ τ, betaInfTau_eq H hX₂ hY₂ τ,
    ← integral_add (pairing_kernel_integrable H hX₁ hY₁ hτ) (pairing_kernel_integrable H hX₂ hY₂ hτ)]
  unfold betaInfTau
  apply integral_congr_ae
  filter_upwards [ae_inSS D] with p hp
  have e : ∀ t : ℝ × ℝ, oneMinusDD (regBracket D X Y p) t.1 t.2 = Et D X₁ Y₁ (p, t) + Et D X₂ Y₂ (p, t) := by
    intro t
    rw [regularized_bracket_additive H h hp, oneMinusDD_add (E_reg H hX₁ hY₁ hp).1 (E_reg H hX₂ hY₂ hp).1
      (E_reg H hX₁ hY₁ hp).2 (E_reg H hX₂ hY₂ hp).2, E_formula H hX₁ hY₁ hp t, E_formula H hX₂ hY₂ hp t,
      Et_eq D X₁ Y₁ hp t, Et_eq D X₂ Y₂ hp t]
  simp only [e]
  unfold Gt
  rw [← mul_add, ← integral_add (integrable_pairing_times_phase_exp H hX₁ hY₁ τ p) (integrable_pairing_times_phase_exp H hX₂ hY₂ τ p)]
  simp only [add_mul]
  rfl
end Formalism.FourierDecayAlt.P.B6
