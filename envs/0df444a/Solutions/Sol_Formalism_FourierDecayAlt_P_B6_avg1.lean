-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.avg1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:29.625912+00:00
-- url     : https://prove2.me/submissions/27197a30-6306-472f-bc79-cc289b3a0bc8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_sigmaFinite__SS_1f0045a81b6a
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_betaInfTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_joint_weighted_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_tau_integral_fourier_form

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
    (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * betaInfTau D τ F F') =
      ∫ p : SS k r, (∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 *
        (om w₁ (t.1 * lam k r D.z (Matrix.of p.1.2)) * om w₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2))))) ∂D.μSS := by
  have := sigmaFinite_μSS D
  simp_rw [betaInfTau_eq H hF hF', ← integral_const_mul]
  rw [integral_integral_swap (joint_weighted_integrable H hF hF' h₁ h₂)]
  apply integral_congr_ae
  filter_upwards [ae_inSS D] with p hp
  rw [tau_integral_fourier_form H hF hF' h₁ h₂ p]
  simp_rw [Bt_eq D F F' hp]
end Formalism.FourierDecayAlt.P.B6
