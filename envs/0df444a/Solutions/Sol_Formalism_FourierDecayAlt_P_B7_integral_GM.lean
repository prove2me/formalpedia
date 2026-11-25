-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.integral_GM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:50:31.212299+00:00
-- url     : https://prove2.me/submissions/aaf83c8e-50d3-41be-a322-1632b84d4fe7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_KM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_integrable_OmK

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    (hXi : XiInt D Ξ 2) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁)
    (h₂ : IsTest w₂) :
    (∫ x, GM D F w₁ w₂ x ∂D.μG) = ∫ p : SS k r, om w₁ (lam k r D.z (Matrix.of p.1.2)) *
          om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * Ph D F F p ∂D.μSS := by
  have h := integrable_OmK D Ξ A hCB hXi hF h₁ h₂
  have hs := h.swap
  have hswap := integral_integral_swap (μ := D.μG) (ν := D.μSS)
    (f := fun (x : Mt k r) (p : SS k r) => Om D w₁ w₂ p * KM D F p x) hs
  unfold GM
  rw [hswap]
  refine integral_congr_ae ?_
  filter_upwards [ae_inSS D] with p hp
  rw [integral_const_mul]
  unfold Om Ph
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_mem D.haarG] with x hx
  exact u_KM_eq D F hp hx
end Formalism.FourierDecayAlt.P.B7
