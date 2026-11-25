-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.y_unfold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:20.312792+00:00
-- url     : https://prove2.me/submissions/06a1c16b-5864-4368-9a35-b8b477e8f302

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_jc_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_integrable_GM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_integral_GM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_lintegral_weighted_swap_ne_top_and_toReal_eq_integral
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_boundary_weight_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_y_H
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_y_norm_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_y_meas_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_y_good

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
attribute [local instance] sfNu
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hI : IntFormula D) (hC : ConjInv D)
    (hCC : CCIntegrable D A) (hCB : CoefBound D Ξ A) (hXi : XiInt D Ξ 2) : Unfold D A := by
  intro F hF
  have hc := jc_cont hF
  have hn := y_meas_n D hc
  constructor
  · have hm : Measurable fun a : (ℝ × ℝ) × ((Fin r → ℂ) × ℂ) =>
        ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') a.2 * ‖hsL (JM D F a.1 a.2)‖ ^ 2) :=
      (((measurable_bcWeight _ _).comp measurable_snd).mul hn).ennreal_ofReal
    have h2 := Measurable.lintegral_prod_right' (ν := (volume : Measure ((Fin r → ℂ) × ℂ))) hm
    simp_rw [y_norm_eq D F]
    exact h2.aemeasurable
  · intro w₁ w₂ h₁ h₂ p₁ p₂
    have hG := integrable_GM D Ξ A hCB hXi hF h₁ h₂
    have hH := y_H D hI hG
    have hWm : Measurable fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2 :=
      (h₁.1.continuous.measurable.comp measurable_fst).mul (h₂.1.continuous.measurable.comp measurable_snd)
    have fin := lintegral_weighted_swap_ne_top_and_toReal_eq_integral (ν := (volume : Measure (ℝ × ℝ))) (μ := (volume : Measure ((Fin r → ℂ) × ℂ)))
      (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2) hWm (fun τ => mul_nonneg (p₁ _) (p₂ _))
      (bcWeight k r (Tz k r D.z) (Tz k r D.z')) (measurable_bcWeight _ _) (boundary_weight_nonneg _ _)
      (fun τ q => ‖hsL (JM D F τ q)‖ ^ 2) hn (fun τ q => by positivity)
      (fun q => ∫ p, GM D F w₁ w₂ (PhiM D (q, p)) ∂D.μSS) hH.1 (y_good D hI hC hCC hF h₁ h₂)
    simp_rw [y_norm_eq D F]
    rw [← integral_GM D Ξ A hCB hXi hF h₁ h₂, ← hH.2]
    exact fin
end Formalism.FourierDecayAlt.P.B7
