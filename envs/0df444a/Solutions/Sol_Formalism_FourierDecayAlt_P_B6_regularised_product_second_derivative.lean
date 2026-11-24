-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.regularised_product_second_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:48:02.53439+00:00
-- url     : https://prove2.me/submissions/2262db48-7875-4874-9f73-5462de58a9da

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_iterated_deriv_two_of_chain
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_contDiff_two_of_derivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_eventually_zero_outside
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_zero_outside
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_derivative_zero_outside
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gam_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_product_rule
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_cutoff_mul_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_nonpositive_not_in_interval

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
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {W : ℝ → ℝ} (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hWs : tsupport W ⊆ Set.Ioo (1 / 2) 2)
    (ρ : ℝ) {q0 q1 q2 : ℝ → ℂ}
    (h0 : ∀ t, 0 < t → HasDerivAt q0 (((-(ρ / t) : ℝ) : ℂ) * q1 t) t)
    (h1 : ∀ t, 0 < t → HasDerivAt q1 (((-(ρ / t) : ℝ) : ℂ) * q2 t) t)
    (hc : ContinuousOn q2 (Set.Ioi 0)) :
    ContDiff ℝ 2 (fun t => (W t : ℂ) * q0 t) ∧
    ∀ t, (W t : ℂ) * q0 t - iteratedDeriv 2 (fun t => (W t : ℂ) * q0 t) t =
      (gam ρ W 0 t : ℂ) * q0 t + (gam ρ W 1 t : ℂ) * q1 t + (gam ρ W 2 t : ℂ) * q2 t := by
  have hW2 : ContDiff ℝ 2 W := contDiff_infty.1 hW 2
  have dW : ∀ t, HasDerivAt W (deriv W t) t := fun t =>
    (hW2.differentiable (by norm_num) t).hasDerivAt
  have hdW1 : ContDiff ℝ 1 (deriv W) := by
    have : ContDiff ℝ (1 + 1) W := by simpa [one_add_one_eq_two] using hW2
    exact (contDiff_succ_iff_deriv.1 this).2.2
  have ddW : ∀ t, HasDerivAt (deriv W) (iteratedDeriv 2 W t) t := fun t => by
    have := (hdW1.differentiable (by norm_num) t).hasDerivAt
    rwa [iteratedDeriv_succ, iteratedDeriv_one]
  have evW : ∀ t, t ≤ 0 → W =ᶠ[𝓝 t] 0 := fun t ht => cutoff_eventually_zero_outside hWs (nonpositive_not_in_interval ht)
  have evdW : ∀ t, t ≤ 0 → deriv W =ᶠ[𝓝 t] 0 := fun t ht => by
    have := (evW t ht).deriv
    refine this.trans ?_
    exact Filter.Eventually.of_forall fun s => by simp
  have evu2 : ∀ t, t ≤ 0 → (fun t => -(ρ * (W t / t))) =ᶠ[𝓝 t] 0 := fun t ht => by
    filter_upwards [evW t ht] with s hs
    simp [hs]
  have du2 : ∀ t, HasDerivAt (fun t => -(ρ * (W t / t))) (-(ρ * (deriv W t / t - W t / t ^ 2))) t := fun t => by
    by_cases ht : t = 0
    · have e : -(ρ * (deriv W t / t - W t / t ^ 2)) = 0 := by
        simp [cutoff_zero_outside hWs (nonpositive_not_in_interval ht.le), cutoff_derivative_zero_outside hWs (nonpositive_not_in_interval ht.le)]
      rw [e]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (evu2 t ht.le)
    · have := (((dW t).div (hasDerivAt_id t) ht).const_mul ρ).neg
      refine HasDerivAt.congr_deriv (f := fun t => -(ρ * (W t / t))) this ?_
      simp only [id]
      field_simp
  have A : ∀ t, HasDerivAt (fun t => (W t : ℂ) * q0 t)
      (((deriv W t : ℝ) : ℂ) * q0 t + ((-(ρ * (W t / t)) : ℝ) : ℂ) * q1 t) t := fun t => by
    convert cutoff_product_rule dW evW h0 t using 1
    push_cast; ring
  have B : ∀ t, HasDerivAt (fun t => ((deriv W t : ℝ) : ℂ) * q0 t + ((-(ρ * (W t / t)) : ℝ) : ℂ) * q1 t)
      (((W t - gam ρ W 0 t : ℝ) : ℂ) * q0 t - (gam ρ W 1 t : ℂ) * q1 t - (gam ρ W 2 t : ℂ) * q2 t) t :=
    fun t => by
    refine ((cutoff_product_rule ddW evdW h0 t).add (cutoff_product_rule du2 evu2 h1 t)).congr_deriv ?_
    simp only [gam]; push_cast; ring
  have cq0 : ContinuousOn q0 (Set.Ioi 0) := fun t ht => (h0 t ht).continuousAt.continuousWithinAt
  have cq1 : ContinuousOn q1 (Set.Ioi 0) := fun t ht => (h1 t ht).continuousAt.continuousWithinAt
  have C : Continuous fun t => ((W t - gam ρ W 0 t : ℝ) : ℂ) * q0 t - (gam ρ W 1 t : ℂ) * q1 t -
      (gam ρ W 2 t : ℂ) * q2 t := by
    refine ((cutoff_mul_continuous (hW.continuous.sub (gam_continuous hW hWs ρ 0)) (fun t ht => ?_) cq0).sub
      (cutoff_mul_continuous (gam_continuous hW hWs ρ 1) (fun t ht => gam_zero hWs ρ 1 ht) cq1)).sub
      (cutoff_mul_continuous (gam_continuous hW hWs ρ 2) (fun t ht => gam_zero hWs ρ 2 ht) hc)
    show W t - gam ρ W 0 t = 0
    rw [cutoff_zero_outside hWs ht, gam_zero hWs ρ 0 ht, sub_zero]
  refine ⟨contDiff_two_of_derivatives A B C, fun t => ?_⟩
  rw [iterated_deriv_two_of_chain A B]
  push_cast; ring
end Formalism.FourierDecayAlt.P.B6
