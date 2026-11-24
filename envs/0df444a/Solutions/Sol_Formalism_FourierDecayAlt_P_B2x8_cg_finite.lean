-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.cg_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:23.624042+00:00
-- url     : https://prove2.me/submissions/f9340a89-0174-416d-a39e-0411618c63ae

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_lintegral_inv_norm_lt_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cg_closed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (R : ℝ) (hR : 0 ≤ R) : (μx.prod (volume : Measure (HPar k r'))) (cgS k r' R) < ∞ := by
  rw [Measure.prod_apply (cg_closed R).measurableSet]
  set V : ℝ≥0∞ := volume (Metric.closedBall (0 : Fin (2 * r' + k + 1) → ℂ) R) with hV
  have hVfin : V < ∞ := measure_closedBall_lt_top
  have hslice : ∀ c : ℂ, (volume : Measure (HPar k r')) (Prod.mk c ⁻¹' cgS k r' R) ≤
      (Metric.closedBall (0 : ℂ) R).indicator (fun c => V * ENNReal.ofReal (2 * R * ‖c‖)) c := by
    intro c
    by_cases hc : ‖c‖ ≤ R
    · rw [Set.indicator_of_mem (by simpa using hc)]
      have : Prod.mk c ⁻¹' cgS k r' R ⊆
          Metric.closedBall (0 : Fin (2 * r' + k + 1) → ℂ) R ×ˢ Set.Icc (-(R * ‖c‖)) (R * ‖c‖) := by
        rintro q ⟨_, h2, h3⟩
        exact ⟨by simpa using h2, abs_le.1 h3⟩
      refine (measure_mono this).trans ?_
      rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
      apply le_of_eq; congr 2; ring
    · have : Prod.mk c ⁻¹' cgS k r' R = ∅ := by
        ext q; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, _⟩; exact hc h1
      rw [this]; simp
  refine (lintegral_mono hslice).trans_lt ?_
  have hmeas : Measurable ((Metric.closedBall (0 : ℂ) R).indicator (fun c => V * ENNReal.ofReal (2 * R * ‖c‖))) := by
    refine Measurable.indicator ?_ Metric.isClosed_closedBall.measurableSet
    fun_prop
  unfold μx
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hmeas]
  have hpt : ∀ c : ℂ, ((fun c : ℂ => ENNReal.ofReal ((‖c‖ ^ 2)⁻¹)) *
      (Metric.closedBall (0 : ℂ) R).indicator (fun c => V * ENNReal.ofReal (2 * R * ‖c‖))) c =
      (Metric.closedBall (0 : ℂ) R).indicator (fun c => (V * ENNReal.ofReal (2 * R)) * ENNReal.ofReal (‖c‖⁻¹)) c := by
    intro c
    rw [Pi.mul_apply]
    by_cases hc : c ∈ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc]
      have e : (‖c‖ ^ 2)⁻¹ * (2 * R * ‖c‖) = 2 * R * ‖c‖⁻¹ := by
        by_cases h0 : ‖c‖ = 0
        · simp [h0]
        · field_simp
      have a : ENNReal.ofReal ((‖c‖ ^ 2)⁻¹) * ENNReal.ofReal (2 * R * ‖c‖) =
          ENNReal.ofReal (2 * R) * ENNReal.ofReal (‖c‖⁻¹) := by
        rw [← ENNReal.ofReal_mul (by positivity), e, ENNReal.ofReal_mul (by positivity)]
      rw [mul_left_comm, a, mul_assoc]
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc, mul_zero]
  rw [lintegral_congr hpt, lintegral_indicator Metric.isClosed_closedBall.measurableSet,
    lintegral_const_mul' _ _ (ENNReal.mul_lt_top hVfin ENNReal.ofReal_lt_top).ne]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hVfin ENNReal.ofReal_lt_top) (lintegral_inv_norm_lt_top R)
end Formalism.FourierDecayAlt.P.B2x8
