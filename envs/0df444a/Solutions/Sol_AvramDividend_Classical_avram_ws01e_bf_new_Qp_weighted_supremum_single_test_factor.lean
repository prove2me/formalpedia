-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_Qp_weighted_supremum_single_test_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:16:26.416999+00:00
-- url     : https://prove2.me/submissions/f3a965f4-3152-40a1-9b78-8bb74c405b2f

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_strict_supremum_drawdown_laplace_threshold_factor
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_exp_supremum_strict_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_positive_supremum_tail_extend
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_upperray_weighted_exp_factor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Genuine tilted Qp factorisation for a single descending exponential test,
derived from upper-record threshold factorisation without full IndepFun. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p lam β : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q) (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p) (hβ : 0 < β)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    (let μ : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal
           (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ φ)))
     let S : Ω × ℝ → ℝ :=
       fun z => runningSup X (Real.toNNReal z.2) z.1
     let D : Ω × ℝ → ℝ :=
       fun z => S z - X.X (Real.toNNReal z.2) z.1
     (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) *
         ENNReal.ofReal (Real.exp (β * S z)) ∂μ) =
       (∫⁻ z, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) *
         (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) ∂μ)) := by
  let μ : Measure (Ω × ℝ) :=
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
  let S : Ω × ℝ → ℝ := fun z => runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z => S z - X.X (Real.toNNReal z.2) z.1
  let W : Ω × ℝ → ENNReal := fun z => ENNReal.ofReal (Real.exp (-β * D z))
  have hSMeas : Measurable S := (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hDMeas : Measurable D := (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  have hWMeas : Measurable W :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul hDMeas).exp)
  have hLaw : Measure.map S μ = expMeasure lam := by
    simpa [μ, S, hroot] using
      (esscher_positive_root_exp_clock_supremum_full_law_ws01d
        X φ q hφ hq hroot p hp lam hlam hlamroot)
  have hSpos : ∀ᵐ z ∂μ, 0 < S z :=
    avram_ws01e_bf_new_exp_supremum_strict_positive_ae μ S lam hlam hSMeas hLaw
  have hK : (∫⁻ z, W z ∂μ) ≠ ⊤ := by
    have hLap : (∫⁻ z, W z ∂μ) =
        ENNReal.ofReal (mgf (fun z : Ω × ℝ => -D z) μ β) := by
      simpa only [W, D, μ] using
        (avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
          X φ p hφ.le hp hJoint β hβ)
    rw [hLap]
    exact ENNReal.ofReal_ne_top
  have hPositiveTail : ∀ b : ℝ, 0 ≤ b →
      (μ.withDensity W) {z : Ω × ℝ | b < S z} =
        μ {z : Ω × ℝ | b < S z} * (∫⁻ z, W z ∂μ) := by
    intro b hb
    have hEvent : MeasurableSet {z : Ω × ℝ | b < S z} :=
      measurableSet_Ioi.preimage hSMeas
    rw [withDensity_apply W hEvent]
    simpa only [μ, S, D, W] using
      (avram_ws01e_b_actual_Qp_strict_supremum_drawdown_laplace_threshold_factor
        X φ p hφ.le hp hJoint b β hb hβ)
  have hAllTail := avram_ws01e_bf_new_positive_supremum_tail_extend
    μ S W hSpos hPositiveTail
  have hWeighted := avram_ws01e_bf_new_upperray_weighted_exp_factor
    μ S W β hSMeas hWMeas hβ hK hAllTail
  simpa only [μ, S, D, W] using hWeighted
