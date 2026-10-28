-- Prove2me | solution 1 for AvramDividend.Classical.chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:28:01.899394+00:00
-- url     : https://prove2.me/submissions/f4859f6c-21ee-4872-8ad3-40e2d5352638

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exp_clock_exponential_eigenfunction_action_ws01a

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact genuine independent-exponential-clock terminal moment, in a
rate-weighted form that remains valid for any sign of the Levy exponent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r)
    (θ : ℝ) (hθ : 0 ≤ θ) (hgap : X.ψ θ < r) (x : ℝ) :
    ENNReal.ofReal (r - X.ψ θ) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (θ * (x + X.X (Real.toNNReal z.2) z.1)))
        ∂(P.prod (ProbabilityTheory.expMeasure r))) =
    ENNReal.ofReal r * ENNReal.ofReal (Real.exp (θ * x)) := by
  let a : ℝ := X.ψ θ
  have hp : 0 < r - a := sub_pos.mpr hgap
  have hpdfR : Measurable (ProbabilityTheory.exponentialPDF r) :=
    (ProbabilityTheory.measurable_exponentialPDFReal r).ennreal_ofReal
  have hpdfP : Measurable (ProbabilityTheory.exponentialPDF (r - a)) :=
    (ProbabilityTheory.measurable_exponentialPDFReal (r - a)).ennreal_ofReal
  have hRealT : Measurable (fun t : ℝ => (Real.toNNReal t : ℝ)) :=
    measurable_coe_nnreal_real.comp measurable_real_toNNReal
  have hExpT : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (hRealT.mul measurable_const))
  have hWeight : Measurable (fun t : ℝ =>
      ProbabilityTheory.exponentialPDF r t *
        ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a))) :=
    hpdfR.mul hExpT
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (r - a)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  have hMass :
      (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF (r - a) t ∂volume) =
        1 := by
    have h := (show (∫⁻ t : ℝ, (1 : ℝ≥0∞)
        ∂(ProbabilityTheory.expMeasure (r - a))) = 1 by simp)
    change (∫⁻ t : ℝ, (1 : ℝ≥0∞)
        ∂(volume.withDensity (ProbabilityTheory.exponentialPDF (r - a)))) = 1 at h
    rw [lintegral_withDensity_eq_lintegral_mul volume hpdfP measurable_const] at h
    simpa using h
  have hDensity (t : ℝ) :
      ENNReal.ofReal (r - a) * ProbabilityTheory.exponentialPDF r t *
        ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)) =
      ENNReal.ofReal r * ProbabilityTheory.exponentialPDF (r - a) t := by
    by_cases ht : 0 ≤ t
    · rw [ProbabilityTheory.exponentialPDF_of_nonneg ht,
          ProbabilityTheory.exponentialPDF_of_nonneg ht,
          Real.coe_toNNReal t ht]
      have hr0 : 0 ≤ r := hr.le
      have hp0 : 0 ≤ r - a := hp.le
      have hprod : 0 ≤ (r - a) * (r * Real.exp (-(r * t))) :=
        mul_nonneg hp0 (mul_nonneg hr0 (Real.exp_nonneg _))
      rw [← ENNReal.ofReal_mul hp0,
          ← ENNReal.ofReal_mul hprod,
          ← ENNReal.ofReal_mul hr0]
      congr 1
      have he : Real.exp (-(r * t)) * Real.exp (a * t) =
          Real.exp (-((r - a) * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (r - a) * (r * Real.exp (-(r * t))) * Real.exp (t * a) =
            (r - a) * r * (Real.exp (-(r * t)) * Real.exp (a * t)) := by
              rw [mul_comm t a]
              ring
        _ = (r - a) * r * Real.exp (-((r - a) * t)) := by rw [he]
        _ = r * ((r - a) * Real.exp (-((r - a) * t))) := by ring
    · have hn : t < 0 := lt_of_not_ge ht
      simp [ProbabilityTheory.exponentialPDF_of_neg hn]
  have hRate :
      ENNReal.ofReal (r - a) *
        (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
          ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a))
          ∂volume) = ENNReal.ofReal r := by
    calc
      _ = (∫⁻ t : ℝ, ENNReal.ofReal (r - a) *
          (ProbabilityTheory.exponentialPDF r t *
            ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)))
          ∂volume) := by
            rw [lintegral_const_mul]
            exact hWeight
      _ = (∫⁻ t : ℝ, ENNReal.ofReal r *
          ProbabilityTheory.exponentialPDF (r - a) t ∂volume) := by
            apply lintegral_congr
            intro t
            simpa only [mul_assoc] using hDensity t
      _ = ENNReal.ofReal r *
          (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF (r - a) t ∂volume) := by
            rw [lintegral_const_mul]
            exact hpdfP
      _ = ENNReal.ofReal r := by rw [hMass, mul_one]
  have hFactor :
      (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
        ENNReal.ofReal (Real.exp (θ * x) *
          Real.exp ((Real.toNNReal t : ℝ) * a)) ∂volume) =
      ENNReal.ofReal (Real.exp (θ * x)) *
        (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
          ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a))
          ∂volume) := by
    calc
      _ = (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (θ * x)) *
          (ProbabilityTheory.exponentialPDF r t *
            ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)))
          ∂volume) := by
            apply lintegral_congr
            intro t
            rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
            ac_rfl
      _ = _ := by
        rw [lintegral_const_mul]
        exact hWeight
  rw [chat04_actual_exp_clock_exponential_eigenfunction_action_ws01a
    P X r hr θ hθ x]
  change ENNReal.ofReal (r - a) *
    (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
      ENNReal.ofReal (Real.exp (θ * x) *
        Real.exp ((Real.toNNReal t : ℝ) * a)) ∂volume) =
    ENNReal.ofReal r * ENNReal.ofReal (Real.exp (θ * x))
  rw [hFactor]
  calc
    ENNReal.ofReal (r - a) *
        (ENNReal.ofReal (Real.exp (θ * x)) *
          (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
            ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a))
            ∂volume)) =
      ENNReal.ofReal (Real.exp (θ * x)) *
        (ENNReal.ofReal (r - a) *
          (∫⁻ t : ℝ, ProbabilityTheory.exponentialPDF r t *
            ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a))
            ∂volume)) := by ac_rfl
    _ = ENNReal.ofReal (Real.exp (θ * x)) * ENNReal.ofReal r := by
      rw [hRate]
    _ = _ := mul_comm _ _
