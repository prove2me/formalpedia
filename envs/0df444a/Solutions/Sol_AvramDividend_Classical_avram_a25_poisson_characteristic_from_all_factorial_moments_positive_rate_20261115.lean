-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_poisson_characteristic_from_all_factorial_moments_positive_rate_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:26:51.74438+00:00
-- url     : https://prove2.me/submissions/0fcb5463-f420-4ac3-ab54-0b2d7f2518ae

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_factorial_moments_positive_mgf_identity_positive_rate_20261115
import Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps10_poisson_power_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real AvramDividend.Classical
open scoped NNReal ENNReal Nat
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n) :
    ∀ u : ℝ,
      charFun (P.map (fun ω => (K ω : ℝ))) u =
      charFun ((poissonMeasure r).map (fun n : ℕ => (n : ℝ))) u := by
  let f : Ω → ℝ := fun ω => (K ω : ℝ)
  let g : ℕ → ℝ := fun n => (n : ℝ)
  have hg : Measurable g := measurable_of_countable _
  have hf : Measurable f := hg.comp hK
  let μ : Measure ℝ := P.map f
  let ν : Measure ℝ := (poissonMeasure r).map g
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  have he (θ : ℝ) (n : ℕ) :
      Real.exp (θ * (n : ℝ)) = (Real.exp θ) ^ n := by
    rw [mul_comm]
    exact Real.exp_nat_mul θ n
  have hIntμ : ∀ θ : ℝ, 0 < θ →
      Integrable (fun y : ℝ => Real.exp (θ * y)) μ := by
    intro θ hθ
    have hA : AEStronglyMeasurable
        (fun y : ℝ => Real.exp (θ * y)) μ := by fun_prop
    exact (integrable_map_measure hA hf.aemeasurable).mpr
      (avram_a25_factorial_moments_positive_mgf_identity_positive_rate_20261115
        P K hK r hr hMom θ hθ).1
  have hIntν : ∀ θ : ℝ, 0 < θ →
      Integrable (fun y : ℝ => Real.exp (θ * y)) ν := by
    intro θ hθ
    have hPow := avram_ubv_ito_jumps10_poisson_power_integrable
      r (Real.exp θ)
    have hExp : Integrable
        (fun n : ℕ => Real.exp (θ * (n : ℝ))) (poissonMeasure r) :=
      hPow.congr (Filter.Eventually.of_forall (fun n => (he θ n).symm))
    have hB : AEStronglyMeasurable
        (fun y : ℝ => Real.exp (θ * y)) ν := by fun_prop
    exact (integrable_map_measure hB hg.aemeasurable).mpr hExp
  have hMean : ∀ θ : ℝ, 0 < θ →
      (∫ y, Real.exp (θ * y) ∂μ) =
        (∫ y, Real.exp (θ * y) ∂ν) := by
    intro θ hθ
    have hA : AEStronglyMeasurable
        (fun y : ℝ => Real.exp (θ * y)) μ := by fun_prop
    have hB : AEStronglyMeasurable
        (fun y : ℝ => Real.exp (θ * y)) ν := by fun_prop
    calc
      (∫ y, Real.exp (θ * y) ∂μ) =
          ∫ ω, Real.exp (θ * (K ω : ℝ)) ∂P := by
            simpa only [μ, f] using (integral_map hf.aemeasurable hA)
      _ = Real.exp ((r : ℝ) * (Real.exp θ - 1)) :=
        (avram_a25_factorial_moments_positive_mgf_identity_positive_rate_20261115
          P K hK r hr hMom θ hθ).2
      _ = ∫ n : ℕ, (Real.exp θ) ^ n ∂poissonMeasure r :=
        (chat06_poisson_count_pgf_general r (Real.exp θ)).symm
      _ = ∫ y, Real.exp (θ * y) ∂ν := by
        rw [integral_map hg.aemeasurable hB]
        apply integral_congr_ae
        filter_upwards [] with n
        exact (he θ n).symm
  have hLaw : μ = ν :=
    measure_eq_of_pos_mgf_on_ray hIntμ hIntν hMean
  intro u
  exact congrArg (fun ρ : Measure ℝ => charFun ρ u) hLaw
