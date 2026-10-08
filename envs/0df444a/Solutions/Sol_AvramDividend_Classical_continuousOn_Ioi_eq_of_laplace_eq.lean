-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_Ioi_eq_of_laplace_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:12:38.335931+00:00
-- url     : https://prove2.me/submissions/02e58c38-fb38-4789-bfbf-6101acb2f65d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_exponential_withDensity_eq

open MeasureTheory Filter Set Topology
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology
open ProbabilityTheory
open AvramDividend.Classical

theorem solution
    (f g : ℝ → ℝ) (b : ℝ)
    (hfcont : ContinuousOn f (Ioi 0))
    (hgcont : ContinuousOn g (Ioi 0))
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * f x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * g x) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * f x =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  let B : ℝ := b + 1
  let μ0 : Measure ℝ := volume.restrict (Ioi 0)
  have hB : b < B := by
    dsimp [B]
    linarith
  have hfB : Integrable (fun x : ℝ => Real.exp (-B * x) * f x) μ0 := by
    dsimp [μ0]
    exact (hlap B hB).1.integrable
  have hgB : Integrable (fun x : ℝ => Real.exp (-B * x) * g x) μ0 := by
    dsimp [μ0]
    exact (hlap B hB).2.1.integrable
  have hf_ae : AEMeasurable f μ0 := by
    simpa [μ0] using hfcont.aemeasurable measurableSet_Ioi
  have hg_ae : AEMeasurable g μ0 := by
    simpa [μ0] using hgcont.aemeasurable measurableSet_Ioi
  have hexp_ae :
      AEMeasurable (fun x : ℝ => Real.exp (-B * x)) μ0 := by
    fun_prop
  have hfdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x)) μ0 :=
    (hexp_ae.mul hf_ae).ennreal_ofReal
  have hgdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x)) μ0 :=
    (hexp_ae.mul hg_ae).ennreal_ofReal
  let μf : Measure ℝ := μ0.withDensity
    (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x))
  let μg : Measure ℝ := μ0.withDensity
    (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x))
  letI : IsFiniteMeasure μf := by
    dsimp [μf]
    exact isFiniteMeasure_withDensity_ofReal hfB.hasFiniteIntegral
  letI : IsFiniteMeasure μg := by
    dsimp [μg]
    exact isFiniteMeasure_withDensity_ofReal hgB.hasFiniteIntegral

  have hf_mgf_int (t : ℝ) (ht : t < 1) :
      Integrable (fun x : ℝ => Real.exp (t * x)) μf := by
    have hθ : b < B - t := by
      dsimp [B]
      linarith
    have hbase : Integrable
        (fun x : ℝ => Real.exp (-(B - t) * x) * f x) μ0 := by
      dsimp [μ0]
      exact (hlap (B - t) hθ).1.integrable
    dsimp [μf]
    rw [integrable_withDensity_iff_integrable_smul₀' hfdens (by simp)]
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hfx : 0 ≤ f x := hfnonneg x hx
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hfx)]
    simp only [smul_eq_mul]
    calc
      Real.exp (-(B - t) * x) * f x
          = (Real.exp (-B * x) * Real.exp (t * x)) * f x := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = (Real.exp (-B * x) * f x) * Real.exp (t * x) := by ring

  have hg_mgf_int (t : ℝ) (ht : t < 1) :
      Integrable (fun x : ℝ => Real.exp (t * x)) μg := by
    have hθ : b < B - t := by
      dsimp [B]
      linarith
    have hbase : Integrable
        (fun x : ℝ => Real.exp (-(B - t) * x) * g x) μ0 := by
      dsimp [μ0]
      exact (hlap (B - t) hθ).2.1.integrable
    dsimp [μg]
    rw [integrable_withDensity_iff_integrable_smul₀' hgdens (by simp)]
    refine hbase.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hgx : 0 ≤ g x := hgnonneg x hx
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hgx)]
    simp only [smul_eq_mul]
    calc
      Real.exp (-(B - t) * x) * g x
          = (Real.exp (-B * x) * Real.exp (t * x)) * g x := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = (Real.exp (-B * x) * g x) * Real.exp (t * x) := by ring

  have hf_strip : Iio (1 : ℝ) ⊆ interior (integrableExpSet id μf) := by
    apply interior_maximal
    · intro t ht
      exact hf_mgf_int t ht
    · exact isOpen_Iio
  have hg_strip : Iio (1 : ℝ) ⊆ interior (integrableExpSet id μg) := by
    apply interior_maximal
    · intro t ht
      exact hg_mgf_int t ht
    · exact isOpen_Iio

  have hf_an :
      AnalyticOnNhd ℂ (complexMGF id μf) {z : ℂ | z.re < 1} := by
    exact analyticOnNhd_complexMGF.mono (fun z hz => hf_strip hz)
  have hg_an :
      AnalyticOnNhd ℂ (complexMGF id μg) {z : ℂ | z.re < 1} := by
    exact analyticOnNhd_complexMGF.mono (fun z hz => hg_strip hz)

  have hmgf_f (t : ℝ) (ht : t < 1) :
      mgf id μf t =
        ∫ x in Ioi (0 : ℝ), Real.exp (-(B - t) * x) * f x := by
    have hθ : b < B - t := by
      dsimp [B]
      linarith
    rw [mgf]
    dsimp [μf]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hfdens (by simp)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hfx : 0 ≤ f x := hfnonneg x hx
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hfx)]
    simp only [id_eq, smul_eq_mul]
    calc
      (Real.exp (-B * x) * f x) * Real.exp (t * x)
          = (Real.exp (-B * x) * Real.exp (t * x)) * f x := by ring
      _ = Real.exp (-(B - t) * x) * f x := by
        rw [← Real.exp_add]
        congr 2
        ring

  have hmgf_g (t : ℝ) (ht : t < 1) :
      mgf id μg t =
        ∫ x in Ioi (0 : ℝ), Real.exp (-(B - t) * x) * g x := by
    have hθ : b < B - t := by
      dsimp [B]
      linarith
    rw [mgf]
    dsimp [μg]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hgdens (by simp)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hgx : 0 ≤ g x := hgnonneg x hx
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_pos _).le hgx)]
    simp only [id_eq, smul_eq_mul]
    calc
      (Real.exp (-B * x) * g x) * Real.exp (t * x)
          = (Real.exp (-B * x) * Real.exp (t * x)) * g x := by ring
      _ = Real.exp (-(B - t) * x) * g x := by
        rw [← Real.exp_add]
        congr 2
        ring

  have hreal : ∀ t : ℝ, t < 1 →
      complexMGF id μf (t : ℂ) = complexMGF id μg (t : ℂ) := by
    intro t ht
    rw [complexMGF_ofReal, complexMGF_ofReal, hmgf_f t ht, hmgf_g t ht]
    exact congrArg (fun r : ℝ => (r : ℂ))
      (hlap (B - t) (by dsimp [B]; linarith)).2.2

  have hmeasure : μf = μg :=
    finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
      μf μg 1 zero_lt_one hf_an hg_an hreal
  exact continuousOn_Ioi_eq_of_exponential_withDensity_eq
    f g B hfcont hgcont hfnonneg hgnonneg hfdens hgdens hmeasure
