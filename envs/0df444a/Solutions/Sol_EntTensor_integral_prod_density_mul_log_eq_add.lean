-- Prove2me | solution 1 for EntTensor.integral_prod_density_mul_log_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T03:59:54.584674+00:00
-- url     : https://prove2.me/submissions/f5aa8b3f-2027-4fbd-a8b2-08d467451ab7

import Theorems.Thm_EntFunctional_toReal_klDiv_withDensity_eq_integral_mul_log
import Theorems.Thm_Tensorization_klDiv_prod_eq_add
import Mathlib.MeasureTheory.Integral.Prod

open Real MeasureTheory InformationTheory
open scoped ENNReal NNReal

theorem solution
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {g₁ : α → ℝ} {g₂ : β → ℝ}
    (hg₁_meas : Measurable g₁) (hg₁_nonneg : ∀ x, 0 ≤ g₁ x)
    (hg₁_int : Integrable g₁ μ) (hg₁_mass : ∫ x, g₁ x ∂μ = 1)
    (hg₁_ent : Integrable (fun x ↦ g₁ x * log (g₁ x)) μ)
    (hg₂_meas : Measurable g₂) (hg₂_nonneg : ∀ y, 0 ≤ g₂ y)
    (hg₂_int : Integrable g₂ ν) (hg₂_mass : ∫ y, g₂ y ∂ν = 1)
    (hg₂_ent : Integrable (fun y ↦ g₂ y * log (g₂ y)) ν) :
    (∫ z, (g₁ z.1 * g₂ z.2) * log (g₁ z.1 * g₂ z.2) ∂(μ.prod ν))
      = (∫ x, g₁ x * log (g₁ x) ∂μ) + (∫ y, g₂ y * log (g₂ y) ∂ν) := by
  classical
  set Q₁ : Measure α := μ.withDensity (fun x ↦ ENNReal.ofReal (g₁ x)) with hQ₁
  set Q₂ : Measure β := ν.withDensity (fun y ↦ ENNReal.ofReal (g₂ y)) with hQ₂
  have hQ₁meas : Measurable (fun x ↦ ENNReal.ofReal (g₁ x)) :=
    ENNReal.measurable_ofReal.comp hg₁_meas
  have hQ₂meas : Measurable (fun y ↦ ENNReal.ofReal (g₂ y)) :=
    ENNReal.measurable_ofReal.comp hg₂_meas
  have hQ₁univ : Q₁ Set.univ = 1 := by
    rw [hQ₁, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hg₁_int (ae_of_all _ hg₁_nonneg),
      hg₁_mass, ENNReal.ofReal_one]
  have hQ₂univ : Q₂ Set.univ = 1 := by
    rw [hQ₂, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hg₂_int (ae_of_all _ hg₂_nonneg),
      hg₂_mass, ENNReal.ofReal_one]
  haveI : IsProbabilityMeasure Q₁ := ⟨hQ₁univ⟩
  haveI : IsProbabilityMeasure Q₂ := ⟨hQ₂univ⟩
  have hprod : Q₁.prod Q₂
      = (μ.prod ν).withDensity
          (fun z ↦ ENNReal.ofReal (g₁ z.1) * ENNReal.ofReal (g₂ z.2)) := by
    rw [hQ₁, hQ₂]; exact prod_withDensity hQ₁meas hQ₂meas
  set G : (α × β) → ℝ := fun z ↦ g₁ z.1 * g₂ z.2 with hG
  have hG_meas : Measurable G := (hg₁_meas.comp measurable_fst).mul (hg₂_meas.comp measurable_snd)
  have hG_nonneg : ∀ z, 0 ≤ G z := fun z ↦ mul_nonneg (hg₁_nonneg _) (hg₂_nonneg _)
  have hof : (fun z : α × β ↦ ENNReal.ofReal (g₁ z.1) * ENNReal.ofReal (g₂ z.2))
      = fun z ↦ ENNReal.ofReal (G z) := by
    funext z; rw [hG]; exact (ENNReal.ofReal_mul (hg₁_nonneg _)).symm
  have hG_int : Integrable G (μ.prod ν) := hg₁_int.mul_prod hg₂_int
  have hG_mass : ∫ z, G z ∂(μ.prod ν) = 1 := by
    rw [hG, integral_prod_mul, hg₁_mass, hg₂_mass, mul_one]
  have hklG : (klDiv (Q₁.prod Q₂) (μ.prod ν)).toReal = ∫ z, G z * log (G z) ∂(μ.prod ν) := by
    rw [hprod, hof]
    exact EntFunctional.toReal_klDiv_withDensity_eq_integral_mul_log
      hG_meas hG_nonneg hG_int hG_mass
  have hkl₁ : (klDiv Q₁ μ).toReal = ∫ x, g₁ x * log (g₁ x) ∂μ := by
    rw [hQ₁]
    exact EntFunctional.toReal_klDiv_withDensity_eq_integral_mul_log
      hg₁_meas hg₁_nonneg hg₁_int hg₁_mass
  have hkl₂ : (klDiv Q₂ ν).toReal = ∫ y, g₂ y * log (g₂ y) ∂ν := by
    rw [hQ₂]
    exact EntFunctional.toReal_klDiv_withDensity_eq_integral_mul_log
      hg₂_meas hg₂_nonneg hg₂_int hg₂_mass
  have hac₁ : Q₁ ≪ μ := by rw [hQ₁]; exact withDensity_absolutelyContinuous _ _
  have hac₂ : Q₂ ≪ ν := by rw [hQ₂]; exact withDensity_absolutelyContinuous _ _
  have hrn₁ : Q₁.rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (g₁ x) := by
    rw [hQ₁]; exact Measure.rnDeriv_withDensity μ hQ₁meas
  have hrn₂ : Q₂.rnDeriv ν =ᵐ[ν] fun y ↦ ENNReal.ofReal (g₂ y) := by
    rw [hQ₂]; exact Measure.rnDeriv_withDensity ν hQ₂meas
  have hllr_int₁ : Integrable (llr Q₁ μ) Q₁ := by
    rw [← integrable_rnDeriv_mul_log_iff hac₁]
    refine (hg₁_ent).congr ?_
    filter_upwards [hrn₁] with x hx
    rw [hx, ENNReal.toReal_ofReal (hg₁_nonneg x)]
  have hllr_int₂ : Integrable (llr Q₂ ν) Q₂ := by
    rw [← integrable_rnDeriv_mul_log_iff hac₂]
    refine (hg₂_ent).congr ?_
    filter_upwards [hrn₂] with y hy
    rw [hy, ENNReal.toReal_ofReal (hg₂_nonneg y)]
  have hne₁ : klDiv Q₁ μ ≠ ∞ := klDiv_ne_top hac₁ hllr_int₁
  have hne₂ : klDiv Q₂ ν ≠ ∞ := klDiv_ne_top hac₂ hllr_int₂
  have htensor : klDiv (Q₁.prod Q₂) (μ.prod ν) = klDiv Q₁ μ + klDiv Q₂ ν :=
    Tensorization.klDiv_prod_eq_add Q₁ μ Q₂ ν
  have hfin : (klDiv (Q₁.prod Q₂) (μ.prod ν)).toReal
      = (klDiv Q₁ μ).toReal + (klDiv Q₂ ν).toReal := by
    rw [htensor, ENNReal.toReal_add hne₁ hne₂]
  rw [hklG, hkl₁, hkl₂] at hfin
  simpa [hG] using hfin
