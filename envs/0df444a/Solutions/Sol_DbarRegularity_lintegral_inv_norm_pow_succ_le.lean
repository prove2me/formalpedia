-- Prove2me | solution 1 for DbarRegularity.lintegral_inv_norm_pow_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T14:49:17.070684+00:00
-- url     : https://prove2.me/submissions/81b0e443-7cc3-4f2c-8d05-1b1f74862b74

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal

/-- The tail integral `∫_{|x| ≥ R} |x|^{-(d+1)} dx` is at most `C / R`. -/
theorem lintegral_inv_norm_pow_succ_le (d : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 0 < R →
      ∫⁻ x in {x : EuclideanSpace ℝ (Fin d) | R ≤ ‖x‖}, ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹)
        ≤ ENNReal.ofReal (C / R) := by
  set V := EuclideanSpace ℝ (Fin d)
  set I₁ : ℝ≥0∞ := ∫⁻ u : V, {u : V | 1 ≤ ‖u‖}.indicator
    (fun u => ENNReal.ofReal ((‖u‖ ^ (d + 1))⁻¹)) u with hI₁
  have hI₁fin : I₁ < ⊤ := by
    have hJ := finite_integral_one_add_norm (E := V) (μ := volume) (r := (d + 1 : ℝ))
      (by simp [V, finrank_euclideanSpace_fin])
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := 2 ^ (d + 1))) hJ)
    rw [hI₁, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun u => ?_
    by_cases hu : 1 ≤ ‖u‖
    · rw [indicator_of_mem (by exact hu), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h0 : 0 < ‖u‖ := by linarith
      have h1 : 1 + ‖u‖ ≤ 2 * ‖u‖ := by linarith
      rw [Real.rpow_neg (by positivity), show (d + 1 : ℝ) = ((d + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
      rw [← inv_pow, ← inv_pow, ← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ h0]
      linarith
    · rw [indicator_of_notMem (by exact hu)]; simp
  refine ⟨I₁.toReal, fun R hR => ?_⟩
  have hR0 : R ≠ 0 := hR.ne'
  have hfin : Module.finrank ℝ V = d := finrank_euclideanSpace_fin
  set F : V → ℝ≥0∞ := {x : V | R ≤ ‖x‖}.indicator (fun x => ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹))
    with hF
  have hFm : Measurable F := by
    refine Measurable.indicator (by fun_prop) ?_
    exact measurableSet_le measurable_const measurable_norm
  have hmap := Measure.map_addHaar_smul (volume : Measure V) hR0
  rw [hfin] at hmap
  have h1 : ∫⁻ x, F x ∂(Measure.map (R • ·) volume) = ∫⁻ u, F (R • u) :=
    lintegral_map hFm (measurable_const_smul R)
  rw [hmap, lintegral_smul_measure] at h1
  have h2 : ∀ u : V, F (R • u) = ENNReal.ofReal ((R ^ (d + 1))⁻¹) *
      {u : V | 1 ≤ ‖u‖}.indicator (fun u => ENNReal.ofReal ((‖u‖ ^ (d + 1))⁻¹)) u := by
    intro u
    simp only [hF, indicator, mem_setOf_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    by_cases hu : 1 ≤ ‖u‖
    · have : R ≤ R * ‖u‖ := by nlinarith
      rw [if_pos this, if_pos hu, ← ENNReal.ofReal_mul (by positivity), mul_pow, mul_inv]
    · have : ¬ R ≤ R * ‖u‖ := fun h => hu (by
        by_contra h'; push_neg at h'; nlinarith)
      rw [if_neg this, if_neg hu, mul_zero]
  simp_rw [h2] at h1
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hI₁] at h1
  have hc : ENNReal.ofReal |(R ^ d)⁻¹| ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff] ; positivity
  have hS : ∫⁻ x in {x : V | R ≤ ‖x‖}, ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹) = ∫⁻ x, F x := by
    rw [hF, lintegral_indicator (measurableSet_le measurable_const measurable_norm)]
  rw [hS]
  rw [smul_eq_mul] at h1
  have h3 : ∫⁻ x, F x = ENNReal.ofReal (R ^ d) *
      (ENNReal.ofReal ((R ^ (d + 1))⁻¹) * I₁) := by
    calc ∫⁻ x, F x = ENNReal.ofReal (R ^ d) * (ENNReal.ofReal |(R ^ d)⁻¹| * ∫⁻ x, F x) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
            mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
      _ = _ := by rw [h1]
  rw [h3, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have h4 : R ^ d * (R ^ (d + 1))⁻¹ = 1 / R := by
    rw [pow_succ]; field_simp
  rw [h4, ← ENNReal.ofReal_toReal hI₁fin.ne, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  apply le_of_eq; congr 1; ring

end DbarRegularity

open DbarRegularity

open MeasureTheory Set
open scoped ENNReal

theorem solution (d : ℕ) :
    ∃ C : ℝ, ∀ R : ℝ, 0 < R →
      ∫⁻ x in {x : EuclideanSpace ℝ (Fin d) | R ≤ ‖x‖}, ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹)
        ≤ ENNReal.ofReal (C / R) :=
  lintegral_inv_norm_pow_succ_le d
