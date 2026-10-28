-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_discount_shift_bounded_kernel_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:37:08.62401+00:00
-- url     : https://prove2.me/submissions/b4791565-d1d2-4ef4-b483-9b31b0613359

import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every given positive q-scale has a genuine subunit renewal kernel for shifting its discount by p. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (Wq : ℝ → ℝ)
    (hWq : IsScaleFunction X q Wq) (p : ℝ) (hp : 0 < p) :
    ∃ θ ρ : ℝ, ∃ K : ℝ → ℝ,
      0 ≤ θ ∧ q + p < X.ψ θ ∧ 0 < ρ ∧ ρ < 1 ∧
      Continuous K ∧ BddAbove (Set.range (fun x : ℝ => ‖K x‖)) ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), K x ∂volume) = ρ ∧
      (∀ x : ℝ, x ≤ 0 → K x = 0) ∧
      (∀ x : ℝ, 0 ≤ K x) ∧
      (∀ x : ℝ, K x = p * (Real.exp (-(θ * x)) * Wq x)) := by
  obtain ⟨θ, hθ, hψall⟩ :=
    chat04_psi_eventually_gt_of_unbounded_variation X (q + p) (add_pos hq hp) hnbv
  have hψ : q + p < X.ψ θ := hψall θ le_rfl
  have hψq : q < X.ψ θ := by linarith
  have hψdiff : 0 < X.ψ θ - q := sub_pos.mpr hψq
  let ρ : ℝ := p / (X.ψ θ - q)
  let K : ℝ → ℝ := fun x => p * (Real.exp (-(θ * x)) * Wq x)
  have hρpos : 0 < ρ := div_pos hp hψdiff
  have hρlt : ρ < 1 := (div_lt_one hψdiff).2 (by linarith)
  have hWzero : Wq 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount X hnbv q (le_of_lt hq) Wq hWq
  have hWcont : Continuous Wq :=
    scaleFunction_continuous_of_zero_origin X q Wq hWq hWzero
  have hE : Continuous (fun x : ℝ => Real.exp (-(θ * x))) := by fun_prop
  have hKcont : Continuous K := continuous_const.mul (hE.mul hWcont)
  have hBound : BddAbove (Set.range (fun x : ℝ => ‖K x‖)) := by
    obtain ⟨C, hC⟩ :=
      scaleFunction_global_weighted_norm_bddAbove X q Wq hWq θ hθ hψq
    refine ⟨‖p‖ * C, ?_⟩
    rintro z ⟨x, rfl⟩
    change ‖p * (Real.exp (-(θ * x)) * Wq x)‖ ≤ ‖p‖ * C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC ⟨x, rfl⟩) (norm_nonneg _)
  obtain ⟨hWi, hWmass⟩ := hWq.2.2.2.2 θ hθ hψq
  have hKi : IntegrableOn K (Ioi (0 : ℝ)) volume := by
    change Integrable
      (fun x : ℝ => p * (Real.exp (-(θ * x)) * Wq x))
      (volume.restrict (Ioi (0 : ℝ)))
    exact hWi.const_mul p
  have hKmass : (∫ x in Ioi (0 : ℝ), K x ∂volume) = ρ := by
    simp only [K, integral_const_mul, hWmass, ρ, div_eq_mul_inv]
  have hKzero (x : ℝ) (hx : x ≤ 0) : K x = 0 := by
    rcases lt_or_eq_of_le hx with hlt | heq
    · simp [K, hWq.1 x hlt]
    · subst x
      simp [K, hWzero]
  have hKpos (x : ℝ) : 0 ≤ K x := by
    have hWx : 0 ≤ Wq x := by
      by_cases hx : 0 ≤ x
      · exact hWq.2.1 x hx
      · simp [hWq.1 x (lt_of_not_ge hx)]
    exact mul_nonneg (le_of_lt hp)
      (mul_nonneg (Real.exp_nonneg _) hWx)
  exact ⟨θ, ρ, K, hθ, hψ, hρpos, hρlt, hKcont,
    hBound, hKi, hKmass, hKzero, hKpos, fun _ => rfl⟩
