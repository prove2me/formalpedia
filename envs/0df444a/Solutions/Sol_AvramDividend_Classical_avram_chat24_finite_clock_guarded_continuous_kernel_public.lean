-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_finite_clock_guarded_continuous_kernel_public
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T15:27:34.080297+00:00
-- url     : https://prove2.me/submissions/63cedbb9-f125-4476-9491-8a7109b504ee

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section

set_option autoImplicit false

/-- Integrability of a bounded, compactly clocked continuous kernel on a finite measure. -/
theorem solution (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (Y : ℝ≥0 → ℝ) (hY : Measurable Y)
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) (q : ℝ)
    (hq : 0 ≤ q) (τ : ℝ≥0) :
    Integrable (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Set.Icc a b then
      Real.exp (-(q * (t : ℝ))) * f (Y t) else 0) μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  set C' : ℝ := max C 0 with hC'
  let φ : ℝ → ℝ := fun y => min (max y a) b
  have hφcont : Continuous φ := by
    dsimp only [φ]
    exact (continuous_id.max continuous_const).min continuous_const
  have hφmem : ∀ y, φ y ∈ Set.Icc a b := by
    intro y
    dsimp only [φ]
    exact ⟨le_min (le_max_right y a) hab, min_le_right _ _⟩
  have hφfix : ∀ y ∈ Set.Icc a b, φ y = y := by
    intro y hy
    dsimp only [φ]
    rw [max_eq_left hy.1, min_eq_left hy.2]
  let F : ℝ → ℝ := fun y => f (φ y)
  have hFcont : Continuous F := by
    dsimp only [F]
    exact hf.comp_continuous hφcont hφmem
  have hFmeas : Measurable F := hFcont.measurable
  let s : Set ℝ≥0 := {t | t ≤ τ ∧ Y t ∈ Set.Icc a b}
  have hs : MeasurableSet s := by
    dsimp only [s]
    exact measurableSet_Iic.inter (hY measurableSet_Icc)
  have hmeas : Measurable
      (fun t : ℝ≥0 => if t ∈ s then Real.exp (-(q * (t : ℝ))) * F (Y t) else 0) := by
    apply Measurable.ite hs
    · have h1 : Measurable fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) := by
        apply Real.measurable_exp.comp
        exact (measurable_const.mul measurable_coe_nnreal_real).neg
      exact h1.mul (hFmeas.comp hY)
    · exact measurable_const
  have hg : (fun t : ℝ≥0 => if t ≤ τ ∧ Y t ∈ Set.Icc a b then
        Real.exp (-(q * (t : ℝ))) * f (Y t) else 0)
      = fun t : ℝ≥0 => if t ∈ s then Real.exp (-(q * (t : ℝ))) * F (Y t) else 0 := by
    funext t
    by_cases ht : t ≤ τ ∧ Y t ∈ Set.Icc a b
    · have hts : t ∈ s := ht
      rw [if_pos ht, if_pos hts]
      dsimp only [F]
      rw [hφfix (Y t) ht.2]
    · have hts : t ∉ s := ht
      rw [if_neg ht, if_neg hts]
  have hbound : ∀ᵐ t : ℝ≥0 ∂μ,
      ‖(if t ∈ s then Real.exp (-(q * (t : ℝ))) * F (Y t) else 0)‖ ≤ C' := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t ∈ s
    · rw [if_pos ht]
      have ht' : t ≤ τ ∧ Y t ∈ Set.Icc a b := ht
      have hexp_le : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
        nlinarith [hq, ht0]
      have hexp_nonneg : 0 ≤ Real.exp (-(q * (t : ℝ))) := (Real.exp_pos _).le
      have hFb : ‖F (Y t)‖ ≤ C := hC (φ (Y t)) (hφmem (Y t))
      calc ‖Real.exp (-(q * (t : ℝ))) * F (Y t)‖
          = Real.exp (-(q * (t : ℝ))) * ‖F (Y t)‖ := by
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hexp_nonneg]
        _ ≤ 1 * C := mul_le_mul hexp_le hFb (norm_nonneg _) (by norm_num)
        _ = C := one_mul C
        _ ≤ C' := le_max_left _ _
    · rw [if_neg ht, norm_zero]
      exact le_max_right C 0
  rw [hg]
  exact Integrable.of_bound hmeas.aestronglyMeasurable C' hbound
