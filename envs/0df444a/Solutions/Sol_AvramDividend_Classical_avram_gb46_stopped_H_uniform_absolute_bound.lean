-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb46_stopped_H_uniform_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:16:54.47196+00:00
-- url     : https://prove2.me/submissions/df0019aa-b3b5-4bc1-9dee-1f9c3ad0120c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The stopped, discounted Hessian coefficient is uniformly bounded on
every finite-cap interior band, uniformly in time, stopping rule and reserve. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (t : ℝ≥0) (ρ : Ω → ℝ≥0)
      (Y : Ω → ℝ) (ω : Ω),
      |if t < ρ ω then
        (1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) *
          (if Y ω ∈ Icc (δ / 2)
            (C.toReal * (((j + 1 : ℕ) : ℝ) /
              ((j + 2 : ℕ) : ℝ))) then
              iteratedDeriv 2 w (Y ω) else 0)
      else 0| ≤ B := by
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hcap : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hfrac : (((j + 1 : ℕ) : ℝ) /
      ((j + 2 : ℕ) : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast (show j + 1 < j + 2 by omega)
  have hb : b < C.toReal := by
    dsimp [b]
    nlinarith [mul_lt_mul_of_pos_left hfrac hcap]
  by_cases hab : a ≤ b
  · have hsub : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
      intro y hy
      have ha : 0 < a := by dsimp [a]; positivity
      have hy0 : 0 ≤ y := le_trans (le_of_lt ha) hy.1
      refine ⟨lt_of_lt_of_le ha hy.1, ?_⟩
      exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 hFiniteCap).2
        (lt_of_le_of_lt hy.2 hb)
    have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
      isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
    have hu : UniqueDiffOn ℝ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
      hopen.uniqueDiffOn
    have hc : ContinuousOn
        (iteratedDerivWithin 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
      hw.continuousOn_iteratedDerivWithin (by norm_num) hu
    have heq : EqOn
        (iteratedDerivWithin 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        (iteratedDeriv 2 w)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
      iteratedDerivWithin_of_isOpen hopen
    have hc' : ContinuousOn (fun y => |iteratedDeriv 2 w y|) (Icc a b) :=
      ((hc.congr heq.symm).mono hsub).abs
    obtain ⟨z, hz, hzmax⟩ :=
      isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc'
    let B : ℝ := |iteratedDeriv 2 w z|
    have hB : 0 ≤ B := abs_nonneg _
    have hbound : ∀ y ∈ Icc a b, |iteratedDeriv 2 w y| ≤ B := by
      intro y hy
      exact hzmax hy
    refine ⟨B, hB, ?_⟩
    intro t ρ Y ω
    by_cases ht : t < ρ ω
    · simp only [if_pos ht]
      by_cases hy : Y ω ∈ Icc a b
      · have he0 : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
          (Real.exp_pos _).le
        have htn : 0 ≤ (t : ℝ) := NNReal.coe_nonneg _
        have he1 : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
          have hn : -(q * (t : ℝ)) ≤ 0 := by nlinarith
          simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hn)
        have hprod : Real.exp (-(q * (t : ℝ))) *
            |iteratedDeriv 2 w (Y ω)| ≤ B := by
          calc
            _ ≤ 1 * |iteratedDeriv 2 w (Y ω)| :=
              mul_le_mul_of_nonneg_right he1 (abs_nonneg _)
            _ = |iteratedDeriv 2 w (Y ω)| := one_mul _
            _ ≤ B := hbound (Y ω) hy
        change |(1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) *
          (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)| ≤ B
        rw [if_pos hy, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
          abs_of_nonneg he0]
        calc
          (1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) *
              |iteratedDeriv 2 w (Y ω)| =
              (1 / 2 : ℝ) *
                (Real.exp (-(q * (t : ℝ))) *
                  |iteratedDeriv 2 w (Y ω)|) := by ring
          _ ≤ (1 / 2 : ℝ) * B :=
            mul_le_mul_of_nonneg_left hprod (by norm_num)
          _ ≤ B := by linarith
      · change |(1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) *
            (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)| ≤ B
        simp [hy, hB]
    · simp [ht, hB]
  · refine ⟨0, le_refl _, ?_⟩
    intro t ρ Y ω
    have hnone : Y ω ∉ Icc a b := by
      intro hy
      exact hab (hy.1.trans hy.2)
    by_cases ht : t < ρ ω
    · simp only [if_pos ht]
      change |(1 / 2 : ℝ) * Real.exp (-(q * (t : ℝ))) *
        (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)| ≤ 0
      simp [hnone]
    · simp [ht]
