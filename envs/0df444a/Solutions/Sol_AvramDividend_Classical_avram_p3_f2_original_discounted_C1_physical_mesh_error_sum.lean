-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_discounted_C1_physical_mesh_error_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:06:25.794896+00:00
-- url     : https://prove2.me/submissions/9c189665-b2c3-44a5-b2f0-c44a6c513cab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_global_stopped_C1_source_cell_taylor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Discounted physical-grid C1 source remainders inherit the genuine unweighted error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ),
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        let z : ℕ → ℝ := fun i =>
          x + X.X (u i) ω - rightLimit D (u i) ω
        let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
        (∀ i, i < n →
          Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
        (∀ i, i < n → |c i| < δ) →
        |∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
        ε * ∑ i ∈ Finset.range n, |c i| := by
  intro ε hε
  obtain ⟨δ, hδ, hCells⟩ :=
    avram_p3_f2_original_global_stopped_C1_source_cell_taylor
      X x C D hD w hwC1 hOpen a b hBand ε hε
  refine ⟨δ, hδ, ?_⟩
  intro ω u n J Y z c hInside hSmall
  have hError := hCells ω u n hInside hSmall
  have hWeighted : ∀ i, i < n →
      |Real.exp (-(q * (u i : ℝ))) *
        (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
        ε * |c i| := by
    intro i hi
    have hTime : 0 ≤ (u i : ℝ) := by exact_mod_cast (u i).property
    have hArg : -(q * (u i : ℝ)) ≤ 0 := neg_nonpos.mpr (mul_nonneg hq hTime)
    have hExpLe : Real.exp (-(q * (u i : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr hArg
    have hExpNonneg : 0 ≤ Real.exp (-(q * (u i : ℝ))) :=
      (Real.exp_pos _).le
    rw [abs_mul, abs_of_nonneg hExpNonneg]
    calc
      Real.exp (-(q * (u i : ℝ))) *
        |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
          1 * |w (z i + c i) - w (z i) - deriv w (z i) * c i| :=
            mul_le_mul_of_nonneg_right hExpLe (abs_nonneg _)
      _ = |w (z i + c i) - w (z i) - deriv w (z i) * c i| := one_mul _
      _ ≤ ε * |c i| := hError i hi
  calc
    |∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
        ∑ i ∈ Finset.range n,
          |Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| :=
              Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * |c i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact hWeighted i (Finset.mem_range.mp hi)
    _ = ε * ∑ i ∈ Finset.range n, |c i| := by rw [Finset.mul_sum]
