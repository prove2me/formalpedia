-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_stopped_discounted_raw_jump_source_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:23:29.402947+00:00
-- url     : https://prove2.me/submissions/924ce2a4-6f84-4241-b131-3ee379dc692c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_frozen_preruin_source_cell_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_cell_caplinear_raw_jump_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- All stopped original physical source cells lose their continuous BV
   residual in one discounted inequality, retaining raw negative jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      Monotone u →
      (∀ i : ℕ, i < n →
        u (i + 1) = 0 ∨
          (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) →
      (∑ i ∈ Finset.range n,
        Real.exp (-(q * (u i : ℝ))) *
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
            V (x + X.X (u i) ω - rightLimit D (u i) ω))) ≤
      (∑ i ∈ Finset.range n,
        Real.exp (-(q * (u i : ℝ))) *
          (V ((x + X.X (u i) ω - rightLimit D (u i) ω) +
              (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) -
              (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
               else 0)) -
            V (x + X.X (u i) ω - rightLimit D (u i) ω))) := by
  have hBound := avram_p3_bv_original_source_cell_caplinear_raw_jump_envelope
    X hBV x D w C hC hw_cont hw_smooth hw_grad
  filter_upwards [hBound] with ω hω
  intro u n hu hPre
  apply Finset.sum_le_sum
  intro i hi
  have hUi : u i ≤ u (i + 1) := hu (Nat.le_succ i)
  have hZ := avram_p3_bv_original_frozen_preruin_source_cell_nonnegative
    X x C D hD ω u i hUi (hPre i (Finset.mem_range.mp hi))
  exact mul_le_mul_of_nonneg_left
    (hω u i hUi hZ) (Real.exp_nonneg _)
