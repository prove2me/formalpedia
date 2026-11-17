-- Prove2me | solution 1 for BranchActualCount.concrete_zero_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T18:41:27.828249+00:00
-- url     : https://prove2.me/submissions/bf3fb9ce-9485-4e1b-b08e-194d4a899f10

import Mathlib
import Theorems.Thm_BranchActualCount_unit_window_bound
import Theorems.Thm_BranchActualCount_eventual_lower_density

theorem solution :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    (∀ T ≥ (600 : ℝ), N (T+1)-N T ≤ 50*Real.log (T+3)) ∧
    (∀ᶠ T : ℝ in Filter.atTop, T*Real.log T/(32*Real.pi) ≤ N T) := by
  exact ⟨BranchActualCount.unit_window_bound, BranchActualCount.eventual_lower_density⟩
