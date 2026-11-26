-- Prove2me | solution 1 for BranchActualCount.original_occurrence_sublinear_bound
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T22:35:16.312177+00:00
-- url     : https://prove2.me/submissions/846eef07-7bd3-4d15-a381-fb451d31ad90

import Mathlib
import Theorems.Thm_BranchActualCount_closed_occurrence_count_exact
import Theorems.Thm_BranchActualCount_global_closed_and_all_window_bounds
theorem solution :
    let xi : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (s : {s : ℂ // xi s = 0 ∧ 0 < s.im}) × Fin (analyticOrderNatAt xi s.val)
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    ∀ y ≥ (1 : ℝ), ∀ F : Finset I,
      (∀ i ∈ F, i.1.val.im^2 ≤ y) → (F.card : ℝ) ≤ 4*(N 600+600)*y^((3 : ℝ)/4) := by
  dsimp only
  intro y hy F hF
  have hf : ∀ i ∈ F, i.1.val.im ≤ Real.sqrt y := by
    intro i hi
    nlinarith [hF i hi,Real.sq_sqrt (show 0 ≤ y by linarith),Real.sqrt_nonneg y]
  have hb := BranchActualCount.closed_occurrence_count_exact.2 (Real.sqrt y) F hf
  exact hb.trans (BranchActualCount.global_closed_and_all_window_bounds.2.1 y hy)
