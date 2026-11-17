-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:16:49.619071+00:00
-- url     : https://prove2.me/submissions/4636d1ea-fadc-49f7-a1b3-87072e55d85c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_window_finite_marked_times_card
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔
       0 < u ∧ u ≤ T ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) :
    ((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B) =
       (((S.filter (fun u : ℝ≥0 => s < u ∧ u ≤ t)).card : ℕ) : ℝ≥0∞) := by
  classical
  let Q : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
  have hQ : Q = (S : Set ℝ≥0) := by
    ext u
    exact (hS u).symm
  have hF : Q.Finite := by
    rw [hQ]
    exact S.finite_toSet
  have hFEq : hF.toFinset = S := by
    ext u
    simp only [Set.Finite.mem_toFinset, hQ]
    rfl
  have hCount :=
    avram_a20_original_borel_window_finite_marked_times_card
      X ω T B hB s t hst htT hF
  simpa only [hFEq] using hCount
