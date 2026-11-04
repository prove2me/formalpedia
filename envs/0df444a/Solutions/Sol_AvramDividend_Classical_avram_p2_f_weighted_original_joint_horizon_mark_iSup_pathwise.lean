-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_joint_horizon_mark_iSup_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:49:54.973775+00:00
-- url     : https://prove2.me/submissions/c0887c49-638b-4af1-8fcd-d2237f19f960

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Continuity from below of the original intrinsic Lévy jump measure
on increasing simultaneous time-and-mark rectangles, path by path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (T : ℕ → ℝ≥0) (hT : Monotone T)
    (B : ℕ → Set ℝ) (hB : Monotone B) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, Ioc s (s + T n) ×ˢ B n) =
    ⨆ n, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T n) ×ˢ B n) := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hSets : Monotone (fun n : ℕ => Ioc s (s + T n) ×ˢ B n) := by
    intro i j hij
    apply Set.prod_mono
    · intro u hu
      have hTime : s + T i ≤ s + T j := by
        simpa only [add_comm] using (add_le_add_left (hT hij) s)
      exact ⟨hu.1, le_trans hu.2 hTime⟩
    · exact hB hij
  change μ (⋃ n, Ioc s (s + T n) ×ˢ B n) =
    ⨆ n, μ (Ioc s (s + T n) ×ˢ B n)
  exact hSets.measure_iUnion
