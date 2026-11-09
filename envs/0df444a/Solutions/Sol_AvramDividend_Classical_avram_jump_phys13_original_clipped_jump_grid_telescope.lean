-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump_phys13_original_clipped_jump_grid_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:26:37.333481+00:00
-- url     : https://prove2.me/submissions/9a49f029-edf7-4e9a-96fd-684bdbb67d15

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_jump_count_grid_telescope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original jump counts partition exactly through the clipped final stopping cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (e : ℕ → ℝ≥0) (he : Monotone e) (N : ℕ)
    (ρ : Ω → ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    J (Ioc (min (e 0) (ρ ω)) (min (e N) (ρ ω)) ×ˢ B) =
      ∑ i ∈ Finset.range N,
        J (Ioc (min (e i) (ρ ω)) (min (e (i + 1)) (ρ ω)) ×ˢ B) := by
  have hClip : Monotone (fun i : ℕ => min (e i) (ρ ω)) := by
    intro i j hij
    exact min_le_min (he hij) le_rfl
  exact avram_ubv_jump12_original_jump_count_grid_telescope
    X ω (fun i => min (e i) (ρ ω)) hClip N B hB
