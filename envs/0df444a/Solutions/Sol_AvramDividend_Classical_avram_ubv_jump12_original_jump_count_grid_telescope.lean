-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump12_original_jump_count_grid_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:56:48.025067+00:00
-- url     : https://prove2.me/submissions/51a885bf-b235-437a-aa45-863fae009a8b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_original_jump_count_two_cell_add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (e : ℕ → ℝ≥0) (he : Monotone e) (N : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let J : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    J (Ioc (e 0) (e N) ×ˢ B) =
      ∑ i ∈ Finset.range N,
        J (Ioc (e i) (e (i + 1)) ×ˢ B) := by
  classical
  let J : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
     (fun u : ℝ≥0 => (u,
       X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change J (Ioc (e 0) (e N) ×ˢ B) =
    ∑ i ∈ Finset.range N, J (Ioc (e i) (e (i + 1)) ×ˢ B)
  induction N with
  | zero =>
      simp
  | succ n ih =>
      have hPart : J (Ioc (e 0) (e (n + 1)) ×ˢ B) =
          J (Ioc (e 0) (e n) ×ˢ B) +
          J (Ioc (e n) (e (n + 1)) ×ˢ B) := by
        exact AvramDividend.Classical.avram_ubv_jump12_original_jump_count_two_cell_add
          X ω (e 0) (e n) (e (n + 1))
          (he (Nat.zero_le n)) (he (Nat.le_succ n)) B hB
      simp only [Finset.sum_range_succ]
      rw [hPart, ih]
