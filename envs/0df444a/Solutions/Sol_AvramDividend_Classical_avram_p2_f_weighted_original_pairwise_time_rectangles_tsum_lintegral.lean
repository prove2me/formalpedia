-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:53:08.120679+00:00
-- url     : https://prove2.me/submissions/acd47a9e-ea0d-4665-9041-5955c438cfc3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-based weighted countable additivity for varying future-time
and Borel mark rectangles, valid at infinite weights and counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℕ → ℝ≥0) (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hTimeDisj : Pairwise (fun i j =>
      Disjoint (Ioc (s i) (s i + T i))
        (Ioc (s j) (s j + T j))))
    (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, Ioc (s n) (s n + T n) ×ˢ B n) ∂P) =
    ∑' n, (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s n) (s n + T n) ×ˢ B n) ∂P) := by
  let N : Set (ℝ≥0 × ℝ) → Ω → ℝ≥0∞ := fun D ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      D
  let S : ℕ → Set (ℝ≥0 × ℝ) :=
    fun n => Ioc (s n) (s n + T n) ×ˢ B n
  have hPath (ω : Ω) : N (⋃ n, S n) ω =
      ∑' n, N (S n) ω :=
    avram_p2_f_weighted_original_pairwise_time_rectangles_tsum_pathwise
      X s (fun n => s n + T n) B hB hTimeDisj ω
  have hMeas (n : ℕ) :
      Measurable (fun ω => H ω * N (S n) ω) :=
    hH.mul (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
      X (s n) (T n) (B n) (hB n))
  change (∫⁻ ω, H ω * N (⋃ n, S n) ω ∂P) =
    ∑' n, (∫⁻ ω, H ω * N (S n) ω ∂P)
  calc
    (∫⁻ ω, H ω * N (⋃ n, S n) ω ∂P) =
      (∫⁻ ω, ∑' n, H ω * N (S n) ω ∂P) := by
        congr 1
        funext ω
        rw [hPath ω]
        exact (ENNReal.tsum_mul_left).symm
    _ = _ := MeasureTheory.lintegral_tsum
      (fun n => (hMeas n).aemeasurable)
