-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_grid_intrinsic_pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:03:55.162699+00:00
-- url     : https://prove2.me/submissions/0b0e614e-6819-442c-87d6-96644495b241

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_grid_past_cell_sum
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_cell_intrinsic_count
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceil_past_intrinsic_count

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k)
    (s t : Fin k → ℝ≥0) (hst : ∀ i, s i ≤ t i) (htT : ∀ i, t i ≤ T)
    (hs : ∀ i, (s i : ℝ) = (i.val : ℝ) * (T : ℝ) / (k : ℝ))
    (ht : ∀ i, (t i : ℝ) = ((i.val + 1 : ℕ) : ℝ) * (T : ℝ) / (k : ℝ)) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    ∀ ω, (((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
      Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
        Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)) =
      ∑ i : Fin k, N 0 (s i) ω * N (s i) (t i) ω := by
  classical
  dsimp only
  intro ω
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  have hpos : ∀ u ∈ F, (0 : ℝ≥0) < u := by
    intro u hu
    have hu' : u ∈ {v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
        X.X v ω - Function.leftLim (fun y : ℝ≥0 => X.X y ω) v ≤
          -(1 / ((n : ℝ) + 1))} := by
      simpa only [F, Set.Finite.mem_toFinset] using hu
    exact hu'.1
  have hcard :=
    avram_leanlevy_bridge_original_ceil_grid_past_cell_sum X ω T hT n k hk
  dsimp only at hcard
  rw [hcard, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_mul]
  rw [avram_leanlevy_bridge_original_ceil_past_intrinsic_count
    X ω T hT k hk i.val (s i) ((hst i).trans (htT i))
      (hs i) n F rfl hpos]
  rw [avram_leanlevy_bridge_original_ceil_cell_intrinsic_count
    X ω T hT k hk i.val (s i) (t i) (hst i) (htT i)
      (hs i) (ht i) n]
