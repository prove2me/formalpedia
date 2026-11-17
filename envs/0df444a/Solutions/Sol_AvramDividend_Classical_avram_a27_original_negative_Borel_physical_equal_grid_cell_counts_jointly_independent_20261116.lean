-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_negative_Borel_physical_equal_grid_cell_counts_jointly_independent_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:39:36.499078+00:00
-- url     : https://prove2.me/submissions/c55d2dc9-c9d1-427f-bfed-0f17c3c5d7b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_Borel_physical_grid_prefix_tuple_filtration_measurable_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_physical_marked_future_count_independent_of_any_past_observable_20261115
import Theorems.Thm_AvramDividend_Classical_avram_a27_finite_chronological_prefix_independence_implies_mutual_independence_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    iIndepFun (fun i : Fin n => fun ω : Ω =>
      NX ω (Ioc ((i.val : ℝ≥0) * δ)
        (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let δ : ℝ≥0 := T / (n : ℝ≥0)
  let C : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    NX ω (Ioc ((i : ℝ≥0) * δ)
      (((i + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)
  change iIndepFun (fun i : Fin n => C i.val) P
  have hMeas : ∀ i < n, Measurable (C i) := by
    intro i hi
    have hle : (i : ℝ≥0) * δ ≤ (((i + 1 : ℕ) : ℝ≥0) * δ) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) bot_le
    simpa only [C, NX] using
      (avram_p2_e_compensator_intrinsic_rectangle_count_measurable
        X ((i : ℝ≥0) * δ) (((i + 1 : ℕ) : ℝ≥0) * δ) hle B hB)
  have hPrefix : ∀ k < n,
      IndepFun (fun ω : Ω => fun i : Fin k => C i.val ω) (C k) P := by
    intro k hk
    have hPast :
        Measurable[𝓕 ((k : ℝ≥0) * δ)]
          (fun ω : Ω => fun i : Fin k => C i.val ω) := by
      simpa only [C, NX, δ] using
        (avram_a27_original_Borel_physical_grid_prefix_tuple_filtration_measurable_20261116
          X T B hB n k (Nat.le_of_lt hk))
    have hInd :=
      avram_a25_original_physical_marked_future_count_independent_of_any_past_observable_20261115
        X ((k : ℝ≥0) * δ) δ B hB
        (fun ω : Ω => fun i : Fin k => C i.val ω) hPast
    have hright : (k : ℝ≥0) * δ + δ =
        (((k + 1 : ℕ) : ℝ≥0) * δ) := by
      simp [Nat.cast_add, add_mul]
    simpa only [C, NX, hright] using hInd
  exact avram_a27_finite_chronological_prefix_independence_implies_mutual_independence_20261116
    P n C hMeas hPrefix
