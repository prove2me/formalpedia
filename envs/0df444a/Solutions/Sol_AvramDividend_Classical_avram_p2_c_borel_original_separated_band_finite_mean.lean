-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_separated_band_finite_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:52:03.653195+00:00
-- url     : https://prove2.me/submissions/9e0fe97f-4cae-4347-8f80-e2b49d9dd0f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_intrinsic_negative_count_le_grid_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_grid_mean_liminf_horizon_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_count_expectation_le_grid_liminf_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
/-- Actual separated negative source jump counts have finite expectation by Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ∂P) < ⊤ := by
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 T ×ˢ Iic (-ε))
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑ i ∈ Finset.range (n + 1),
    (if X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
        X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω < -ε / 2
     then (1 : ℝ≥0∞) else 0)
  let G : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑ i ∈ Finset.range (n + 1),
    (Iic (-(ε / 2))).indicator (fun _ : ℝ => (1 : ℝ≥0∞))
      (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
        X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω)
  have hXm (u : ℝ≥0) : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hMeas (n : ℕ) : Measurable (F n) := by
    dsimp [F]
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite
      (measurableSet_Iio.preimage ((hXm _).sub (hXm _)))
      measurable_const measurable_const
  have hPath (ω : Ω) :
      N ω ≤ Filter.liminf (fun n => F n ω) atTop := by
    simpa only [N, F] using
      (avram_p2_34dbea70_actual_original_intrinsic_negative_count_le_grid_liminf
        X ω T hT ε hε)
  have hFG (n : ℕ) (ω : Ω) : F n ω ≤ G n ω := by
    dsimp [F, G]
    apply Finset.sum_le_sum
    intro i hi
    let z : ℝ := X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
      X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω
    change (if z < -ε / 2 then (1 : ℝ≥0∞) else 0) ≤
      (Iic (-(ε / 2))).indicator (fun _ : ℝ => (1 : ℝ≥0∞)) z
    by_cases hz : z < -ε / 2
    · have hm : z ∈ Iic (-(ε / 2)) := by
        simpa only [Set.mem_Iic, neg_div] using (le_of_lt hz)
      simp only [if_pos hz, Set.indicator_of_mem hm, le_refl]
    · simp only [if_neg hz]
      exact zero_le
  obtain ⟨C, _, hGridBound⟩ :=
    avram_p2_34dbea70_actual_original_grid_mean_liminf_horizon_bound
      X T hT (ε / 2) (by positivity)
  have hMean : Filter.liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop ≤
      ENNReal.ofReal (C * (T : ℝ)) := by
    calc
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, G n ω ∂P) atTop :=
        Filter.liminf_le_liminf
          (Filter.Eventually.of_forall (fun n => lintegral_mono (hFG n)))
      _ ≤ _ := by simpa only [G, neg_div] using hGridBound
  have hBound :=
    avram_p2_34dbea70_actual_count_expectation_le_grid_liminf_mean
      P N F (ENNReal.ofReal (C * (T : ℝ))) hMeas hPath hMean
  change (∫⁻ ω, N ω ∂P) < ⊤
  exact lt_of_le_of_lt hBound ENNReal.ofReal_lt_top
