-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_postruin_uniform_floor_mask_eventually_false
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:13:43.919197+00:00
-- url     : https://prove2.me/submissions/04259894-f9ba-48fe-a3bf-3f9ccdc2ae67

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (T : ℝ) (hT : 0 < T) (t : ℝ≥0) (τ : ℝ≥0∞)
    (hτ : τ < (t : ℝ≥0∞)) :
    ∀ᶠ n in Filter.atTop,
      ¬ ((Real.toNNReal
        (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) /
          ((n : ℝ) + 2)) : ℝ≥0∞) < τ) := by
  have hRat : 0 ≤ (t : ℝ) / T :=
    div_nonneg t.property (le_of_lt hT)
  have hFloor :
      Tendsto (fun y : ℝ => (⌊((t : ℝ) / T) * y⌋₊ : ℝ) / y)
        atTop (𝓝 ((t : ℝ) / T)) :=
    tendsto_nat_floor_mul_div_atTop hRat
  have hShift : Tendsto (fun n : ℝ => n + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id
  have hScaled : Tendsto
      (fun n : ℝ =>
        T * ((⌊((t : ℝ) / T) * (n + 2)⌋₊ : ℝ) / (n + 2)))
      atTop (𝓝 (T * ((t : ℝ) / T))) := by
    simpa only [Function.comp_def] using (hFloor.comp hShift).const_mul T
  have hTval : T * ((t : ℝ) / T) = (t : ℝ) := by
    field_simp [ne_of_gt hT]
  have hReal : Tendsto
      (fun n : ℝ =>
        T * (⌊((t : ℝ) / T) * (n + 2)⌋₊ : ℝ) / (n + 2))
      atTop (𝓝 (t : ℝ)) := by
    simpa only [hTval, mul_div_assoc] using hScaled
  have hENN := ENNReal.tendsto_ofReal hReal
  have hτ' : τ < ENNReal.ofReal (t : ℝ) := by
    simpa [ENNReal.ofReal] using hτ
  filter_upwards [hENN.eventually (eventually_gt_nhds hτ')] with n hn
  exact not_lt_of_ge hn.le
