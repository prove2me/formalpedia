-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a67_original_strict_positive_uniform_clock_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:17:17.743879+00:00
-- url     : https://prove2.me/submissions/cb5c99f6-bc31-48cf-8245-8a2756d5f1b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ => Real.toNNReal (T - T / ((n : ℝ) + 2)))
      atTop (𝓝[<] (⟨T, le_of_lt hT⟩ : ℝ≥0)) := by
  have hOne : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2))
      atTop (𝓝 0) := by
    convert (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1) using 1
    funext n
    congr 1
    push_cast
    ring
  have hδ : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => T) atTop (𝓝 T)).mul hOne)
  have hReal : Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 2))
      atTop (𝓝 T) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => T) atTop (𝓝 T)).sub hδ)
  apply (tendsto_nhdsWithin_iff).2
  constructor
  · have hTo := (continuous_real_toNNReal.tendsto T).comp hReal
    have hEq : Real.toNNReal T = (⟨T, le_of_lt hT⟩ : ℝ≥0) := by
      apply Subtype.ext
      exact Real.coe_toNNReal T (le_of_lt hT)
    rw [hEq] at hTo
    simpa only [Function.comp_def] using hTo
  · filter_upwards [] with n
    change Real.toNNReal (T - T / ((n : ℝ) + 2)) <
      (⟨T, le_of_lt hT⟩ : ℝ≥0)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm : (1 : ℝ) < (n : ℝ) + 2 := by linarith
    have hpos := sub_pos.mpr (div_lt_self hT hm)
    apply (Real.toNNReal_lt_iff_lt_coe (le_of_lt hpos)).2
    change T - T / ((n : ℝ) + 2) < T
    have hsmall : 0 < T / ((n : ℝ) + 2) := by positivity
    linarith
