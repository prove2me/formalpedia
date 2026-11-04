-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_negative_tail_uniform_width_probability_O
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:43:31.00374+00:00
-- url     : https://prove2.me/submissions/7b950705-6ba9-457e-8911-06c692c9029b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_negative_tail_unweighted_linear_smalltime_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original-process negative-tail bound applies eventually at
every width of a uniform finite-horizon time mesh. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        P {ω : Ω | X.X (T / ((n : ℝ≥0) + 1)) ω ≤ -ε} ≤
          ENNReal.ofReal (C * ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    avram_p2_original_negative_tail_unweighted_linear_smalltime_bound X ε hε
  have hreal : Tendsto
      (fun n : ℕ => ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, NNReal.coe_zero] using
      (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).comp
        (avram_p2_34dbea70_uniform_time_mesh_width_tendsto_zero T)
  have hpositive : ∀ n : ℕ,
      (0 : ℝ) < ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) := by
    intro n
    have hden : (0 : ℝ≥0) < (n : ℝ≥0) + 1 := by positivity
    exact_mod_cast (div_pos hT hden)
  have hwithin : Tendsto
      (fun n : ℕ => ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ))
      atTop (nhdsWithin (0 : ℝ) (Ioi 0)) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨hreal, Filter.Eventually.of_forall (fun n => hpositive n)⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hwithin.eventually hbound] with n hn
  simpa only [Real.toNNReal_coe] using hn
