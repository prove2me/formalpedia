-- Prove2me | solution 1 for AvramDividend.Classical.avram_b116_original_all_negative_cutoff_jump_time_sets_union_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:25:44.032717+00:00
-- url     : https://prove2.me/submissions/a80e17cd-a243-4a1f-b720-51cde293519b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original all-negative band cutoff sets exhaust exactly the physical nonzero jump times, for every original path and interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    (⋃ n : ℕ, {u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}) =
    {u : ℝ≥0 | s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hsu, hut, hband⟩
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨hsu, hut, by linarith⟩
  · rintro ⟨hsu, hut, hne⟩
    have hz : (0 : ℝ≥0) ≤ s := zero_le
    have hu : 0 < u := lt_of_le_of_lt hz hsu
    have hleft :=
      (avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω).1 u
    have hnonpos : X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 :=
      sub_nonpos.mpr (X.noPosJumps ω u _ hu hleft)
    have hneg : X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 :=
      lt_of_le_of_ne hnonpos hne
    have hlim : Tendsto
        (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have he : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / ((n : ℝ) + 1) <
        -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) :=
      hlim.eventually (isOpen_Iio.mem_nhds (neg_pos.mpr hneg))
    obtain ⟨n, hn⟩ := he.exists
    refine ⟨n, hsu, hut, ?_⟩
    linarith
