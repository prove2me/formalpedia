-- Prove2me | solution 1 for AvramDividend.Classical.avram_b118_original_finite_physically_marked_cells_one_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T17:32:25.205203+00:00
-- url     : https://prove2.me/submissions/906ac7bc-0d47-4d95-9097-9097102eb871

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One negative cutoff simultaneously detects every genuinely marked original physical cell in a finite stopped-grid family. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hMarked : ∀ i ∈ S, ∃ u : ℝ≥0,
      s i < u ∧ u ≤ t i ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) :
    ∃ n : ℕ, ∀ i ∈ S, ∃ u : ℝ≥0,
      s i < u ∧ u ≤ t i ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1)) := by
  classical
  let C : ℕ → ℕ → Prop := fun n i => ∃ u : ℝ≥0,
    s i < u ∧ u ≤ t i ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))
  have hMono : ∀ i n m, n ≤ m → C n i → C m i := by
    intro i n m hnm hC
    obtain ⟨u, hsu, hut, hband⟩ := hC
    have hSub :=
      avram_b115_original_random_interval_negative_mark_cutoff_sets_monotone
        X ω (s i) (t i) n m hnm
    exact ⟨u, (hSub ⟨hsu, hut, hband⟩).1,
      (hSub ⟨hsu, hut, hband⟩).2.1,
      (hSub ⟨hsu, hut, hband⟩).2.2⟩
  have hCover : ∀ i ∈ S, ∃ n : ℕ, C n i := by
    intro i hi
    obtain ⟨u, hsu, hut, hne⟩ := hMarked i hi
    have hz : (0 : ℝ≥0) ≤ s i := zero_le
    have hu : 0 < u := lt_of_le_of_lt hz hsu
    have hleft :=
      (avram_p2_a_zero_rate_original_cadlag_regular_all_times X ω).1 u
    have hjle : X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 :=
      sub_nonpos.mpr (X.noPosJumps ω u _ hu hleft)
    have hjneg : X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0 :=
      lt_of_le_of_ne hjle hne
    have hlim : Tendsto
        (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have he : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / ((n : ℝ) + 1) <
        -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) :=
      hlim.eventually (isOpen_Iio.mem_nhds (neg_pos.mpr hjneg))
    obtain ⟨n, hn⟩ := he.exists
    refine ⟨n, u, hsu, hut, ?_⟩
    linarith
  have hAux : ∀ T : Finset ℕ,
      (∀ i ∈ T, ∃ n : ℕ, C n i) →
      ∃ n : ℕ, ∀ i ∈ T, C n i := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨0, by simp⟩
    | @insert a T ha ih =>
        intro hT
        have hTa : ∃ n : ℕ, C n a := hT a (by simp)
        have hTsmall : ∀ i ∈ T, ∃ n : ℕ, C n i := by
          intro i hi
          exact hT i (Finset.mem_insert_of_mem hi)
        obtain ⟨n, hn⟩ := ih hTsmall
        obtain ⟨m, hm⟩ := hTa
        refine ⟨max n m, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact hMono i m (max n m) (le_max_right _ _) hm
        · exact hMono i n (max n m) (le_max_left _ _) (hn i hi')
  exact hAux S hCover
