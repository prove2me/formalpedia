-- Prove2me | solution 1 for AvramDividend.Classical.avram_b188_original_random_physical_interval_actual_jump_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:40:21.257078+00:00
-- url     : https://prove2.me/submissions/cd8bf14d-94ca-4d62-9eb8-2fab885a9b27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the genuine spectrally negative Levy sample path, the event of an actual nonzero source jump in any half-open interval between measurable random clocks is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : Ω → ℝ≥0)
    (hs : Measurable s) (ht : Measurable t)
    (hst : ∀ ω, s ω ≤ t ω) :
    MeasurableSet {ω : Ω | ∃ u : ℝ≥0,
      s ω < u ∧ u ≤ t ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by
  let N : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s ω) (t ω) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  have hN (n : ℕ) : MeasurableSet {ω : Ω | N n ω ≠ 0} := by
    have hm :=
      avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
        X n s t hs ht
    exact (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage hm
  have hMark (ω : Ω) :
      (∃ u : ℝ≥0, s ω < u ∧ u ≤ t ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ↔
      (∃ n : ℕ, N n ω ≠ 0) := by
    constructor
    · rintro ⟨u, hsu, hut, hne⟩
      have hMarked : ∀ i ∈ ({0} : Finset ℕ), ∃ v : ℝ≥0,
          (fun _ : ℕ => s ω) i < v ∧
          v ≤ (fun _ : ℕ => t ω) i ∧
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0 := by
        intro i hi
        exact ⟨u, hsu, hut, hne⟩
      obtain ⟨n, hCut⟩ :=
        avram_b118_original_finite_physically_marked_cells_one_cutoff
          X ω ({0} : Finset ℕ) (fun _ => s ω) (fun _ => t ω) hMarked
      obtain ⟨v, hsv, hvt, hband⟩ := hCut 0 (by simp)
      exact ⟨n,
        (avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
          X ω (s ω) (t ω) (hst ω) n).mpr ⟨v, hsv, hvt, hband⟩⟩
    · rintro ⟨n, hn⟩
      obtain ⟨u, hsu, hut, hband⟩ :=
        (avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
          X ω (s ω) (t ω) (hst ω) n).mp hn
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨u, hsu, hut, by linarith⟩
  have hUnion : MeasurableSet
      (⋃ n : ℕ, {ω : Ω | N n ω ≠ 0}) :=
    MeasurableSet.iUnion hN
  have hEq : {ω : Ω | ∃ u : ℝ≥0,
      s ω < u ∧ u ≤ t ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} =
      ⋃ n : ℕ, {ω : Ω | N n ω ≠ 0} := by
    ext ω
    simpa only [Set.mem_setOf_eq, Set.mem_iUnion] using hMark ω
  rw [hEq]
  exact hUnion
