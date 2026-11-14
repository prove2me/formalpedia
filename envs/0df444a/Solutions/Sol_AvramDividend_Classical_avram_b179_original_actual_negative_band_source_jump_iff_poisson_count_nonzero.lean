-- Prove2me | solution 1 for AvramDividend.Classical.avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:44:13.967351+00:00
-- url     : https://prove2.me/submissions/40d208a7-1845-4416-90db-41fd959523ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original negative-band jump measure of any ordered physical half-open source interval is nonzero exactly when that actual source interval contains a jump in the same negative mark band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ) :
    (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1))))) ≠ 0 ↔
    ∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)) := by
  classical
  let S : Set ℝ≥0 := {u : ℝ≥0 | s < u ∧ u ≤ t ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((n : ℝ) + 1))}
  have hFinite : S.Finite := by
    have ht :=
      avram_wave7_06_original_negative_band_marked_times_finite X ω t n
    apply ht.subset
    intro u hu
    have hz : (0 : ℝ≥0) ≤ s := zero_le
    exact ⟨lt_of_le_of_lt hz hu.1, hu.2.1, hu.2.2⟩
  have hEq :
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1))))) =
      (S.ncard : ℝ≥0∞) := by
    simpa only [S] using
      avram_p2_e_compensator_original_interval_negative_band_count_ncard
        X ω s t hst n
  change _ ≠ 0 ↔ S.Nonempty
  rw [hEq]
  constructor
  · intro hne
    by_contra hempty
    have hs : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    simp [hs] at hne
  · intro hnonempty
    have hpos : 0 < S.ncard := (Set.ncard_pos hFinite).mpr hnonempty
    exact_mod_cast (Nat.ne_of_gt hpos)
