-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T18:24:53.658943+00:00
-- url     : https://prove2.me/submissions/5edceefb-da1f-47c1-b29b-cb38a5b4acd1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_all_nonzero_marks_locally_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_mark_maps_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      {u : ℝ≥0 | 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}.Finite := by
  classical
  have hAll :=
    avram_ubv_mixed12_original_finite_activity_all_nonzero_marks_locally_finite_ae
      X hFinite
  filter_upwards [hAll] with ω hω
  intro t
  let jump : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let mark : ℝ≥0 → ℝ≥0 × ℝ := fun u => (u, jump u)
  let S : Set ℝ≥0 := {u | 0 < u ∧ jump u ≠ 0}
  let T : Set ℝ≥0 := {u | 0 < u ∧ u ≤ t ∧ jump u ≠ 0}
  have hMarkMeas : Measurable mark := by
    simpa [mark, jump] using
      (avram_bv_jump8_original_frozen_mark_maps_measurable X ω 0).1
  have hZeroMeas : MeasurableSet ({0} : Set ℝ) :=
    measurableSet_singleton (0 : ℝ)
  have hBoxMeas :
      MeasurableSet (Ioc (0 : ℝ≥0) t ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hSMeas : MeasurableSet S := by
    change MeasurableSet
      (Ioi (0 : ℝ≥0) ∩ jump ⁻¹' ({0}ᶜ : Set ℝ))
    exact measurableSet_Ioi.inter
      (hZeroMeas.compl.preimage hMarkMeas.snd)
  have hSet : mark ⁻¹' (Ioc (0 : ℝ≥0) t ×ˢ (Set.univ : Set ℝ)) ∩ S = T := by
    ext u
    simp [mark, S, T, and_assoc, and_left_comm, and_comm]
  have hTMeas : MeasurableSet T := by
    rw [← hSet]
    exact (hBoxMeas.preimage hMarkMeas).inter hSMeas
  have hMap : ((Measure.count.restrict S).map mark)
      (Ioc 0 t ×ˢ (Set.univ : Set ℝ)) < ⊤ := by
    simpa [S, mark, jump] using hω t
  rw [Measure.map_apply hMarkMeas hBoxMeas] at hMap
  rw [Measure.restrict_apply
    (hBoxMeas.preimage hMarkMeas)] at hMap
  rw [hSet] at hMap
  have hCo : (T.encard : ℝ≥0∞) < ⊤ := by
    simpa only [Measure.count_apply hTMeas] using hMap
  have hCard : T.encard < ⊤ := by
    by_contra hn
    have htop : T.encard = ⊤ := eq_top_iff.mpr (le_of_not_gt hn)
    simpa [htop] using hCo
  exact Set.encard_lt_top_iff.mp hCard
