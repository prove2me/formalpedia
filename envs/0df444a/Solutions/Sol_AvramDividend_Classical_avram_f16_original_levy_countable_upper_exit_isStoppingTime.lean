-- Prove2me | solution 1 for AvramDividend.Classical.avram_f16_original_levy_countable_upper_exit_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:20:42.759222+00:00
-- url     : https://prove2.me/submissions/17da8035-2fb1-41d8-b643-b3fe1aedb24a

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℕ → ℝ≥0) (upper : ℝ) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ⨅ j : ℕ,
        if upper < X.X (r j) ω
        then (r j : WithTop ℝ≥0) else ⊤) := by
  classical
  have hsingle (j : ℕ) : IsStoppingTime 𝓕.rightCont
      (fun ω : Ω =>
        if upper < X.X (r j) ω
        then (r j : WithTop ℝ≥0) else ⊤) := by
    have hmeas : Measurable[𝓕.rightCont (r j)]
        (fun ω : Ω => X.X (r j) ω) :=
      (X.adapted (r j)).mono (𝓕.le_rightCont (r j)) le_rfl
    have hA : MeasurableSet[𝓕.rightCont (r j)]
        {ω : Ω | upper < X.X (r j) ω} :=
      hmeas measurableSet_Ioi
    intro t
    by_cases hrt : r j ≤ t
    · have hinc : 𝓕.rightCont (r j) ≤ 𝓕.rightCont t :=
        (𝓕.rightCont).mono hrt
      have hAt : MeasurableSet[𝓕.rightCont t]
          {ω : Ω | upper < X.X (r j) ω} :=
        hinc _ hA
      convert hAt using 1
      ext ω
      by_cases hω : upper < X.X (r j) ω
      · simpa [hω] using (WithTop.coe_le_coe.mpr hrt)
      · have hnot :
            ¬ ((⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) := by
          intro htop
          have heq : (t : WithTop ℝ≥0) = ⊤ := top_unique htop
          exact (WithTop.coe_ne_top : (t : WithTop ℝ≥0) ≠ ⊤) heq
        simpa [hω] using hnot
    · have hempty :
          {ω : Ω | (if upper < X.X (r j) ω
            then (r j : WithTop ℝ≥0) else ⊤) ≤ t} =
          (∅ : Set Ω) := by
        ext ω
        by_cases hω : upper < X.X (r j) ω
        · have hnot :
              ¬ ((r j : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) := by
            intro h
            exact hrt (WithTop.coe_le_coe.mp h)
          simpa [hω] using hnot
        · have hnot :
              ¬ ((⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) := by
            intro htop
            have heq : (t : WithTop ℝ≥0) = ⊤ := top_unique htop
            exact (WithTop.coe_ne_top : (t : WithTop ℝ≥0) ≠ ⊤) heq
          simpa [hω] using hnot
      rw [hempty]
      exact @MeasurableSet.empty Ω (𝓕.rightCont t)
  exact IsStoppingTime.iInf hsingle
