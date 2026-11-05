-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_countable_exterior_observation_inf_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:14:00.088195+00:00
-- url     : https://prove2.me/submissions/db1f0e9e-b164-46f3-90b0-d8710157d4df

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) := by
  classical
  have hsingle (k : ℕ) : IsStoppingTime 𝓕.rightCont
      (fun ω : Ω =>
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) := by
    have hmeas : Measurable[𝓕.rightCont (r k)]
        (fun ω : Ω => x + X.X (r k) ω - rightLimit D (r k) ω) :=
      (postPaymentReserve_cadlag_adapted X x D hD).2.2 (r k)
    have hA : MeasurableSet[𝓕.rightCont (r k)]
        {ω : Ω | x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
          upper < x + X.X (r k) ω - rightLimit D (r k) ω} := by
      exact (hmeas measurableSet_Iio).union (hmeas measurableSet_Ioi)
    intro t
    by_cases hrt : r k ≤ t
    · have hinc : 𝓕.rightCont (r k) ≤ 𝓕.rightCont t :=
        (𝓕.rightCont).mono hrt
      have hAt : MeasurableSet[𝓕.rightCont t]
          {ω : Ω | x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω} :=
        hinc _ hA
      convert hAt using 1
      ext ω
      by_cases hω : x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
          upper < x + X.X (r k) ω - rightLimit D (r k) ω
      · simpa [hω] using (WithTop.coe_le_coe.mpr hrt)
      · have hnot : ¬ ((⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) := by
          intro htop
          have heq : (t : WithTop ℝ≥0) = ⊤ := top_unique htop
          exact (WithTop.coe_ne_top : (t : WithTop ℝ≥0) ≠ ⊤) heq
        simpa [hω] using hnot
    · have hempty :
        {ω : Ω | (if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) ≤ t} = (∅ : Set Ω) := by
        ext ω
        by_cases hω : x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        · have hnot : ¬ ((r k : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) := by
            intro h
            exact hrt (WithTop.coe_le_coe.mp h)
          simpa [hω] using hnot
        · have hnot : ¬ ((⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) := by
            intro htop
            have heq : (t : WithTop ℝ≥0) = ⊤ := top_unique htop
            exact (WithTop.coe_ne_top : (t : WithTop ℝ≥0) ≠ ⊤) heq
          simpa [hω] using hnot
      rw [hempty]
      exact @MeasurableSet.empty Ω (𝓕.rightCont t)
  exact IsStoppingTime.iInf hsingle