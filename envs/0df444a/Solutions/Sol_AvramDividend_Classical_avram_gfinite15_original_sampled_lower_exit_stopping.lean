-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite15_original_sampled_lower_exit_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:09:08.98043+00:00
-- url     : https://prove2.me/submissions/8184d78b-9ae1-4031-acd1-23200d562154

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (δ : ℝ) :
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤) := by
  classical
  have hsingle (k : ℕ) : IsStoppingTime 𝓕.rightCont
      (fun ω : Ω =>
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤) := by
    have hmeas : Measurable[𝓕.rightCont (r k)]
        (fun ω : Ω => x + X.X (r k) ω - rightLimit D (r k) ω) :=
      (postPaymentReserve_cadlag_adapted X x D hD).2.2 (r k)
    have hA : MeasurableSet[𝓕.rightCont (r k)]
        {ω : Ω | x + X.X (r k) ω - rightLimit D (r k) ω < δ} :=
      hmeas measurableSet_Iio
    intro t
    by_cases hrt : r k ≤ t
    · have hinc : 𝓕.rightCont (r k) ≤ 𝓕.rightCont t :=
        (𝓕.rightCont).mono hrt
      have hAt : MeasurableSet[𝓕.rightCont t]
          {ω : Ω | x + X.X (r k) ω - rightLimit D (r k) ω < δ} :=
        hinc _ hA
      convert hAt using 1
      ext ω
      by_cases hω : x + X.X (r k) ω - rightLimit D (r k) ω < δ
      · simpa [hω] using (WithTop.coe_le_coe.mpr hrt)
      · have hnot : ¬ ((⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) := by
          intro htop
          have heq : (t : WithTop ℝ≥0) = ⊤ := top_unique htop
          exact (WithTop.coe_ne_top : (t : WithTop ℝ≥0) ≠ ⊤) heq
        simpa [hω] using hnot
    · have hempty :
        {ω : Ω | (if x + X.X (r k) ω - rightLimit D (r k) ω < δ
          then (r k : WithTop ℝ≥0) else ⊤) ≤ t} = (∅ : Set Ω) := by
        ext ω
        by_cases hω : x + X.X (r k) ω - rightLimit D (r k) ω < δ
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
