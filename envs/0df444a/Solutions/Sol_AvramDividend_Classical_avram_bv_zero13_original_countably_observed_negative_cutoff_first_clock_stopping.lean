-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_countably_observed_negative_cutoff_first_clock_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T10:19:01.257922+00:00
-- url     : https://prove2.me/submissions/09fd8349-e3e5-4949-a416-bb00206b1771

import Mathlib
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! The actual original marked past-count determines an observed jump clock.
    Every observation gate is in its own right-continuous history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (r : ℕ → ℝ≥0) :
    let pastCount : ℕ → ℕ → Ω → ℝ :=
      fun n k ω =>
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 =>
            (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (r k) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => ⨅ n : ℕ, ⨅ k : ℕ,
        if 0 < pastCount n k ω
        then (r k : WithTop ℝ≥0) else ⊤) := by
  classical
  let pastCount : ℕ → ℕ → Ω → ℝ := fun n k ω =>
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (r k) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change IsStoppingTime 𝓕.rightCont
    (fun ω : Ω => ⨅ n : ℕ, ⨅ k : ℕ,
      if 0 < pastCount n k ω then (r k : WithTop ℝ≥0) else ⊤)
  have hsingle (n k : ℕ) : IsStoppingTime 𝓕.rightCont
      (fun ω : Ω =>
        if 0 < pastCount n k ω then (r k : WithTop ℝ≥0) else ⊤) := by
    have hm : Measurable[𝓕.rightCont (r k)] (pastCount n k) :=
      (avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted
        X (r k) n).measurable
    have hA : MeasurableSet[𝓕.rightCont (r k)]
        {ω : Ω | 0 < pastCount n k ω} :=
      hm measurableSet_Ioi
    intro t
    by_cases hrt : r k ≤ t
    · have hinc : 𝓕.rightCont (r k) ≤ 𝓕.rightCont t :=
        (𝓕.rightCont).mono hrt
      have hAt : MeasurableSet[𝓕.rightCont t]
          {ω : Ω | 0 < pastCount n k ω} := hinc _ hA
      convert hAt using 1
      ext ω
      by_cases hω : 0 < pastCount n k ω
      · simpa [hω] using (WithTop.coe_le_coe.mpr hrt)
      · have hnot : ¬ ((⊤ : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) := by
          intro htop
          have heq : (t : WithTop ℝ≥0) = ⊤ := top_unique htop
          exact (WithTop.coe_ne_top : (t : WithTop ℝ≥0) ≠ ⊤) heq
        simpa [hω] using hnot
    · have hempty :
          {ω : Ω |
            (if 0 < pastCount n k ω
             then (r k : WithTop ℝ≥0) else ⊤) ≤ t} = (∅ : Set Ω) := by
        ext ω
        by_cases hω : 0 < pastCount n k ω
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
  exact IsStoppingTime.iInf (fun n => IsStoppingTime.iInf (hsingle n))
