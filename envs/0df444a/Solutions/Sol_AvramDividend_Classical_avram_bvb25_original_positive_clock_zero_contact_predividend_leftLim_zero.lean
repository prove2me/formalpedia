-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb25_original_positive_clock_zero_contact_predividend_leftLim_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:55:10.27942+00:00
-- url     : https://prove2.me/submissions/aac0f052-4472-4065-8ecd-243d5cea174a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hSource : ∀ s : ℝ≥0, s ≤ S →
      X.X s ω = (s : ℝ) * X.drift)
    (hZero : ∀ s : ℝ≥0, s ≤ S →
      riskProcess X x D s ω = 0) :
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t = 0  := by
  have hnb : (nhdsWithin t (Iio t)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  exact avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
    X x C D hD ω S t ht hnb hSource hZero
