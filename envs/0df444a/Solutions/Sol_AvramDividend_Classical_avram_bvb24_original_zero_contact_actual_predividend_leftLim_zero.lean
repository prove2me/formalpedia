-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:46:15.335918+00:00
-- url     : https://prove2.me/submissions/b560350d-eea0-483c-bfa5-9e84805cce82

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
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
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S)
    (hnb : (nhdsWithin t (Iio t)).NeBot)
    (hSource : ∀ s : ℝ≥0, s ≤ S →
      X.X s ω = (s : ℝ) * X.drift)
    (hZero : ∀ s : ℝ≥0, s ≤ S →
      riskProcess X x D s ω = 0) :
    Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t = 0  := by
  have hPre :=
    avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
      X x C D hD ω S t ht hnb hSource
  have hLeft :
      Function.leftLim (fun s : ℝ≥0 => D s ω) t = D t ω :=
    (hD.1.1.2.2.1 ω t).leftLim_eq
  rw [hPre, hLeft]
  have hR := hZero t ht
  change x + X.X t ω - D t ω = 0 at hR
  simpa only [hSource t ht] using hR
