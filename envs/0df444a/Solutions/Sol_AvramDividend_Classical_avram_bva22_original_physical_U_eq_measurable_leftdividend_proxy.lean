-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva22_original_physical_U_eq_measurable_leftdividend_proxy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:25:11.381341+00:00
-- url     : https://prove2.me/submissions/e3be951b-87cd-41f6-8e8f-15d65ea40f2b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The exact zero-jump prepayment reserve is linear drift minus measurable dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (htpos : 0 < t)
    (hsource : ∀ r : ℝ≥0, r ≤ S → X.X r ω = (r : ℝ) * X.drift) :
    Function.leftLim (fun r : ℝ≥0 =>
      x + X.X r ω - rightLimit D r ω) t =
    x + (t : ℝ) * X.drift -
      Function.leftLim (fun r : ℝ≥0 => rightLimit D r ω) t := by
  have hnb : (nhdsWithin t (Iio t)).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have hU := avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
    X x C D hD ω S t ht hnb hsource
  have hDlim := avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
    X x C D hD ω t hnb
  rw [hDlim]
  exact hU
