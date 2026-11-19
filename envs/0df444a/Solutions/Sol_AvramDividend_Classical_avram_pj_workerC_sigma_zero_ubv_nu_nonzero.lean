-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_sigma_zero_ubv_nu_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:29:41.773929+00:00
-- url     : https://prove2.me/submissions/54ce2fa3-336a-47c9-9131-1b9c7d6091d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    X.ν ≠ 0 := by
  intro hν
  exact (AvramDividend.Classical.avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded
    X hν hBV) hσ

