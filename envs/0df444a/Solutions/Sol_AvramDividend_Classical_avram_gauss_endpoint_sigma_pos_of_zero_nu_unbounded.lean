-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_endpoint_sigma_pos_of_zero_nu_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:11:02.744268+00:00
-- url     : https://prove2.me/submissions/03475289-41b4-48cf-9e83-9a9cfb37e011

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
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation) :
    0 < X.σ := by
  have hσ : X.σ ≠ 0 :=
    avram_gauss_endpoint_sigma_ne_zero_of_zero_nu_unbounded X hν hBV
  exact lt_of_le_of_ne X.σ_nonneg (Ne.symm hσ)
