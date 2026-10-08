-- Prove2me | solution 1 for AvramDividend.Classical.standing_bv_levy_absolutely_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:04:28.782962+00:00
-- url     : https://prove2.me/submissions/235ac3c0-744a-4456-ac93-66d02caff3e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation) :
    X.ν ≪ volume := by
  have h33 : X.Condition33 := hX.2.2
  unfold SpectrallyNegativeLevy.Condition33 at h33
  rcases h33 with hσ | hvar | hac
  · have hnσ : ¬ 0 < X.σ := by
      rw [hbv.1]
      exact lt_irrefl 0
    exact (hnσ hσ).elim
  · have hfinite :
        (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) ≠ ⊤ :=
      ne_of_lt hbv.2
    exact (hfinite hvar).elim
  · exact hac
