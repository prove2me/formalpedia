-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_drift_deficit_increment_strict_ae
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:42:55.116978+00:00
-- url     : https://prove2.me/submissions/8a1b1c38-d05d-495d-8661-1a73077c2b37

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_increment_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ ω ∂P,
      X.drift * (s : ℝ) - X.X s ω <
        X.drift * (t : ℝ) - X.X t ω := by
  haveI := X.isProbability
  have h0 := bv_infinite_activity_drift_deficit_increment_zero_atom X hBV hνinf s t hst
  rw [measureReal_eq_zero_iff] at h0
  have hne : ∀ᵐ ω ∂P, (X.drift * (t : ℝ) - X.X t ω) - (X.drift * (s : ℝ) - X.X s ω) ≠ 0 := by
    rw [ae_iff]; simpa using h0
  filter_upwards [hne, bv_drift_deficit_ae_monotone_all_times X hBV] with ω h1 h2
  have := h2 hst.le
  simp only at this
  exact lt_of_le_of_ne this (fun e => h1 (by rw [e]; ring))
