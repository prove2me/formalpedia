-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_finite_zero_original_fixed_clock_drift_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:01:28.500908+00:00
-- url     : https://prove2.me/submissions/676bf561-6e6e-48f1-be9f-c6d29e55c3d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_stopping_future_nojump_drift_probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hZero : X.ν (Iio (0 : ℝ)) = 0) (t : ℝ≥0) :
    P.real {ω : Ω | X.X t ω = (t : ℝ) * X.drift} = 1 := by
  classical
  have hstop : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s]
        {ω : Ω | (fun _ : Ω => (0 : ℝ≥0)) ω ≤ s} := by
    intro s
    simpa using
      (MeasurableSet.univ :
        MeasurableSet[𝓕.rightCont s] (Set.univ : Set Ω))
  have h :=
    AvramDividend.Classical.avram_bv_zero13_original_stopping_future_nojump_drift_probability
      X hBV hFinite (fun _ : Ω => (0 : ℝ≥0)) hstop t
  have hforward :
      P.real {ω : Ω | (t : ℝ) * X.drift = X.X t ω} = 1 := by
    simpa [hZero, X.X_zero, sub_eq_zero] using h
  have hset :
      {ω : Ω | X.X t ω = (t : ℝ) * X.drift} =
        {ω : Ω | (t : ℝ) * X.drift = X.X t ω} := by
    ext ω
    exact eq_comm
  rw [hset]
  exact hforward
