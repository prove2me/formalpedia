-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_true_localtime_positive_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:21:35.395986+00:00
-- url     : https://prove2.me/submissions/9877ed37-6b38-4dba-a97c-adab35a4f341

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A positive Esscher root forces the genuine running-record local time
to have positive mass at a fixed finite observation time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    0 < P {ω : Ω | 0 < runningSup X (1 : ℝ≥0) ω} := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hLap := X.laplace (1 : ℝ≥0) φ hφ.le
  have hMoment :
      (∫ ω, Real.exp (φ * X.X (1 : ℝ≥0) ω) ∂P) = Real.exp q := by
    have h := hLap.2
    change (∫ ω, Real.exp (φ * X.X (1 : ℝ≥0) ω) ∂P) =
      Real.exp ((1 : ℝ) * X.ψ φ) at h
    simpa [hroot] using h
  have hPositive : 0 < P {ω : Ω | 0 < X.X (1 : ℝ≥0) ω} := by
    by_contra hNotPositive
    have hZero : P {ω : Ω | 0 < X.X (1 : ℝ≥0) ω} = 0 :=
      bot_unique (not_lt.mp hNotPositive)
    have hNonpos : ∀ᵐ ω ∂P, X.X (1 : ℝ≥0) ω ≤ 0 := by
      have hAE : ∀ᵐ ω ∂P, ¬ 0 < X.X (1 : ℝ≥0) ω := by
        exact (ae_iff).2 (by simpa using hZero)
      filter_upwards [hAE] with ω hw
      exact le_of_not_gt hw
    have hBound : ∀ᵐ ω ∂P,
        Real.exp (φ * X.X (1 : ℝ≥0) ω) ≤ 1 := by
      filter_upwards [hNonpos] with ω hw
      have hprod : φ * X.X (1 : ℝ≥0) ω ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hφ.le hw
      simpa using (Real.exp_le_exp.mpr hprod)
    have hIntLe :
        (∫ ω, Real.exp (φ * X.X (1 : ℝ≥0) ω) ∂P) ≤ 1 := by
      calc
        _ ≤ ∫ _ : Ω, (1 : ℝ) ∂P :=
          integral_mono_ae hLap.1 (integrable_const _) hBound
        _ = 1 := by simp
    rw [hMoment] at hIntLe
    have hExpGt : (1 : ℝ) < Real.exp q := by
      simpa using (Real.exp_lt_exp.mpr hq)
    exact (not_le_of_gt hExpGt) hIntLe
  have hIncl :
      {ω : Ω | 0 < X.X (1 : ℝ≥0) ω} ⊆
        {ω : Ω | 0 < runningSup X (1 : ℝ≥0) ω} := by
    intro ω hw
    exact lt_of_lt_of_le hw ((runningSup_monotone_and_path_le X ω).2 1)
  exact lt_of_lt_of_le hPositive (measure_mono hIncl)
