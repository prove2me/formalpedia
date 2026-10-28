-- Prove2me | solution 1 for AvramDividend.Classical.chat01_fixed_horizon_upcrossing_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:42:03.727754+00:00
-- url     : https://prove2.me/submissions/311d80b0-a673-4af7-8808-0880536902f6

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_probability_explicit_tail
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- All measurable upward passages by a fixed time have arbitrarily small
    probability uniformly for sufficiently large barriers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (t ε : ℝ) (hε : 0 < ε) :
    ∃ z0 : ℝ, ∀ z : ℝ, z0 ≤ z → 0 ≤ z →
      ∀ A : Set Ω, MeasurableSet A →
        A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)} →
        (∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t) →
        P A ≤ ENNReal.ofReal ε := by
  refine ⟨(q * t - Real.log ε) / φ + 1, ?_⟩
  intro z hz hz0 A hAmeas hA htime
  have hφne : φ ≠ 0 := ne_of_gt hφ
  have hcancel :
      φ * ((q * t - Real.log ε) / φ) =
        q * t - Real.log ε := by
    field_simp [hφne]
  have hmul :
      φ * ((q * t - Real.log ε) / φ + 1) ≤ φ * z :=
    mul_le_mul_of_nonneg_left hz (le_of_lt hφ)
  rw [mul_add, hcancel, mul_one] at hmul
  have hexp : Real.exp (q * t - φ * z) ≤ ε := by
    calc
      Real.exp (q * t - φ * z) ≤ Real.exp (Real.log ε) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = ε := Real.exp_log hε
  exact (chat01_finite_horizon_upcrossing_probability_explicit_tail
    X q hq φ hφ hroot z hz0 A hAmeas hA t htime).trans
      (ENNReal.ofReal_le_ofReal hexp)
