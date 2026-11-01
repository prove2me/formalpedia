-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actualStopped_theta_exponential_payment_kernel_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:18:29.712645+00:00
-- url     : https://prove2.me/submissions/96e4e4cd-0b67-4c4a-8337-4a05e1f81679

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Actual source postpayment solvency yields exponential domination at
every payment time, including the first right dividend atom, for θ>0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) ≤
      Real.exp (θ * x) * Real.exp
        (θ * (X.X t ω - rightLimit D t ω) - (t : ℝ) * q) := by
  have hpay : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by
    change 0 ≤ (t : ℝ) ∧
      ((t : ℝ) = 0 ∨ ENNReal.ofReal (t : ℝ) < ruinTime X x D ω) at ht
    rcases ht.2 with hz | hs
    · left
      exact_mod_cast hz
    · right
      simpa using hs
  have hsolv : 0 ≤ x + X.X t ω - rightLimit D t ω := by
    by_cases hz : t = 0
    · subst t
      have hinit := hD.1.2 ω 0 (Or.inl rfl)
      change rightLimit D 0 ω - D 0 ω ≤
        x + X.X 0 ω - D 0 ω at hinit
      have hD0 := hD.1.1.1 ω
      rw [X.X_zero ω, hD0] at hinit
      rw [X.X_zero ω]
      linarith
    · have htpos : 0 < t := pos_iff_ne_zero.mpr hz
      exact (capped_postPaymentReserve_within_cap_before_ruin
        X x C D hD ω t htpos (hpay.resolve_left hz)).1
  have hscaled : 0 ≤ θ * (x + X.X t ω - rightLimit D t ω) :=
    mul_nonneg (le_of_lt hθ) hsolv
  calc
    Real.exp (-(q * (t : ℝ))) ≤
      Real.exp (θ * x +
        (θ * (X.X t ω - rightLimit D t ω) - (t : ℝ) * q)) :=
        Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_add]
