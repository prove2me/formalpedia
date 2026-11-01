-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:19:33.439987+00:00
-- url     : https://prove2.me/submissions/a6e4a52b-1181-41ce-87a4-65c4572ba395

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- On an actual admissible pre-ruin payment time, a discounted dividend
unit is bounded by the original source postpayment exponential test. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (q : ℝ) :
    Real.exp (-(q * (t : ℝ))) ≤
      Real.exp x * Real.exp
        (X.X t ω - rightLimit D t ω - (t : ℝ) * q) := by
  have hpay :
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by
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
  calc
    Real.exp (-(q * (t : ℝ))) ≤
        Real.exp (x + (X.X t ω - rightLimit D t ω - (t : ℝ) * q)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp x * Real.exp
          (X.X t ω - rightLimit D t ω - (t : ℝ) * q) := by
      rw [Real.exp_add]
