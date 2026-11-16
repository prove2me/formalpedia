-- Prove2me | solution 1 for AvramDividend.Classical.avram_b26_event_centered_two_gain_cash_gap_no_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:37:00.697657+00:00
-- url     : https://prove2.me/submissions/f0a2224b-937d-4d00-96be-454e63dbc022

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b26_positive_event_cash_gap_forces_signed_L1_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (F : Ω → ℝ)
    (b δ : ℝ) (hδ : 0 < δ)
    (G J Err : ℕ → Ω → ℝ)
    (hEI : ∀ n, Integrable (Err n) P)
    (hGap : b + δ ≤ ∫ ω in A, F ω ∂P)
    (hGC : ∀ n, (∫ ω in A, G n ω ∂P) = 0)
    (hJC : ∀ n, (∫ ω in A, J n ω ∂P) = 0)
    (hLedger : ∀ n,
      (∫ ω in A, F ω ∂P) ≤
        b + (∫ ω in A, G n ω ∂P) +
          (∫ ω in A, J n ω ∂P) +
          (∫ ω in A, Err n ω ∂P))
    (hErrorZero : Tendsto
      (fun n => ∫ ω, ‖Err n ω‖ ∂P) atTop (𝓝 (0 : ℝ))) :
    False := by
  have hCash' (n : ℕ) :
      (∫ ω in A, F ω ∂P) ≤ b + (∫ ω in A, Err n ω ∂P) := by
    have hLedgerN := hLedger n
    rw [hGC n, hJC n] at hLedgerN
    linarith
  have hLower :=
    avram_b26_positive_event_cash_gap_forces_signed_L1_error
      P A F b δ hδ Err hEI hGap hCash'
  have hSmall :
      ∀ᶠ n in atTop, (∫ ω, ‖Err n ω‖ ∂P) < δ :=
    hErrorZero.eventually (eventually_lt_nhds hδ)
  obtain ⟨n, hn⟩ := hSmall.exists
  exact (not_lt_of_ge (hLower n)) hn
