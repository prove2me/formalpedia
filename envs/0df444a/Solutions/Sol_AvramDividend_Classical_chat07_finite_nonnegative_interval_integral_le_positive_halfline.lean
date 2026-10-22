-- Prove2me | solution 1 for AvramDividend.Classical.chat07_finite_nonnegative_interval_integral_le_positive_halfline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:55:47.477166+00:00
-- url     : https://prove2.me/submissions/ca74cacb-57ad-46c3-963a-73e10770c87c

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

/-! A finite interval of a globally nonnegative integrable function is
bounded by its positive-halfline integral using set monotonicity. -/
theorem solution
    (g : ℝ → ℝ) (hg : IntegrableOn g (Ioi (0 : ℝ)))
    (hgnonneg : ∀ x : ℝ, 0 ≤ g x) (n : ℕ) :
    (∫ x in (1 : ℝ)..((n : ℝ) + 1), g x) ≤
      (∫ x in Ioi (0 : ℝ), g x) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsubset :
      Ioc (1 : ℝ) ((n : ℝ) + 1) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_trans (zero_lt_one : (0 : ℝ) < 1) hx.1
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g :=
    Filter.Eventually.of_forall hgnonneg
  have hsubset_ae :
      Ioc (1 : ℝ) ((n : ℝ) + 1) ≤ᵐ[volume] Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall (by
      intro x hx
      exact hsubset hx)
  rw [intervalIntegral.integral_of_le hn]
  exact MeasureTheory.setIntegral_mono_set hg hnonneg_ae hsubset_ae
