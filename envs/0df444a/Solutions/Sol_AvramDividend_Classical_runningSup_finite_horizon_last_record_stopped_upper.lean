-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_finite_horizon_last_record_stopped_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:13:03.385161+00:00
-- url     : https://prove2.me/submissions/349f9a15-b097-4e43-9698-b10cb81ef006

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_firstRecord_grid_finite_clocks_realisable_before_horizon
import Theorems.Thm_AvramDividend_Classical_runningSup_finite_record_cells_with_terminal_discount_upper
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q b h : ℝ)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 < h)
    (N : ℕ) (t : ℝ≥0)
    (hN : (⨅ (r : ℝ≥0)
      (_ : b + (N : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) <
      (t : ℝ≥0∞))
    (hnext : ¬ (⨅ (r : ℝ≥0)
      (_ : b + ((N + 1 : ℕ) : ℝ) * h < X.X r ω),
      (r : ℝ≥0∞)) < (t : ℝ≥0∞))
    (htτ : (t : ℝ≥0∞) < τ) :
    ∃ u : ℕ → ℝ≥0,
      (∀ k : ℕ, k ≤ N →
        (u k : ℝ≥0∞) =
          (⨅ (r : ℝ≥0)
            (_ : b + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))) ∧
      (∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u 0 : ℝ) (t : ℝ)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ∑ k ∈ Finset.range (N + 1),
        ENNReal.ofReal (Real.exp (-(q * (u k : ℝ)))) *
          ENNReal.ofReal h := by
  obtain ⟨u, hu, hord, hNtime⟩ :=
    firstRecord_grid_finite_clocks_realisable_before_horizon
      X ω b h (le_of_lt hh) t N hN
  have h0n (k : ℕ) (hk : k ≤ N) :
      (u 0 : ℝ) ≤ (u k : ℝ) := by
    induction k with
    | zero => exact le_refl _
    | succ k ih =>
      exact (ih (Nat.le_trans (Nat.le_succ k) hk)).trans
        (hord k (Nat.lt_of_succ_le hk))
  have hNtNN : u N ≤ t :=
    ENNReal.coe_le_coe.mp (le_of_lt hNtime)
  have hNt : (u N : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hNtNN
  have hSurvive : ENNReal.ofReal (u N : ℝ) < τ := by
    simpa using (lt_trans hNtime htτ)
  refine ⟨u, hu, ?_⟩
  exact runningSup_finite_record_cells_with_terminal_discount_upper
    X ω τ q b h hq hb (le_of_lt hh) N u t hu hord
    (h0n N le_rfl) hSurvive hNt (le_of_not_gt hnext)
