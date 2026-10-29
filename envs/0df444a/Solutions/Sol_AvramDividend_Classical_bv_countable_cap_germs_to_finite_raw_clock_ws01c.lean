-- Prove2me | solution 1 for AvramDividend.Classical.bv_countable_cap_germs_to_finite_raw_clock_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:56:52.913536+00:00
-- url     : https://prove2.me/submissions/bba33e42-9407-4728-8139-57af985f8e86

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℝ≥0∞)
    (G : ℝ≥0 → Ω → Prop)
    (hCap : ∀ N : ℕ, ∀ᵐ ω ∂P,
      G ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω) :
    ∀ᵐ ω ∂P,
      τ ω < ⊤ → G (τ ω).toNNReal ω := by
  have hAll : ∀ᵐ ω ∂P, ∀ N : ℕ,
      G ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω :=
    ae_all_iff.mpr hCap
  filter_upwards [hAll] with ω hw hFinite
  have hNeTop : τ ω ≠ ⊤ := ne_of_lt hFinite
  have hτCo : ((τ ω).toNNReal : ℝ≥0∞) = τ ω :=
    ENNReal.coe_toNNReal hNeTop
  obtain ⟨N, hN⟩ := exists_nat_gt (τ ω).toNNReal
  have hCapGe : τ ω ≤ (N : ℝ≥0∞) := by
    rw [← hτCo]
    exact_mod_cast (le_of_lt hN)
  have hInf : τ ω ⊓ (N : ℝ≥0∞) = τ ω :=
    inf_eq_left.mpr hCapGe
  simpa only [hInf] using hw N
