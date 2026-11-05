-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_paid_atoms_ennreal_value_loss_without_summability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:47:23.156061+00:00
-- url     : https://prove2.me/submissions/0e57d6a5-ea3c-45be-8ea2-5ff4ae1e5be1

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Nonnegative original paid atoms admit an extended-real value-loss bound without L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (u : ℝ≥0),
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D u ω - D u ω ≤
          w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    (ω : Ω) (A : Set ℝ) (μatom : Measure ℝ)
    (hMass : ∀ a : A,
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω))
    (hPaid : ∀ a : A, Real.toNNReal a.1 = 0 ∨
      (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' a : A,
      ENNReal.ofReal (Real.exp (-(q * a.1))) * μatom {a.1}) ≤
    ∑' a : A,
      ENNReal.ofReal (Real.exp (-(q * a.1))) *
        ENNReal.ofReal
          (w (riskProcess X x D (Real.toNNReal a.1) ω) -
            w (riskProcess X x D (Real.toNNReal a.1) ω -
              (rightLimit D (Real.toNNReal a.1) ω -
                D (Real.toNNReal a.1) ω))) := by
  apply ENNReal.tsum_le_tsum
  intro a
  rw [hMass a]
  have hval := hjump ω (Real.toNNReal a.1) (hPaid a)
  exact mul_le_mul_of_nonneg_left
    (ENNReal.ofReal_le_ofReal hval) (by positivity)
