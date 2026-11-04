-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_real_indexed_cash_atom_tsum_le_value_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:56:04.868295+00:00
-- url     : https://prove2.me/submissions/7ca85c95-0006-4371-8641-587c4675cc62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_real_time_cash_atom_le_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True real-indexed Cash atoms are bounded by original source secant losses. -/
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
    (hA0 : ∀ a : A, 0 ≤ a.1)
    (hμatom : ∀ a : A,
      μatom {a.1} = ENNReal.ofReal
        (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω))
    (hdelta : ∀ a : A,
      0 ≤ rightLimit D (Real.toNNReal a.1) ω -
        D (Real.toNNReal a.1) ω)
    (helig : ∀ a : A, Real.toNNReal a.1 = 0 ∨
      (Real.toNNReal a.1 : ℝ≥0∞) < ruinTime X x D ω)
    (hCashSum : Summable (fun a : A =>
      (ENNReal.ofReal (Real.exp (-(q * a.1))) *
        μatom {a.1}).toReal))
    (hValueSum : Summable (fun a : A =>
      Real.exp (-(q * a.1)) *
        (w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω))))) :
    (∑' a : A,
      (ENNReal.ofReal (Real.exp (-(q * a.1))) *
        μatom {a.1}).toReal) ≤
      ∑' a : A, Real.exp (-(q * a.1)) *
        (w (riskProcess X x D (Real.toNNReal a.1) ω) -
          w (riskProcess X x D (Real.toNNReal a.1) ω -
            (rightLimit D (Real.toNNReal a.1) ω -
              D (Real.toNNReal a.1) ω))) := by
  apply Summable.tsum_le_tsum ?_ hCashSum hValueSum
  intro a
  exact avram_p4_f_assembly_original_real_time_cash_atom_le_secant
    X x D w q hjump ω a.1 (hA0 a) μatom
    (hμatom a) (hdelta a) (helig a)
