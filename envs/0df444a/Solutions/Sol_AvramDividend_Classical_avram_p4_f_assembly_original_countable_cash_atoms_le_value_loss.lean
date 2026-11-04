-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_countable_cash_atoms_le_value_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:48:12.284746+00:00
-- url     : https://prove2.me/submissions/cb52d3e3-ca5b-4942-bddf-cd79b9bc3ee8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real original Cash atomic sums are bounded by corresponding value losses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (A : Set ℝ≥0) (μatom : Measure ℝ)
    (hμatom : ∀ a : A,
      μatom {(a.1 : ℝ)} =
        ENNReal.ofReal (rightLimit D a.1 ω - D a.1 ω))
    (hdelta : ∀ a : A,
      0 ≤ rightLimit D a.1 ω - D a.1 ω)
    (helig : ∀ a : A,
      a.1 = 0 ∨ (a.1 : ℝ≥0∞) < ruinTime X x D ω)
    (hCashSum : Summable (fun a : A =>
      (ENNReal.ofReal (Real.exp (-(q * (a.1 : ℝ)))) *
        μatom {(a.1 : ℝ)}).toReal))
    (hValueSum : Summable (fun a : A =>
      Real.exp (-(q * (a.1 : ℝ))) *
        (w (riskProcess X x D a.1 ω) -
          w (riskProcess X x D a.1 ω -
            (rightLimit D a.1 ω - D a.1 ω))))) :
    (∑' a : A,
      (ENNReal.ofReal (Real.exp (-(q * (a.1 : ℝ)))) *
        μatom {(a.1 : ℝ)}).toReal) ≤
      ∑' a : A,
        Real.exp (-(q * (a.1 : ℝ))) *
          (w (riskProcess X x D a.1 ω) -
            w (riskProcess X x D a.1 ω -
              (rightLimit D a.1 ω - D a.1 ω))) := by
  apply Summable.tsum_le_tsum ?_ hCashSum hValueSum
  intro a
  exact avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
    X x D w q hjump ω a.1 μatom (hμatom a) (hdelta a) (helig a)
