-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_real_time_cash_atom_le_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:47:05.177193+00:00
-- url     : https://prove2.me/submissions/00f1b0e3-37ea-41c7-b1a9-487a1de653df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Nonnegative real-indexed original Cash atoms obey the true secant loss budget. -/
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
    (ω : Ω) (t : ℝ) (ht : 0 ≤ t) (μatom : Measure ℝ)
    (hμatom : μatom {t} =
      ENNReal.ofReal (rightLimit D (Real.toNNReal t) ω -
        D (Real.toNNReal t) ω))
    (hdelta : 0 ≤ rightLimit D (Real.toNNReal t) ω -
      D (Real.toNNReal t) ω)
    (helig : Real.toNNReal t = 0 ∨
      (Real.toNNReal t : ℝ≥0∞) < ruinTime X x D ω) :
    (ENNReal.ofReal (Real.exp (-(q * t))) * μatom {t}).toReal ≤
      Real.exp (-(q * t)) *
        (w (riskProcess X x D (Real.toNNReal t) ω) -
          w (riskProcess X x D (Real.toNNReal t) ω -
            (rightLimit D (Real.toNNReal t) ω -
              D (Real.toNNReal t) ω))) := by
  have hcast : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := by
    simpa [ht] using (Real.coe_toNNReal t)
  have hAtom : μatom {((Real.toNNReal t : ℝ≥0) : ℝ)} =
      ENNReal.ofReal (rightLimit D (Real.toNNReal t) ω -
        D (Real.toNNReal t) ω) := by
    simpa [hcast] using hμatom
  have h := avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
    X x D w q hjump ω (Real.toNNReal t) μatom hAtom hdelta helig
  simpa [hcast] using h
