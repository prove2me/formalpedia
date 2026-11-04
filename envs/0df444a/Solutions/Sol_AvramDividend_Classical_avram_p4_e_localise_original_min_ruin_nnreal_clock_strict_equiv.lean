-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_min_ruin_nnreal_clock_strict_equiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:56:38.848011+00:00
-- url     : https://prove2.me/submissions/282ec087-4a43-41a7-ad40-71d78bd1d252

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- True original finite clipped clock agrees with the strict extended-real min threshold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω (t : ℝ≥0),
      t < τ ω ↔ (t : ℝ≥0∞) <
        min (ruinTime X x D ω) (n : ℝ≥0∞) := by
  intro ω t
  have hnlt : (n : ℝ≥0∞) < ⊤ := by simp
  have hmin_lt : min (ruinTime X x D ω) (n : ℝ≥0∞) < ⊤ :=
    lt_of_le_of_lt (min_le_right _ _) hnlt
  have hcoe : ((τ ω : ℝ≥0) : ℝ≥0∞) =
      min (ruinTime X x D ω) (n : ℝ≥0∞) := by
    rw [hτ ω]
    exact ENNReal.coe_toNNReal (ne_of_lt hmin_lt)
  rw [← hcoe]
  simp