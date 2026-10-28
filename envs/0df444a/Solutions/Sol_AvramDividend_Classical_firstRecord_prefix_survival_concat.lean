-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_prefix_survival_concat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:10:38.892094+00:00
-- url     : https://prove2.me/submissions/c18781ae-0ad9-406b-b204-128cf73dcd17

import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstRecord_shifted_drawdown_survival_iff
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Concatenate pre-record survival with shifted future drawdown survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (a : ℝ) (T : ℝ≥0)
    (hPre : ∀ r : ℝ≥0, r < u → reflectedSup X r ω ≤ a)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    ∀ r : ℝ≥0, r < u + T → reflectedSup X r ω ≤ a := by
  have hAfter :
      ∀ t : ℝ≥0, t ≤ T → reflectedSup X (u + t) ω ≤ a :=
    (firstRecord_shifted_drawdown_survival_iff
      X b hb ω u hu hBdd a T).2 hPost
  intro r hr
  by_cases hru : r < u
  · exact hPre r hru
  · have hur : u ≤ r := le_of_not_gt hru
    have hDelta : r - u ≤ T :=
      (tsub_le_iff_left).2 (le_of_lt hr)
    have hEq : u + (r - u) = r := add_tsub_cancel_of_le hur
    simpa [hEq] using hAfter (r - u) hDelta
