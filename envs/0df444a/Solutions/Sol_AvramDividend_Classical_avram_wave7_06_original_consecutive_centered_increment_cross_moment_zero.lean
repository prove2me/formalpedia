-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_consecutive_centered_increment_cross_moment_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:30:54.16867+00:00
-- url     : https://prove2.me/submissions/5b5f1d20-94ed-48e9-8eb9-2bfbe37bbd2d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_increment_L1_product_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Consecutive centred original X-increments are orthogonal in expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hFirst : Integrable (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable (fun ω =>
      X.X (s + u + v) ω - X.X (s + u) ω) P)
    (hZeroFirst : (∫ ω, X.X (s + u) ω - X.X s ω ∂P) = 0)
    (hZeroSecond :
      (∫ ω, X.X (s + u + v) ω - X.X (s + u) ω ∂P) = 0) :
    (∫ ω, (X.X (s + u) ω - X.X s ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω) ∂P) = 0 := by
  rw [avram_wave7_06_original_consecutive_increment_L1_product_factorisation
    X s u v hFirst hSecond, hZeroFirst, hZeroSecond]
  ring
