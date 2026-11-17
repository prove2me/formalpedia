-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_original_barrier_no_initial_atom_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:52:08.410172+00:00
-- url     : https://prove2.me/submissions/9fc672c6-88b0-44b7-902e-3b42bf78fa94

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) (hxa : x ≤ a) :
    IsAdmissibleLe X x (ENNReal.ofReal a) (barrierStrategy X x a) ∧
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) <
        ruinTime X x (barrierStrategy X x a) ω) →
      rightLimit (barrierStrategy X x a) t ω -
        barrierStrategy X x a t ω ≤
      w (riskProcess X x (barrierStrategy X x a) t ω) -
      w (riskProcess X x (barrierStrategy X x a) t ω -
        (rightLimit (barrierStrategy X x a) t ω -
         barrierStrategy X x a t ω)) := by 
  constructor
  · exact barrierStrategy_admissibleLe_nonnegative_barrier X x a hx ha
  · intro ω t _
    have hr := barrierStrategy_no_right_jump_of_initial_below_barrier
      X x a hxa ω t
    simp only [hr, sub_self, sub_zero, le_refl]
