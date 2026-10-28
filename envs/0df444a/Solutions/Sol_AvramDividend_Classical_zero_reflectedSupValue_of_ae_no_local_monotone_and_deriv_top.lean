-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_of_ae_no_local_monotone_and_deriv_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:54:22.923039+00:00
-- url     : https://prove2.me/submissions/55379e0d-45a0-4fb2-b76b-d058f802d9fd

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_no_local_monotone_path
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Reduce instant zero-barrier ruin and an infinite scale slope to zero value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hNoMono : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ¬ MonotoneOn (fun t : ℝ≥0 => X.X t ω) (Icc 0 ε))
    (hder : derivZeroPlus W = ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  have hruin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 :=
    hNoMono.mono (fun ω hω =>
      barrierRuinTime_zero_of_no_local_monotone_path X ω hω)
  rw [barrierSupValue_zero_of_ae_instant_ruin X 0 q hruin,
    barrierValue_zero_of_derivZeroPlus_top W hder]
  simp
