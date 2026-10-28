-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_of_ae_early_downward_jumps_and_deriv_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:01:10.479118+00:00
-- url     : https://prove2.me/submissions/92ce282f-2f2e-4248-a438-5f3220f91782

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_early_downward_jumps
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_derivZeroPlus_top
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Assemble the almost-sure early-downward-jump path criterion with the scale boundary value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hJumps : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => X.X s ω) (nhdsWithin t (Iio t)) (nhds l) ∧
          X.X t ω < l)
    (hder : derivZeroPlus W = ⊤) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by
  have hruin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 := by
    filter_upwards [hJumps] with ω hω
    exact barrierRuinTime_zero_of_early_downward_jumps X ω hω
  rw [barrierSupValue_zero_of_ae_instant_ruin X 0 q hruin,
      barrierValue_zero_of_derivZeroPlus_top W hder]
  simp
