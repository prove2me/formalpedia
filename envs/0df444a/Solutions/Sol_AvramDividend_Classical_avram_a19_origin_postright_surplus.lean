-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_origin_postright_surplus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:18:00.484037+00:00
-- url     : https://prove2.me/submissions/dfe4ae13-be11-4502-b51d-bca973036c53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The first physical-grid left-limit reserve is the surplus after the time-zero right dividend. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (u : ℕ → ℕ → ℝ≥0)
    (hgrid0 : ∀ n, u n 0 = 0) (n : ℕ) (ω : Ω) :
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n 0) =
      x - rightLimit D 0 ω := by
  rw [hgrid0 n]
  rw [avram_p2_a_zero_rate_leftLim_origin_nnreal]
  rw [X.X_zero ω]
  ring
