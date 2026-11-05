-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:40:08.999797+00:00
-- url     : https://prove2.me/submissions/8ba1b28f-7fe8-4a0a-b178-d4cb74224002

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped dividend atom and postpayment terminal value
have the exact discounted jump bound required at the right horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      Real.exp (-(q * (t : ℝ))) *
          (rightLimit D t ω - D t ω) +
        Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω) ≤
        Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω) := by
  intro ω t hPre
  have hJ := hjump ω t hPre
  have hState :
      riskProcess X x D t ω -
        (rightLimit D t ω - D t ω) =
          x + X.X t ω - rightLimit D t ω := by
    simp only [riskProcess]
    ring
  rw [hState] at hJ
  have hDiscount : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    (Real.exp_pos _).le
  calc
    Real.exp (-(q * (t : ℝ))) *
          (rightLimit D t ω - D t ω) +
        Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω) ≤
      Real.exp (-(q * (t : ℝ))) *
          (w (riskProcess X x D t ω) -
            w (x + X.X t ω - rightLimit D t ω)) +
        Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω) := by
            exact add_le_add_left
              (mul_le_mul_of_nonneg_left hJ hDiscount) _
    _ = Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω) := by ring
