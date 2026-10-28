-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_killed_discount_lower_of_shifted_guard
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:29:50.076917+00:00
-- url     : https://prove2.me/submissions/dbb0f8a4-84cf-4129-9d89-9c13b9e0cd9e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_survives_of_shifted_drawdown_guard

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (ω : Ω) (u v T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hvT : v ≤ u + T)
    (hPre : ∀ r : ℝ≥0, r < u → reflectedSup X r ω ≤ a)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    ENNReal.ofReal
        (ε * Real.exp (-(q * (((u + T : ℝ≥0) : ℝ))))) ≤
      (if (v : ℝ≥0∞) < barrierRuinTime X a ω then
         ENNReal.ofReal (ε * Real.exp (-(q * (v : ℝ))))
       else 0) := by
  rw [if_pos (AvramDividend.Classical.nextRecord_survives_of_shifted_drawdown_guard X a b ε ha hb hε ω u v T
    hu hv hvT hPre hPost)]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hε
  apply Real.exp_le_exp.2
  have : (v : ℝ) ≤ ((u + T : ℝ≥0) : ℝ) := by exact_mod_cast hvT
  nlinarith
