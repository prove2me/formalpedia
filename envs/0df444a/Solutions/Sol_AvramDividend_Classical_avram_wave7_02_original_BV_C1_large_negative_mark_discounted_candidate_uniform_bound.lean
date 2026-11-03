-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_large_negative_mark_discounted_candidate_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:24:50.06421+00:00
-- url     : https://prove2.me/submissions/892d879a-4163-41d3-b4d7-122ca10653d8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- An original negative Levy source mark separated from zero has a bounded
discounted C1 candidate-value difference, including a ruin overshoot. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (a b R : ℝ) (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R)
    (hBound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (z : ℝ) (hz : z ≤ -a / 2) :
    |Real.exp (-(q * (t : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t + z) -
      w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t))| ≤ 2 * R := by
  let y : ℝ := Function.leftLim (fun s : ℝ≥0 =>
    x + X.X s ω - rightLimit D s ω) t
  change |Real.exp (-(q * (t : ℝ))) * (w (y + z) - w y)| ≤ 2 * R
  change y ∈ Icc a b at hBand
  have hyz : y + z ≤ b := by linarith [hBand.2, hz, ha]
  have hDelta : |w (y + z) - w y| ≤ 2 * R := by
    calc
      |w (y + z) - w y| ≤ |w (y + z)| + |w y| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (w (y + z)) 0 (w y))
      _ ≤ R + R := add_le_add (hBound _ hyz) (hBound _ hBand.2)
      _ = 2 * R := by ring
  have hTime : 0 ≤ (t : ℝ) := NNReal.coe_nonneg _
  have hexp : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    have hneg : -(q * (t : ℝ)) ≤ 0 := neg_nonpos.mpr (mul_nonneg hq hTime)
    simpa using (Real.exp_le_exp.mpr hneg)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(q * (t : ℝ))) * |w (y + z) - w y|
      ≤ Real.exp (-(q * (t : ℝ))) * (2 * R) :=
        mul_le_mul_of_nonneg_left hDelta (Real.exp_pos _).le
    _ ≤ 1 * (2 * R) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = 2 * R := one_mul _
