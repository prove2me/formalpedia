-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:11.015878+00:00
-- url     : https://prove2.me/submissions/af7b694d-cb16-4a68-a65f-b2bb1456c9b7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_excess_dominated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An actual reserve-strip secant slope bound and summable source right cash
give an absolutely summable and nonpositive stopped dividend atom correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (K : ℝ) (hK : 1 ≤ K)
    (hPayNonneg : ∀ i : ι, 0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω)))
    (hLocalSecant : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          K * (rightLimit D (t i) ω - D (t i) ω)) :
    Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ∧
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by
  let δ : ι → ℝ := fun i => rightLimit D (t i) ω - D (t i) ω
  let B : ι → ℝ := fun i => (K - 1) * δ i
  have hB0 : ∀ i : ι, 0 ≤ B i := by
    intro i
    exact mul_nonneg (sub_nonneg.mpr hK) (hPayNonneg i)
  have hBsum : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) * B i) := by
    have hRewrite :
        (fun i : ι => Real.exp (-(q * (t i : ℝ))) * B i) =
          (fun i : ι => (K - 1) *
            (Real.exp (-(q * (t i : ℝ))) * δ i)) := by
      funext i
      dsimp [B]
      ring
    rw [hRewrite]
    exact hPaySummable.mul_left (K - 1)
  have hExcess : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          (rightLimit D (t i) ω - D (t i) ω) + B i := by
    intro i
    calc
      _ ≤ K * δ i := hLocalSecant i
      _ = (rightLimit D (t i) ω - D (t i) ω) + B i := by
        dsimp [B, δ]
        ring
  exact avram_p4_d_dividend_original_countable_rightjump_excess_dominated
    X x D w q hjump t ω hPre B hB0 hBsum hExcess