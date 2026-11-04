-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightjump_excess_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:18:10.169267+00:00
-- url     : https://prove2.me/submissions/b36f17c5-b18e-4c32-bac9-c3f071c11b95

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A source-state excess-value-loss envelope makes the authentic countable
right-dividend correction absolutely summable, while hjump gives its sign. -/
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
    (B : ι → ℝ) (hB_nonneg : ∀ i, 0 ≤ B i)
    (hB_summable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) * B i))
    (hExcess : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
          w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        (rightLimit D (t i) ω - D (t i) ω) + B i) :
    Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ∧
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by
  let f : ι → ℝ := fun i =>
    Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))
  let g : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) * B i
  have hAt : ∀ i : ι, f i ≤ 0 := by
    intro i
    exact avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
      X x D w q hjump (fun _ => t i) ω (hPre i)
  have hLower (i : ι) : -(g i) ≤ f i := by
    have hRaw :
        -(B i) ≤
          (rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω) := by
      linarith [hExcess i]
    calc
      -(g i) = Real.exp (-(q * (t i : ℝ))) * (-(B i)) := by
        dsimp [g]
        ring
      _ ≤ Real.exp (-(q * (t i : ℝ))) *
          ((rightLimit D (t i) ω - D (t i) ω) +
            w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (riskProcess X x D (t i) ω)) :=
        mul_le_mul_of_nonneg_left hRaw (le_of_lt (Real.exp_pos _))
      _ = f i := rfl
  have hNorm : ∀ i : ι, ‖f i‖ ≤ g i := by
    intro i
    have hG : 0 ≤ g i :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (hB_nonneg i)
    rw [Real.norm_eq_abs, abs_of_nonpos (hAt i)]
    linarith [hLower i]
  have hSeries : Summable f :=
    Summable.of_norm_bounded (show Summable g from hB_summable) hNorm
  exact ⟨hSeries, tsum_nonpos hAt⟩