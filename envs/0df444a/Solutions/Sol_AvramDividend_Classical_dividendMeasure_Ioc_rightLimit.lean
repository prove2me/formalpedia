-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_Ioc_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T02:57:17.27447+00:00
-- url     : https://prove2.me/submissions/34f25554-e61c-4650-9669-3ee00c19f519

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The Lebesgue-Stieltjes measure of a dividend strategy on the half-open
interval `(a, b]` is the increase of the RIGHT LIMIT of the strategy across
that interval.

This is the `Ioc` companion of the Proved
`dividendMeasure_Ico_eq_dividend_increment`, which gives the mass of the open
interval `(a, b)`.  The Lebesgue-Stieltjes measure of the monotone real
extension of the strategy is the Stieltjes measure of its right limit, and
Mathlib's `StieltjesFunction.measure_Ioc` gives the mass of `(a, b]` as the
increase of that right limit; the Proved
`dividendPath_real_rightLim_eq_rightLimit` identifies the right limit of the
real extension with the strategy's own right limit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (rightLimit D b ω - rightLimit D a ω) := by
  -- The real extension of the strategy is monotone.
  have hmono : Monotone (fun s : ℝ => D s.toNNReal ω) := by
    intro a b hab
    exact (hD.2.1 ω) (Real.toNNReal_mono hab)
  -- The dividend measure is the Stieltjes measure of the right limit.
  have hmeasure :
      dividendMeasure D ω =
        hmono.stieltjesFunction.measure := by
    unfold dividendMeasure
    rw [dif_pos hmono]
  rw [hmeasure, StieltjesFunction.measure_Ioc]
  -- The right limit of the real extension is the strategy's right limit.
  have hright : ∀ (t : ℝ≥0),
      Function.rightLim (fun s : ℝ => D s.toNNReal ω) (t : ℝ) = rightLimit D t ω :=
    fun t => by
      exact dividendPath_real_rightLim_eq_rightLimit D ω
        (fun s u hsu => hD.2.1 ω hsu) t
  -- The Stieltjes function of a monotone `f` is its right limit, by `rfl`.
  simp only [Monotone.stieltjesFunction_eq]
  have hboth : Function.rightLim (fun s : ℝ => D s.toNNReal ω) ↑a = rightLimit D a ω ∧
      Function.rightLim (fun s : ℝ => D s.toNNReal ω) ↑b = rightLimit D b ω :=
    ⟨hright a, hright b⟩
  rw [hboth.1, hboth.2]
