-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_raw_positive_reserve_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:17:20.362473+00:00
-- url     : https://prove2.me/submissions/4cfc0c96-93a5-43c2-8701-72d4acd89258

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original Lévy reserve at its bounded ruin-truncated stop has
integrable positive part, independently of the possibly infinite negative mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hXstopped : Measurable (fun ω => X.X (τ ω) ω)) :
    Integrable (fun ω => max (x + X.X (τ ω) ω) 0) P := by
  have hExpX : Integrable
      (fun ω => Real.exp (X.X (τ ω) ω)) P := by
    simpa using
      (avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q
        X x D n τ hτeq hτmeas hτstop 1 (by norm_num) 0)
  have hExpReserve : Integrable
      (fun ω => Real.exp (x + X.X (τ ω) ω)) P := by
    convert hExpX.const_mul (Real.exp x) using 1
    funext ω
    rw [Real.exp_add]
  have hPosMeas : Measurable
      (fun ω => max (x + X.X (τ ω) ω) 0) :=
    (measurable_const.add hXstopped).max measurable_const
  have hPointwise : ∀ y : ℝ, max y 0 ≤ Real.exp y := by
    intro y
    rcases le_total y 0 with hy | hy
    · rw [max_eq_right hy]
      exact (Real.exp_pos y).le
    · rw [max_eq_left hy]
      nlinarith [Real.add_one_le_exp y]
  apply hExpReserve.mono hPosMeas.stronglyMeasurable.aestronglyMeasurable
  filter_upwards [] with ω
  have hn : 0 ≤ max (x + X.X (τ ω) ω) 0 := le_max_right _ _
  simpa [Real.norm_eq_abs, abs_of_nonneg hn,
    abs_of_pos (Real.exp_pos _)] using
      (hPointwise (x + X.X (τ ω) ω))
