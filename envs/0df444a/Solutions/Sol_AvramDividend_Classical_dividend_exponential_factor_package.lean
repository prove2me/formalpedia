-- Prove2me | solution 1 for AvramDividend.Classical.dividend_exponential_factor_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:26:15.523383+00:00
-- url     : https://prove2.me/submissions/90282b40-deaa-409b-9550-bc3491213eab

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Adapted 𝓕 (fun t ω => Real.exp (-(θ * D t ω))) ∧
    (∀ ω, Antitone (fun t => Real.exp (-(θ * D t ω)))) ∧
    (∀ t ω, 0 < Real.exp (-(θ * D t ω)) ∧
      Real.exp (-(θ * D t ω)) ≤ 1) := by
  rcases hD with ⟨hzero, hmono, hleft, hadapt⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact ((measurable_const.mul (hadapt t)).neg).exp
  · intro ω s t hst
    apply Real.exp_le_exp.mpr
    have hm : D s ω ≤ D t ω := (hmono ω) hst
    have hmul : θ * D s ω ≤ θ * D t ω :=
      mul_le_mul_of_nonneg_left hm hθ
    linarith
  · intro t ω
    constructor
    · exact Real.exp_pos _
    · have hnonneg : 0 ≤ D t ω := by
        have hm : D 0 ω ≤ D t ω :=
          (hmono ω) (zero_le : (0 : ℝ≥0) ≤ t)
        rw [hzero ω] at hm
        exact hm
      have hle : -(θ * D t ω) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg hθ hnonneg)
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
