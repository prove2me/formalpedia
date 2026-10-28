-- Prove2me | solution 1 for AvramDividend.Classical.bv_two_sided_terminal_payoff_uniform_bound_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:17:03.099035+00:00
-- url     : https://prove2.me/submissions/6973ca12-14d0-493e-879a-133af9b715fa

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_two_sided_boundary_partition
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_pointwise_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Both strict two-sided terminal q-scale payoffs are bounded by W(a), including BV boundary contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hxa : x ≤ a) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ≤ ENNReal.ofReal (W a) := by
  have hW0a : W 0 ≤ W a := hW.2.2.2.1
    (by simp) (by simpa using ha) ha
  have hUpper := chat04_strict_stopped_exit_payoff_pointwise_bound
    X q (le_of_lt hq) a x hxa W ω
  have hPartition := chat04_two_sided_boundary_partition
    X q W hW a x hxa ω
  let tUp := twoSidedExitUpTime X (a - x) ω
  let tDown := twoSidedExitDownTime X (-x) ω
  by_cases hup : tUp < tDown
  · have hdown : ¬tDown < tUp := not_lt_of_ge (le_of_lt hup)
    simpa [tUp, tDown, hup, hdown] using hUpper
  · rw [hPartition]
    by_cases hdown : tDown < tUp
    · simp only [tUp, tDown] at hup hdown
      simp only [if_neg hup, zero_add, if_pos hdown]
      by_cases hcontact : x + X.X tDown.toNNReal ω = 0
      · simp only [tDown] at hcontact
        simp only [if_pos hcontact]
        have ht : 0 ≤ tDown.toReal := ENNReal.toReal_nonneg
        have hnonneg : 0 ≤ q * tDown.toReal :=
          mul_nonneg (le_of_lt hq) ht
        have hexp : Real.exp (-(q * tDown.toReal)) ≤ 1 := by
          rw [← Real.exp_zero]
          exact (Real.exp_le_exp).mpr (neg_nonpos.mpr hnonneg)
        calc
          ENNReal.ofReal (Real.exp (-(q * tDown.toReal))) *
              ENNReal.ofReal (W 0) ≤
              (1 : ENNReal) * ENNReal.ofReal (W 0) := by
                gcongr
                simpa using ENNReal.ofReal_le_ofReal hexp
          _ = ENNReal.ofReal (W 0) := by simp
          _ ≤ ENNReal.ofReal (W a) := ENNReal.ofReal_le_ofReal hW0a
      · simp only [tDown] at hcontact
        simp [hcontact]
    · simp only [tUp, tDown] at hup hdown
      simp [hup, hdown]