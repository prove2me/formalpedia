-- Prove2me | solution 1 for AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T14:44:13.07409+00:00
-- url     : https://prove2.me/submissions/a0a13336-4710-409d-8228-755f122765bc

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_true_upperfirst_terminal_real_expectation
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  let F : Ω → ℝ := fun ω =>
    if twoSidedExitUpTime X (a-x) ω <
        twoSidedExitDownTime X (-x) ω then
      Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
    else 0
  obtain ⟨hFInt, hFVal⟩ :=
    avram_ws01b_bv_true_upperfirst_terminal_real_expectation
      X hX q hq W hW hBV a x ha hx0 hxa
  have hWnonneg (z : ℝ) : 0 ≤ W z := by
    by_cases hz : 0 ≤ z
    · exact hW.2.1 z hz
    · have hNeg : z < 0 := lt_of_not_ge hz
      rw [hW.1 z hNeg]
  have hFnonneg : ∀ ω : Ω, 0 ≤ F ω := by
    intro ω
    by_cases hu : twoSidedExitUpTime X (a-x) ω <
        twoSidedExitDownTime X (-x) ω
    · simp only [F, if_pos hu]
      exact mul_nonneg (Real.exp_nonneg _) (hWnonneg _)
    · simp [F, hu]
  have hOfReal :
      (∫⁻ ω, ENNReal.ofReal (F ω) ∂P) = ENNReal.ofReal (W x) := by
    have h :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFInt
        (Filter.Eventually.of_forall hFnonneg)
    rw [hFVal] at h
    exact h.symm
  have hReward (ω : Ω) :
      ENNReal.ofReal (F ω) =
      (if twoSidedExitUpTime X (a-x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (a-x) ω).toReal))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))
      else 0) := by
    by_cases hu : twoSidedExitUpTime X (a-x) ω <
        twoSidedExitDownTime X (-x) ω
    · simp only [F, if_pos hu]
      rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rfl
    · simp [F, hu]
  have hTerminal :
      (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂P) = ENNReal.ofReal (W x) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (F ω) ∂P := by
        apply lintegral_congr_ae
        filter_upwards with ω
        exact (hReward ω).symm
      _ = ENNReal.ofReal (W x) := hOfReal
  have hFactor :=
    chat04_strict_stopped_exit_payoff_any_measure_factorisation
      X P q a x hxa W
  simpa only [twoSidedExitExpectation] using hFactor.symm.trans hTerminal
