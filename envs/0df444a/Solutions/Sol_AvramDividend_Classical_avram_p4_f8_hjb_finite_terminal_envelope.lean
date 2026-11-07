-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f8_hjb_finite_terminal_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:42:28.678354+00:00
-- url     : https://prove2.me/submissions/306a9489-b531-4bf8-bc7d-52d8eeb553e6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_finite_stopped_reserve_le_barrier
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_topcap_global_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_positive_deriv_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The nonnegative discounted stopped potential is bounded by w of the upper barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤)
    (q : ℝ) (hq : 0 < q)
    (b : ℝ) (n : ℕ) (hb : 1 ≤ b) (ω : Ω) :
    ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
      (min (twoSidedExitUpTimeCorrected X (b - 1) ω)
        (min (twoSidedExitDownTimeCorrected X (-1) ω)
          (n : ℝ≥0∞))))) *
      w (1 + X.X (ENNReal.toNNReal
        (min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω)
            (n : ℝ≥0∞)))) ω)) ≤ ENNReal.ofReal (w b) := by
  let τ : ℝ≥0∞ :=
    min (twoSidedExitUpTimeCorrected X (b - 1) ω)
      (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
  let y : ℝ := 1 + X.X (ENNReal.toNNReal τ) ω
  have hy_le : y ≤ b := by
    have hbnd := avram_p4_f7_hjb_finite_stopped_reserve_le_barrier
      X hX b n hb ω
    dsimp [y, τ]
    linarith
  have hn := avram_p4_f7_hjb_topcap_global_nonnegative
    w C hw0 hw_cont hw_neg hw_smooth hw_grad hTop
  have hmon : MonotoneOn w (Ici 0) := by
    have hS : {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} = Ioi (0 : ℝ) := by
      ext z
      simp [hTop]
    have hd : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ w z := by
      intro z hz
      have hm : z ∈ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
        simp [hz, hTop]
      exact (hw_smooth.contDiffAt
        (by simpa [hS] using (isOpen_Ioi.mem_nhds hz))).differentiableAt (by norm_num)
    have hg : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z := by
      intro z hz
      exact hw_grad z hz (by simp [hTop])
    exact (avram_p4_f6_hjb_positive_deriv_monotone w hw0 hw_cont hd hg).1
  have hwb : w y ≤ w b := by
    by_cases hy : y < 0
    · rw [hw_neg y hy]
      exact hn b
    · exact hmon (Set.mem_Ici.mpr (le_of_not_gt hy))
        (Set.mem_Ici.mpr (by linarith)) hy_le
  have hdiscount : Real.exp (-(q * ENNReal.toReal τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hnonneg := mul_nonneg hq.le (ENNReal.toReal_nonneg : 0 ≤ ENNReal.toReal τ)
    linarith
  have hproduct : Real.exp (-(q * ENNReal.toReal τ)) * w y ≤ w b := by
    calc
      Real.exp (-(q * ENNReal.toReal τ)) * w y ≤ 1 * w y :=
        mul_le_mul_of_nonneg_right hdiscount (hn y)
      _ = w y := one_mul _
      _ ≤ w b := hwb
  exact ENNReal.ofReal_le_ofReal hproduct
