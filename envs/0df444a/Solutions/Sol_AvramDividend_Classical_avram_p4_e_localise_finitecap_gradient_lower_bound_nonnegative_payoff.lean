-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:53:29.357071+00:00
-- url     : https://prove2.me/submissions/2c6099ea-0aef-4331-b3c2-c15a1ca0e3db

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section
/-- Positive interior derivative, source boundary continuity and w(0) ≥ 0 imply nonnegative finite-cap payoff, including both endpoints. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwDiff : DifferentiableOn ℝ w (Ioo (0 : ℝ) c))
    (hwGrad : ∀ y : ℝ, 0 < y → y < c → 1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → y ≤ c → 0 ≤ w y := by
  have hwIcc : ContinuousOn w (Icc (0 : ℝ) c) :=
    hwcont.mono (by intro y hy; exact hy.1)
  have hmono : MonotoneOn w (Icc (0 : ℝ) c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) c) hwIcc
    · simpa only [interior_Icc] using hwDiff
    · intro y hy
      have hy' : 0 < y ∧ y < c := by
        simpa only [interior_Icc, Set.mem_Ioo] using hy
      exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (hwGrad y hy'.1 hy'.2)
  intro y h0 hyc
  exact le_trans hw0 (hmono ⟨le_refl _, hc⟩ ⟨h0, hyc⟩ h0)
