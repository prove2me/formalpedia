-- Prove2me | solution 1 for AvramDividend.Classical.excursion_integrated_tilted_scale_C1_log_concave
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:03:32.17208+00:00
-- url     : https://prove2.me/submissions/85248ba4-c081-4882-9ff2-22928bc46814

import Theorems.Thm_AvramDividend_Classical_excursion_integrated_scale_C1_log_concave
import Theorems.Thm_AvramDividend_Classical_esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_log_concave_of_scale_log_concave
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution
    (W V : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi (0 : ℝ)))
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤)
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t)))
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) ∧
      ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by
  obtain ⟨hWdiff, hWlog⟩ :=
    excursion_integrated_scale_C1_log_concave W φ μ hcont hfin hWpos hexp
  exact ⟨esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one φ W V hWdiff hV,
    esscher_tilted_log_concave_of_scale_log_concave φ W V hWpos hV hWlog⟩
