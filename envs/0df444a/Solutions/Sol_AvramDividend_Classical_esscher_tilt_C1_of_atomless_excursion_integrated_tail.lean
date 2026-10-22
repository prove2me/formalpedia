-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilt_C1_of_atomless_excursion_integrated_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T23:32:21.615258+00:00
-- url     : https://prove2.me/submissions/69080494-c549-45d3-aa9e-00a58e142c0b

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Ici_of_finite_pos_noAtoms
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_positive_integrated_excursion_tail
import Theorems.Thm_AvramDividend_Classical_esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution (μ : Measure ℝ) [NullSingletonClass μ] (W V : ℝ → ℝ)
    (a c φ : ℝ) (ha : 0 < a)
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤)
    (hW : ∀ x : ℝ, 0 < x →
      W x = c * Real.exp (∫ t in a..x, μ.real (Ici t)))
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  have hT : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0) :=
    continuousOn_measureReal_Ici_of_finite_pos_noAtoms μ hfin
  have hWc1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    contDiffOn_one_of_positive_integrated_excursion_tail
      (fun t : ℝ => μ.real (Ici t)) W a c ha hT hW
  exact esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
    φ W V hWc1 hV
