-- Prove2me | solution 1 for AvramDividend.Classical.causal_exp_l1_convolution_continuous_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:06:54.660191+00:00
-- url     : https://prove2.me/submissions/0ccce9a2-0d85-465f-9466-2552408b62a7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Causal L1 convolution with exponential damping is continuous at zero. -/
theorem solution
    (P : ℝ → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hP : IntegrableOn P (Ioi (0 : ℝ)) volume) :
    ContinuousOn
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
        P (x - s) * Real.exp (-w * s) ∂volume)
      (Ici (0 : ℝ)) := by
  have hVc : ContinuousOn (fun s : ℝ => Real.exp (-w * s))
      (Ici (0 : ℝ)) := by fun_prop
  have hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R →
        |Real.exp (-w * s)| ≤ C := by
    intro R hR
    refine ⟨1, ?_⟩
    intro s hs
    have hneg : -w * s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hw) hs.1.le
    have hle : Real.exp (-w * s) ≤ 1 :=
      Real.exp_le_one_iff.mpr hneg
    simpa only [abs_of_pos (Real.exp_pos _)] using hle
  exact causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded
    P (fun s : ℝ => Real.exp (-w * s)) hP hVc hVb
