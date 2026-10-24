-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:17:59.904691+00:00
-- url     : https://prove2.me/submissions/23d75a07-ae0b-45cb-8673-d030040ed281

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_vanishes_at_origin
import Theorems.Thm_AvramDividend_Classical_causal_continuousOn_Ici_of_positive_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology

theorem solution
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ici (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume)
      (Ici (0 : ℝ)) := by
  let C : ℝ → ℝ := fun x =>
    ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume
  have hPositive : ContinuousOn C (Ioi (0 : ℝ)) :=
    causal_l1_convolution_continuousOn_positive_of_Ici_input K V hK hVc
  have hVpositive : ContinuousOn V (Ioi (0 : ℝ)) :=
    hVc.mono (by intro x hx; change (0 : ℝ) < x at hx; exact hx.le)
  have hRight : Tendsto C (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (nhds (0 : ℝ)) :=
    causal_l1_convolution_vanishes_at_origin K V hK hVpositive hVb
  have hC0 : C 0 = 0 := by simp [C]
  have hRight' : Tendsto C (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (nhds (C 0)) := by
    simpa only [hC0] using hRight
  exact causal_continuousOn_Ici_of_positive_limit C hPositive hRight'
