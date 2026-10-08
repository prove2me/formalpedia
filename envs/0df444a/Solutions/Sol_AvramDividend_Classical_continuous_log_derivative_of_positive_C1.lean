-- Prove2me | solution 1 for AvramDividend.Classical.continuous_log_derivative_of_positive_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:01:22.616751+00:00
-- url     : https://prove2.me/submissions/cbca6e9a-84c9-4936-9c5b-722a0d53bb81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology

theorem solution
    (V : ℝ → ℝ)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hVone : ContDiffOn ℝ 1 V (Ioi (0 : ℝ))) :
    ContinuousOn (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      (Ioi (0 : ℝ)) := by
  have hlog : ContDiffOn ℝ 1 (fun x : ℝ => Real.log (V x)) (Ioi (0 : ℝ)) :=
    hVone.log (by
      intro x hx
      exact (hVpos x hx).ne')
  exact hlog.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
