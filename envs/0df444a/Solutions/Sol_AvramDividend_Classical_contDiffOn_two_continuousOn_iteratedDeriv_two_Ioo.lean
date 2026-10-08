-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_two_continuousOn_iteratedDeriv_two_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:14:48.663668+00:00
-- url     : https://prove2.me/submissions/191235d1-9a55-4cdb-ae10-0e14b29e75e3

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (W : ℝ → ℝ) (a : ℝ)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn (iteratedDeriv 2 W) (Ioo 0 a) := by
  have huniq : UniqueDiffOn ℝ (Ioo 0 a) :=
    isOpen_Ioo.uniqueDiffOn
  have hwithin :
      ContinuousOn (iteratedDerivWithin 2 W (Ioo 0 a)) (Ioo 0 a) :=
    hC2.continuousOn_iteratedDerivWithin (by norm_num) huniq
  exact hwithin.congr (by
    intro x hx
    exact ((iteratedDerivWithin_of_isOpen
      (f := W) (n := 2) isOpen_Ioo) hx).symm)
