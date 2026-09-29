-- Prove2me | solution 1 for FamousTheorems.subalgebra_topologicalclosure_eq_top_of_separatespoints
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:06.416725+00:00
-- url     : https://prove2.me/submissions/84cbf1fe-d04c-446b-8c81-838f6b51c903

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {X : Type u_1} [inst : TopologicalSpace X] 
    [inst_1 : CompactSpace X] (A : Subalgebra ℝ C(X, ℝ)), A.SeparatesPoints → A.topologicalClosure = ⊤ :=
  @_root_.ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
