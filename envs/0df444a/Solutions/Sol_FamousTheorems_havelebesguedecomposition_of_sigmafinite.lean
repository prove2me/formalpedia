-- Prove2me | solution 1 for FamousTheorems.havelebesguedecomposition_of_sigmafinite
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:14.285186+00:00
-- url     : https://prove2.me/submissions/975be65a-62a6-4e85-9d72-b57d1eba1c08

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {m : MeasurableSpace α} 
    (μ ν : MeasureTheory.Measure α) [MeasureTheory.SFinite μ] [MeasureTheory.SigmaFinite ν], μ.HaveLebesgueDecomposition ν :=
  @_root_.MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite
