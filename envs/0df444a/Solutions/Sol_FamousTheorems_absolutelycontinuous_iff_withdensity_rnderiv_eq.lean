-- Prove2me | solution 1 for FamousTheorems.absolutelycontinuous_iff_withdensity_rnderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:05.608667+00:00
-- url     : https://prove2.me/submissions/19f6b784-b062-4221-85f5-132d7a0a9c44

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {m : MeasurableSpace α} 
    {μ ν : MeasureTheory.Measure α} [μ.HaveLebesgueDecomposition ν], 
    μ.AbsolutelyContinuous ν ↔ ν.withDensity (μ.rnDeriv ν) = μ :=
  @_root_.MeasureTheory.Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq
