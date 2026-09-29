-- Prove2me | solution 1 for FamousTheorems.measure_limsup_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:34.281787+00:00
-- url     : https://prove2.me/submissions/d8f2eb7d-d874-4ad5-a2af-76e4a028d603

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} 
    {s : ℕ → Set Ω}, 
    (∀ (n : ℕ), MeasurableSet (s n)) → ProbabilityTheory.iIndepSet s μ → ∑' (n : ℕ), μ (s n) = ⊤ → μ (limsup s atTop) = 1 :=
  @_root_.ProbabilityTheory.measure_limsup_eq_one
