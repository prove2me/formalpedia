-- Prove2me | solution 1 for FamousTheorems.fourier_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:25.57632+00:00
-- url     : https://prove2.me/submissions/b19cad44-b080-46eb-8c2d-deaa5eeba86d

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {V : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
    [inst_2 : NormedAddCommGroup V] [inst_3 : InnerProductSpace ℝ V] [inst_4 : MeasurableSpace V] [inst_5 : BorelSpace V] 
    [inst_6 : FiniteDimensional ℝ V] (f : V → E) (w : V), 
    FourierTransform.fourier f w = ∫ (v : V), Real.fourierChar (-inner ℝ v w) • f v :=
  @_root_.Real.fourier_eq
