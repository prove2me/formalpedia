-- Prove2me | solution 1 for FamousTheorems.fourierinv_fourier_eq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:53.448603+00:00
-- url     : https://prove2.me/submissions/f89364db-dfca-42dd-bd84-c851bd6cab82

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {V : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : MeasurableSpace V] [inst_3 : BorelSpace V] [inst_4 : FiniteDimensional ℝ V] 
    [inst_5 : NormedAddCommGroup E] [inst_6 : NormedSpace ℂ E] {f : V → E} [CompleteSpace E], 
    MeasureTheory.Integrable f MeasureTheory.volume → 
    MeasureTheory.Integrable (FourierTransform.fourier f) MeasureTheory.volume → 
    ∀ {v : V}, ContinuousAt f v → FourierTransformInv.fourierInv (FourierTransform.fourier f) v = f v :=
  @_root_.MeasureTheory.Integrable.fourierInv_fourier_eq
