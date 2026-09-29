-- Prove2me | solution 1 for FamousTheorems.tendsto_integral_exp_smul_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:25.666671+00:00
-- url     : https://prove2.me/submissions/80dae29d-5276-4e7a-8cf9-4e264f6c9dd8

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} {V : Type u_2} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℂ E] (f : V → E) [inst_2 : AddCommGroup V] [inst_3 : TopologicalSpace V] 
    [IsTopologicalAddGroup V] [T2Space V] [inst_6 : MeasurableSpace V] [BorelSpace V] [inst_8 : Module ℝ V] 
    [ContinuousSMul ℝ V] [FiniteDimensional ℝ V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure], 
    Tendsto (fun w => ∫ (v : V), Real.fourierChar (-w v) • f v ∂μ) (cocompact (StrongDual ℝ V)) (𝓝 0) :=
  @_root_.tendsto_integral_exp_smul_cocompact
