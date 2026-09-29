-- Prove2me | solution 1 for FamousTheorems.convolution_tendsto_right
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:25.278214+00:00
-- url     : https://prove2.me/submissions/26810ae3-bd1d-4cc6-9d8a-bda7771cb445

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {G : Type u_1} {E' : Type u_2} [inst : NormedAddCommGroup E'] 
    [inst_1 : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_2 : NormedSpace ℝ E'] [inst_3 : NormedAddCommGroup G] 
    [inst_4 : NormedSpace ℝ G] [CompleteSpace E'] [BorelSpace G] [inst_7 : FiniteDimensional ℝ G] [μ.IsAddHaarMeasure] 
    {ι : Type u_3} {φ : ι → ContDiffBump 0} {g : ι → G → E'} {k : ι → G} {x₀ : G} {z₀ : E'} {l : Filter ι}, 
    Tendsto (fun i => (φ i).rOut) l (𝓝 0) → 
    (∀ᶠ (i : ι) in l, MeasureTheory.AEStronglyMeasurable (g i) μ) → 
    Tendsto (Function.uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀) → 
    Tendsto k l (𝓝 x₀) → 
    Tendsto (fun i => MeasureTheory.convolution ((φ i).normed μ) (g i) (ContinuousLinearMap.lsmul ℝ ℝ) μ (k i)) l 
    (𝓝 z₀) :=
  @_root_.ContDiffBump.convolution_tendsto_right
