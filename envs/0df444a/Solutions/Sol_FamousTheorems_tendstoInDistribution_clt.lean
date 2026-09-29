-- Prove2me | solution 1 for FamousTheorems.tendstoInDistribution_clt
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:06:24.8378+00:00
-- url     : https://prove2.me/submissions/f18dd621-68cc-4145-83da-8133f04a452e

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

theorem solution {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hY : HasLaw Y (gaussianReal 0 (Var[X 0; P]).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P' :=
  ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident
