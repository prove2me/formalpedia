-- Prove2me | solution 1 for GambiniPullin.diskModelIntegral_sigma_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T04:41:29.769915+00:00
-- url     : https://prove2.me/submissions/d549e81d-46dc-46b6-bb4f-f63f90b686e5

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

set_option autoImplicit false

open MeasureTheory Filter GambiniPullin in
theorem solution (R : ℝ) : diskModelIntegral 0 R = 0 := by
  unfold diskModelIntegral
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2} with hS
  have hpre : Prod.swap ⁻¹' S = S := by
    ext p
    simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap]
    rw [add_comm]
  have hodd : ∀ p : ℝ × ℝ,
      modelIntegrand 0 (Prod.swap p).1 (Prod.swap p).2 = -modelIntegrand 0 p.1 p.2 := by
    intro p
    simp only [Prod.fst_swap, Prod.snd_swap, modelIntegrand, modelDenom, zero_mul, add_zero,
      div_one]
    rw [← neg_div]
    congr 1
    · ring
    · ring
  have key := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).setIntegral_preimage_emb
    (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding
    (fun p : ℝ × ℝ => modelIntegrand 0 p.1 p.2) S
  rw [hpre] at key
  simp only [hodd, integral_neg] at key
  rw [Measure.volume_eq_prod]
  linarith
