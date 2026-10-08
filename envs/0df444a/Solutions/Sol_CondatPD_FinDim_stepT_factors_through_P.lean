-- Prove2me | solution 1 for CondatPD.FinDim.stepT_factors_through_P
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T22:46:51.32805+00:00
-- url     : https://prove2.me/submissions/81a7b912-1025-48aa-8b2e-5c150d5eec95

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

set_option autoImplicit false

open InnerProductSpace

open CondatPD.FinDim in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (PG : X → X) (PH : Y → Y) (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) :
    ∀ z z' : X × Y, opP τ σ L z = opP τ σ L z' →
      stepT PG PH τ σ L z = stepT PG PH τ σ L z' := by
  intro z z' h
  have h1 : τ⁻¹ • z.1 - ContinuousLinearMap.adjoint L z.2
      = τ⁻¹ • z'.1 - ContinuousLinearMap.adjoint L z'.2 := congrArg Prod.fst h
  have h2 : -(L z.1) + σ⁻¹ • z.2 = -(L z'.1) + σ⁻¹ • z'.2 := congrArg Prod.snd h
  have key1 : ∀ w : X × Y, w.1 - τ • ContinuousLinearMap.adjoint L w.2
      = τ • (τ⁻¹ • w.1 - ContinuousLinearMap.adjoint L w.2) := by
    intro w
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have key2 : ∀ (w : X × Y) (a : X), w.2 + σ • L ((2 : ℝ) • a - w.1)
      = σ • (-(L w.1) + σ⁻¹ • w.2) + σ • L ((2 : ℝ) • a) := by
    intro w a
    rw [map_sub, smul_add, smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
    abel
  have hx : PG (z.1 - τ • ContinuousLinearMap.adjoint L z.2)
      = PG (z'.1 - τ • ContinuousLinearMap.adjoint L z'.2) := by
    rw [key1 z, key1 z', h1]
  simp only [stepT]
  rw [key2 z, key2 z', h2, hx]
