-- Prove2me | solution 1 for DerivativeChainContinuation.kernel_mean_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:35:32.043597+00:00
-- url     : https://prove2.me/submissions/a9b53124-7335-41ce-8b88-4bd8171df3ac

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (f : ι → ℝ) (g : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hK : ∀ i a, 0 ≤ K i a) (hKs : ∀ i, ∑ a, K i a=1)
    (hcost : ∀ i a, g a ≤ f i+‖y a-x i‖) :
    (∑ a, (∑ i, w i*K i a)*g a) ≤ (∑ i, w i*f i)+(∑ i, w i*kernelCost K x y i) := by
  have hrow (i : ι) : (∑ a, K i a*g a) ≤ f i+kernelCost K x y i := by
    calc
      _ ≤ ∑ a, K i a*(f i+‖y a-x i‖) := Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (hcost i a) (hK i a)
      _ = _ := by simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hKs,one_mul,kernelCost]
  calc
    _ = ∑ i, w i*(∑ a, K i a*g a) := by
      simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]
      exact Finset.sum_comm
    _ ≤ ∑ i, w i*(f i+kernelCost K x y i) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hrow i) (hw i)
    _ = _ := by simp [mul_add,Finset.sum_add_distrib]
