-- Prove2me | solution 1 for DerivativeChainContinuation.mixture_gini
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:37:26.643458+00:00
-- url     : https://prove2.me/submissions/ec70e61e-3180-4205-8a09-5f13e95e7800

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
    (w : ι → ℝ) (K : ι → κ → ℝ) (y : κ → ℂ) :
    finiteGini (fun a => ∑ i, w i*K i a) y =
      ∑ i, ∑ j, w i*w j*kernelPairDistance K y i j := by
  classical
  unfold finiteGini kernelPairDistance
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset κ)) (t := (Finset.univ : Finset ι))]
  conv_rhs => rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring
