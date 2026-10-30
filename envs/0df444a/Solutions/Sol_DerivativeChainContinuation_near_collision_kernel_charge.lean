-- Prove2me | solution 1 for DerivativeChainContinuation.near_collision_kernel_charge
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:31:20.451013+00:00
-- url     : https://prove2.me/submissions/36fa25f3-2c4f-4f2a-9dc2-0c62967b671a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainContinuation_NearCollision
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_kernel_pair_bounds
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hK : ∀ i a, 0 ≤ K i a)
    (hKs : ∀ i, ∑ a, K i a=1) (hKm : ∀ i, ∑ a, (K i a:ℂ)*y a=x i) :
    nearCollisionCharge w x (kernelCost K x y) ≤
      (∑ i, ∑ j, w i*w j*kernelPairDistance K y i j)-finiteGini w x := by
  have hp (i j : ι) : max (kernelCost K x y i-2*‖x i-x j‖) 0 ≤
      kernelPairDistance K y i j-‖x i-x j‖ := by
    obtain ⟨h1,h2⟩ := kernel_pair_bounds K x y hK hKs hKm i j
    exact max_le (by linarith) (by linarith)
  unfold nearCollisionCharge finiteGini
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (hp i j) (mul_nonneg (hw i) (hw j))
