-- Prove2me | solution 1 for DerivativeChainContinuation.transport_mean_from_square_profile
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:24:44.70056+00:00
-- url     : https://prove2.me/submissions/8fb685c8-59f3-4bd8-9a0c-14c218f8daad

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_orderedDispersion_bound
import Theorems.Thm_DerivativeChainContinuation_sqrt_transport_constant
import Theorems.Thm_DerivativeChainContinuation_transport_potential_bound
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution (r : RealRows) (n : ℕ) (hn : 0<n)
    (K : ℝ) (hK : 0 ≤ K) (hstep : ∀ k<n,RealRowStep r k)
    (hsquare : ∀ k≤n, ∑ i,(r k i)^2=3*(k : ℝ)*(k+1)*K^2) :
    meanHistoryCost r n ≤ 5*Real.sqrt n*K := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hd : ∀ k≤j+1,orderedDispersion (r k) ≤ (k : ℝ)*(k+1)*Real.sqrt (k+2)*K :=
    fun k hk => orderedDispersion_bound k (r k) K hK (hsquare k hk)
  have hpot := transport_potential_bound r j K hK hstep hd
  have hpos : (0 : ℝ)<(j+1 : ℝ)*(j+2) := by positivity
  have hlast : orderedDispersion (r (j+1))/((j+1 : ℝ)*(j+2)) ≤ Real.sqrt (j+3 : ℝ)*K := by
    apply (div_le_iff₀ hpos).mpr
    have h := hd (j+1) (by omega)
    norm_num [Nat.cast_add,Nat.cast_one,add_assoc] at h
    nlinarith [h]
  have hc := mul_le_mul_of_nonneg_right (sqrt_transport_constant (j+1 : ℝ) (by positivity)) hK
  norm_num [Nat.cast_add,Nat.cast_one,add_assoc] at hc ⊢
  linarith
