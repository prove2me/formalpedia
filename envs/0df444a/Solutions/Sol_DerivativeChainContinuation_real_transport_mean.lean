-- Prove2me | solution 1 for DerivativeChainContinuation.real_transport_mean
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:27:20.267261+00:00
-- url     : https://prove2.me/submissions/82c63e0b-eb03-4b24-9ddb-928b98db4afc

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_real_tower_square_profile
import Theorems.Thm_DerivativeChainContinuation_transport_mean_from_square_profile
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


open DerivativeChainContinuation in
theorem solution (r : RealRows) (n : ℕ) (hn : 0<n)
    (hstep : ∀ k<n,RealRowStep r k) (hc : ∑ i,r n i=0) :
    meanHistoryCost r n ≤ (5/Real.sqrt 3)*Real.sqrt ((∑ i,(r n i)^2)/(n+1 : ℝ)) := by
  let S : ℝ := ∑ i,(r n i)^2
  let K : ℝ := Real.sqrt (S/(3*(n : ℝ)*(n+1)))
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hn1 : (0 : ℝ)<n+1 := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hKsq : K^2=S/(3*(n : ℝ)*(n+1)) := Real.sq_sqrt (by positivity)
  have hsquare : ∀ k≤n, ∑ i,(r k i)^2=3*(k : ℝ)*(k+1)*K^2 := by
    intro k hk
    have h := real_tower_square_profile r n hstep hc k hk
    rw [hKsq]
    dsimp [S]
    field_simp
    nlinarith [h]
  have hm := transport_mean_from_square_profile r n hn K hK hstep hsquare
  have he : Real.sqrt (n : ℝ)*K = Real.sqrt (S/(n+1 : ℝ))/Real.sqrt 3 := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hnR.le,hKsq,div_pow,
      Real.sq_sqrt (by positivity : 0 ≤ S/(n+1 : ℝ)),Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)]
    field_simp
  calc
    meanHistoryCost r n ≤ 5*Real.sqrt n*K := hm
    _ = (5/Real.sqrt 3)*Real.sqrt (S/(n+1 : ℝ)) := by rw [mul_assoc,he]; ring
