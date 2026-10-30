-- Prove2me | solution 1 for DerivativeChainContinuation.real_tower_cost_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:31:53.950983+00:00
-- url     : https://prove2.me/submissions/3324ef2d-7317-4955-afab-70f928a41d69

import Mathlib
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finiteEndpointCost_lipschitz
import Theorems.Thm_DerivativeChainContinuation_real_transport_mean
import Theorems.Thm_DerivativeChainContinuation_uniform_endpoint_second_moment
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation



theorem finiteEndpointCost_attained {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (x : ι → ℂ) (v : ℂ) :
    ∃ i, finiteEndpointCost c x v = c i + ‖x i-v‖ := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ
    (fun i => c i+‖x i-v‖) Finset.univ_nonempty
  refine ⟨i, le_antisymm ?_ ?_⟩
  · apply ciInf_le
    exact ⟨c i+‖x i-v‖, by rintro _ ⟨j,rfl⟩; exact hi j (Finset.mem_univ j)⟩
  · exact le_ciInf fun j => hi j (Finset.mem_univ j)



theorem finiteEndpointCost_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (x : ι → ℂ) (hc : ∀ i, 0 ≤ c i) (v : ℂ) :
    0 ≤ finiteEndpointCost c x v := by
  obtain ⟨i,hi⟩ := finiteEndpointCost_attained c x v
  rw [hi]
  exact add_nonneg (hc i) (norm_nonneg _)




end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators





theorem realHistoryCost_nonneg (r : RealRows) (k : ℕ) (v : ℝ) :
    0 ≤ realHistoryCost r k v := by
  induction k generalizing v with
  | zero => exact abs_nonneg _
  | succ k ih => exact finiteEndpointCost_nonneg _ _ (fun i => ih _) _

theorem realHistoryCost_lipschitz (r : RealRows) (k : ℕ) (v w : ℝ) :
    |realHistoryCost r k v-realHistoryCost r k w| ≤ |v-w| := by
  cases k with
  | zero =>
    simpa [realHistoryCost,sub_sub_sub_cancel_right] using
      abs_abs_sub_abs_le_abs_sub (v-r 0 0) (w-r 0 0)
  | succ k =>
    have h := finiteEndpointCost_lipschitz
      (fun i : Fin (k+1) => realHistoryCost r k (r k i)) (fun i => (r k i : ℂ))
      (v : ℂ) (w : ℂ)
    simpa [realHistoryCost,←Complex.ofReal_sub] using h








end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (r : RealRows) (n : ℕ) (hn : 0<n)
    (hstep : ∀ k<n,RealRowStep r k) (hc : ∑ i,r n i=0) :
    (∑ i,(realHistoryCost r n (r n i))^2) ≤ (28/3 : ℝ)*(∑ i,(r n i)^2) := by
  have hm := real_transport_mean r n hn hstep hc
  have hh := uniform_endpoint_second_moment (n+1) (by omega) (r n)
    (fun i => realHistoryCost r n (r n i)) hc (fun i => realHistoryCost_nonneg r n _)
    (fun i j => realHistoryCost_lipschitz r n _ _) (5/Real.sqrt 3) (by positivity)
    (by simpa [meanHistoryCost,Nat.cast_add,Nat.cast_one] using hm)
  have hs := Real.sq_sqrt (show (0 : ℝ)≤3 by norm_num)
  have hp : Real.sqrt (3 : ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he : 1+(5/Real.sqrt (3 : ℝ))^2=(28/3 : ℝ) := by
    field_simp
    nlinarith
  rw [he] at hh
  have hn1 : (0 : ℝ)<n+1 := by positivity
  apply (div_le_div_iff_of_pos_right hn1).mp
  simpa only [Nat.cast_add,Nat.cast_one,mul_div_assoc] using hh
