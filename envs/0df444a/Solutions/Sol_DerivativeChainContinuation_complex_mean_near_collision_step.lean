-- Prove2me | solution 1 for DerivativeChainContinuation.complex_mean_near_collision_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:41:20.494466+00:00
-- url     : https://prove2.me/submissions/84b55f29-048a-47be-ba02-13cc1687a3af

import Mathlib
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainContinuation_NearCollision
import Definitions.Def_DerivativeChainContinuation_NearCollisionTower
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_kernel_mean_cost_bound
import Theorems.Thm_DerivativeChainContinuation_mixture_gini
import Theorems.Thm_DerivativeChainContinuation_near_collision_kernel_charge
import Theorems.Thm_DerivativeChainContinuation_near_collision_local_mass
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
namespace DerivativeChainContinuation





theorem finiteEndpointCost_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (x : ι → ℂ) (v : ℂ) (i : ι) :
    finiteEndpointCost c x v ≤ c i+‖x i-v‖ := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ
    (fun j => c j+‖x j-v‖) Finset.univ_nonempty
  apply ciInf_le
  exact ⟨c j+‖x j-v‖, by rintro _ ⟨k,rfl⟩; exact hj k (Finset.mem_univ k)⟩






end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



theorem near_collision_martingale_inequality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hK : ∀ i a, 0 ≤ K i a)
    (hKs : ∀ i, ∑ a, K i a=1) (hKm : ∀ i, ∑ a, (K i a:ℂ)*y a=x i) :
    nearCollisionCharge w x (kernelCost K x y) ≤
      finiteGini (fun a => ∑ i, w i*K i a) y-finiteGini w x := by
  rw [mixture_gini]
  exact near_collision_kernel_charge w K x y hw hK hKs hKm

theorem near_collision_step_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1)
    (hK : ∀ i a, 0 ≤ K i a) (hKs : ∀ i, ∑ a, K i a=1)
    (hKm : ∀ i, ∑ a, (K i a:ℂ)*y a=x i)
    (r a : ℝ) (ha : 0 < a)
    (hmass : ∀ i, a ≤ ∑ j, if ‖x i-x j‖ ≤ r then w j else 0) :
    (∑ i, w i*kernelCost K x y i) ≤ 2*r+
      (finiteGini (fun b => ∑ i, w i*K i b) y-finiteGini w x)/a := by
  have hl := near_collision_local_mass w x (kernelCost K x y) r a hw hs ha.le hmass
  have hu := near_collision_martingale_inequality w K x y hw hK hKs hKm
  have hh : ((∑ i, w i*kernelCost K x y i)-2*r) ≤
      (finiteGini (fun b => ∑ i, w i*K i b) y-finiteGini w x)/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  linarith
end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (r : ComplexRootRows) (k : ℕ)
    (hstep : UniformPolynomialStep r k) (ρ α : ℝ) (ha : 0 < α)
    (hmass : ∀ i, α ≤ rowLocalMass r k ρ i) :
    complexMeanCost r (k+1) ≤ complexMeanCost r k+2*ρ+
      (uniformSlotGini r (k+1)-uniformSlotGini r k)/α := by
  obtain ⟨_,K,hK,hKs,hKm,hKcol⟩ := hstep
  let w : Fin (k+1) → ℝ := fun _ => (k+1:ℝ)⁻¹
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; positivity
  have hs : ∑ i, w i=1 := by simp [w, show (k:ℝ)+1 ≠ 0 by positivity]
  have hcost (i : Fin (k+1)) (j : Fin (k+2)) :
      complexRowHistoryCost r (k+1) (r (k+1) j) ≤
        complexRowHistoryCost r k (r k i)+‖r (k+1) j-r k i‖ := by
    simpa only [complexRowHistoryCost,norm_sub_rev] using finiteEndpointCost_le
      (fun i => complexRowHistoryCost r k (r k i)) (r k) (r (k+1) j) i
  have ht := kernel_mean_cost_bound w K (r k) (r (k+1))
    (fun i => complexRowHistoryCost r k (r k i))
    (fun j => complexRowHistoryCost r (k+1) (r (k+1) j)) hw hK hKs hcost
  have hb := near_collision_step_bound w K (r k) (r (k+1)) hw hs hK hKs hKm ρ α ha hmass
  have hm (j : Fin (k+2)) : (∑ i, w i*K i j)=(k+2:ℝ)⁻¹ := hKcol j
  simp only [hm] at ht hb
  have ht' : complexMeanCost r (k+1) ≤ complexMeanCost r k+
      (∑ i, w i*kernelCost K (r k) (r (k+1)) i) := by
    convert ht using 1 <;> norm_num [complexMeanCost,w,Nat.cast_add,Nat.cast_one,add_assoc]
  have hb' : (∑ i, w i*kernelCost K (r k) (r (k+1)) i) ≤
      2*ρ+(uniformSlotGini r (k+1)-uniformSlotGini r k)/α := by
    convert hb using 1 <;> norm_num [uniformSlotGini,w,Nat.cast_add,Nat.cast_one,add_assoc]
  linarith
