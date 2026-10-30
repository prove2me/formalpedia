-- Prove2me | solution 1 for DerivativeChainContinuation.transport_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:21:56.088351+00:00
-- url     : https://prove2.me/submissions/bab0324f-8a1d-4beb-92e4-3d37a50ad878

import Mathlib
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_mean_cost_transport_step
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


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









theorem realHistoryCost_step (r : RealRows) (k : ℕ) (v : ℝ) (i : Fin (k+1)) :
    realHistoryCost r (k+1) v ≤ realHistoryCost r k (r k i)+|v-r k i| := by
  have h := finiteEndpointCost_le
    (fun i : Fin (k+1) => realHistoryCost r k (r k i)) (fun i => (r k i : ℂ))
    (v : ℂ) i
  simpa [realHistoryCost,←Complex.ofReal_sub,abs_sub_comm] using h

theorem meanHistoryCost_zero (r : RealRows) : meanHistoryCost r 0 = 0 := by
  simp [meanHistoryCost,realHistoryCost]

theorem meanHistoryCost_step (r : RealRows) (k : ℕ) (h : RealRowStep r k) :
    meanHistoryCost r (k+1) ≤ meanHistoryCost r k +
      (orderedDispersion (r (k+1))-orderedDispersion (r k))/((k+1 : ℝ)*(k+2)) := by
  have hh := mean_cost_transport_step (k+1) (by omega)
    (r (k+1)) (r k) (fun i => realHistoryCost r (k+1) (r (k+1) i))
    (fun i => realHistoryCost r k (r k i)) h.1
    (fun i => by simpa only [abs_sub_comm] using realHistoryCost_step r k (r (k+1) i.castSucc) i)
    (fun i => realHistoryCost_step r k (r (k+1) i.succ) i)
  norm_num [meanHistoryCost,Nat.cast_add,Nat.cast_one,add_assoc] at hh ⊢
  exact hh


end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators

theorem inverse_sqrt_step (x : ℝ) (hx : 0 ≤ x) :
    1/Real.sqrt (x+1) ≤ 2*(Real.sqrt (x+1)-Real.sqrt x) := by
  have hp : 0 < Real.sqrt (x+1) := Real.sqrt_pos.mpr (by linarith)
  have hs := Real.sq_sqrt hx
  have ht := Real.sq_sqrt (show 0 ≤ x+1 by linarith)
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (Real.sqrt (x+1)-Real.sqrt x)]




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (r : RealRows) (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hstep : ∀ k<n+1,RealRowStep r k)
    (hD : ∀ k≤n+1,orderedDispersion (r k) ≤ (k : ℝ)*(k+1)*Real.sqrt (k+2)*K) :
    meanHistoryCost r (n+1) ≤
      orderedDispersion (r (n+1))/((n+1 : ℝ)*(n+2))+
        4*K*(Real.sqrt (n+2)-Real.sqrt 2) := by
  induction n with
  | zero =>
    have h := meanHistoryCost_step r 0 (hstep 0 (by omega))
    have hd0 : orderedDispersion (r 0)=0 := by simp [orderedDispersion]
    simpa [meanHistoryCost_zero,hd0] using h
  | succ n ih =>
    have hold := ih (fun k hk => hstep k (by omega)) (fun k hk => hD k (by omega))
    have hnew := meanHistoryCost_step r (n+1) (hstep (n+1) (by omega))
    have hd := hD (n+1) (by omega)
    have h1 : (0 : ℝ)<n+1 := by positivity
    have h2 : (0 : ℝ)<n+2 := by positivity
    have h3 : (0 : ℝ)<n+3 := by positivity
    have hspos : 0<Real.sqrt (n+3 : ℝ) := Real.sqrt_pos.mpr h3
    have hs := Real.sq_sqrt h3.le
    have hint := inverse_sqrt_step (n+2 : ℝ) h2.le
    have hd' : 2*orderedDispersion (r (n+1))/((n+1 : ℝ)*(n+2)*(n+3)) ≤
        2*K/Real.sqrt (n+3 : ℝ) := by
      apply (div_le_div_iff₀ (mul_pos (mul_pos h1 h2) h3) hspos).mpr
      have hh := mul_le_mul_of_nonneg_right hd (show 0 ≤ 2*Real.sqrt (n+3 : ℝ) by positivity)
      norm_num only [Nat.cast_add,Nat.cast_one] at hh
      have he : ((n+1 : ℝ)*(n+1+1)*Real.sqrt (n+1+2)*K)*(2*Real.sqrt (n+3 : ℝ)) =
          (2*K)*((n+1 : ℝ)*(n+2)*(n+3)) := by
        have hi : (n : ℝ)+1+2=n+3 := by ring
        rw [hi]
        calc
          _ = 2*K*(n+1)*(n+2)*(Real.sqrt (n+3 : ℝ))^2 := by ring
          _ = _ := by rw [hs]; ring
      rw [he] at hh
      nlinarith
    have heq : orderedDispersion (r (n+1))/((n+1 : ℝ)*(n+2)) +
        (orderedDispersion (r (n+2))-orderedDispersion (r (n+1)))/((n+2 : ℝ)*(n+3)) =
        orderedDispersion (r (n+2))/((n+2 : ℝ)*(n+3)) +
        2*orderedDispersion (r (n+1))/((n+1 : ℝ)*(n+2)*(n+3)) := by
      field_simp
      ring
    have hpay : 2*K/Real.sqrt (n+3 : ℝ) ≤
        4*K*(Real.sqrt (n+3 : ℝ)-Real.sqrt (n+2 : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hint (show 0≤2*K by positivity)
      norm_num [add_assoc] at h
      simp only [div_eq_mul_inv] at h ⊢
      nlinarith [h]
    norm_num [Nat.add_assoc,Nat.cast_add,Nat.cast_one,add_assoc] at hnew hold ⊢
    linarith [heq,hd'.trans hpay]
