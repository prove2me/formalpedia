-- Prove2me | solution 1 for DerivativeChainContinuation.realHistoryCost_attained
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T16:48:39.614988+00:00
-- url     : https://prove2.me/submissions/1aa28451-4f18-463d-aea5-5ce59bd36f18

import Mathlib
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainContinuation_RealEndpointCost
import Definitions.Def_DerivativeChainContinuation_RealHistories
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
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








end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators







theorem realChainCost_snoc {n : ℕ} (z : Fin (n+1) → ℝ) (v : ℝ) :
    realChainCost (Fin.snoc z v)=realChainCost z+|v-z (Fin.last n)| := by
  unfold realChainCost
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.succ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,Fin.succ_last]




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (r : RealRows) (n : ℕ) (v : ℝ)
    (hv : ∃ j : Fin (n+1), v=r n j) :
    ∃ z : Fin (n+1) → ℝ, IsRowHistory r z ∧ z (Fin.last n)=v ∧
      realChainCost z=realHistoryCost r n v := by
  induction n generalizing v with
  | zero =>
    obtain ⟨j,rfl⟩ := hv
    have hj : j=0 := Fin.eq_zero j
    subst j
    refine ⟨fun _ => r 0 0,?_,rfl,?_⟩
    · intro i
      have hi : i=0 := Fin.eq_zero i
      subst i
      exact ⟨0,rfl⟩
    · simp [realChainCost,realHistoryCost]
  | succ n ih =>
    obtain ⟨j,hj⟩ := finiteEndpointCost_attained
      (fun i : Fin (n+1) => realHistoryCost r n (r n i)) (fun i => (r n i : ℂ)) (v : ℂ)
    obtain ⟨z,hz,hend,hcost⟩ := ih (r n j) ⟨j,rfl⟩
    refine ⟨Fin.snoc z v,?_,by simp,?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simpa only [Fin.snoc_last,Fin.val_last] using hv
      | cast i =>
        simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hz i
    · rw [realChainCost_snoc,hcost,hend]
      simpa only [realHistoryCost,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        abs_sub_comm] using hj.symm
