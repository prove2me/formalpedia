-- Prove2me | solution 1 for DerivativeChainContinuation.complexRowHistoryCost_attained
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:33:28.114803+00:00
-- url     : https://prove2.me/submissions/e5df7e11-842e-4bb2-bfde-813d9cf265b3

import Mathlib
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_EndpointCost
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


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
open Polynomial DerivativeChainPrivate
open scoped BigOperators





theorem complex_chainCost_snoc {n : ℕ} (z : Fin (n+1) → ℂ) (v : ℂ) :
    chainCost (Fin.snoc z v)=chainCost z+‖v-z (Fin.last n)‖ := by
  change (∑ i : Fin (n+1), ‖(Fin.snoc z v : Fin (n+2) → ℂ) i.succ-(Fin.snoc z v : Fin (n+2) → ℂ) i.castSucc‖)=
    (∑ i : Fin n, ‖z i.succ-z i.castSucc‖)+‖v-z (Fin.last n)‖
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.succ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,Fin.succ_last]






end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (r : ComplexRootRows) (n : ℕ) (v : ℂ)
    (hv : ∃ j : Fin (n+1), v=r n j) :
    ∃ z : Fin (n+1) → ℂ, IsComplexRowHistory r z ∧ z (Fin.last n)=v ∧
      chainCost z=complexRowHistoryCost r n v := by
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
    · simp [chainCost,complexRowHistoryCost]
  | succ n ih =>
    obtain ⟨j,hj⟩ := finiteEndpointCost_attained
      (fun i : Fin (n+1) => complexRowHistoryCost r n (r n i)) (r n) v
    obtain ⟨z,hz,hend,hcost⟩ := ih (r n j) ⟨j,rfl⟩
    refine ⟨Fin.snoc z v,?_,by simp,?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last,Fin.val_last] using hv
      | cast i => simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hz i
    · rw [complex_chainCost_snoc,hcost,hend]
      simpa only [complexRowHistoryCost,norm_sub_rev] using hj.symm
