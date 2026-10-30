-- Prove2me | solution 1 for DerivativeChainPhaseLock.actual_endpoint_cost_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T06:46:30.661308+00:00
-- url     : https://prove2.me/submissions/68a4dfdb-1e18-42f0-9027-80c79c4eddf5

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_ComplexHistories
import Definitions.Def_DerivativeChainContinuation_UniformRootTower
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_complexEndpointCost_attained
import Theorems.Thm_DerivativeChainContinuation_complexRowHistoryCost_attained
import Theorems.Thm_DerivativeChainContinuation_complex_tower_factor
import Theorems.Thm_DerivativeChainContinuation_uniform_polynomial_tower
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


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





theorem complex_rowHistory_actual (r : ComplexRootRows) (n : ℕ)
    (hstep : ∀ k<n,UniformPolynomialStep r k) (z : Fin (n+1) → ℂ)
    (hz : IsComplexRowHistory r z) :
    ∀ i, (derivative^[n-i.val] (complexRowProduct r n)).eval (z i)=0 := by
  intro i
  obtain ⟨c,hc,heq⟩ := complex_tower_factor r n hstep i.val (by omega)
  obtain ⟨j,hj⟩ := hz i
  rw [heq,eval_mul,eval_C,hj]
  have he : (complexRowProduct r i.val).eval (r i.val j)=0 := by
    simp only [complexRowProduct,eval_prod,eval_sub,eval_X,eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
  rw [he,mul_zero]
end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open DerivativeChainContinuation DerivativeChainPrivate
namespace DerivativeChainPrefixLaws
noncomputable section

































theorem endpoint_cost_le_chain {n : ℕ} (a : Fin (n+1) → ℂ) (z : Fin (n+1) → ℂ)
    (hz : IsChain a z) : complexEndpointCost a (z (Fin.last n)) ≤ chainCost z := by
  unfold complexEndpointCost
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro t ⟨zz,hzz,he,rfl⟩
    unfold chainCost
    positivity
  · exact ⟨z,hz,rfl,rfl⟩

end
end DerivativeChainPrefixLaws



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainPrefixLaws
namespace DerivativeChainPhaseLock
noncomputable section

theorem actual_chain_at_source_slot {n : ℕ} (a : Fin (n+1) → ℂ) (j : Fin (n+1)) :
    ∃ z : Fin (n+1) → ℂ,IsChain a z ∧ z (Fin.last n)=a j := by
  obtain ⟨r,htop,hstep⟩ := uniform_polynomial_tower n a
  obtain ⟨z,hz,he,hcost⟩ := complexRowHistoryCost_attained r n (a j) ⟨j,by rw [htop]⟩
  refine ⟨z,?_,he⟩
  intro i
  have h := complex_rowHistory_actual r n hstep z hz i
  simpa only [row,complexRowProduct,htop,fromRoots,
    show n+1-(i.val+1)=n-i.val by omega] using h



end
end DerivativeChainPhaseLock



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
open Polynomial DerivativeChainPrivate DerivativeChainContinuation DerivativeChainPrefixLaws
open DerivativeChainPhaseLock




theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (i j : Fin (n+1)) :
    |_root_.DerivativeChainContinuation.complexEndpointCost a (a i)-_root_.DerivativeChainContinuation.complexEndpointCost a (a j)| ≤ ‖a i-a j‖ := by
  cases n with
  | zero => simp only [Fin.eq_zero i,Fin.eq_zero j,sub_self,abs_zero,norm_zero,le_refl]
  | succ n =>
    have hstep (i j : Fin (n+2)) : _root_.DerivativeChainContinuation.complexEndpointCost a (a j) ≤
        _root_.DerivativeChainContinuation.complexEndpointCost a (a i)+‖a i-a j‖ := by
      obtain ⟨z,hz,he,hcost⟩ := _root_.DerivativeChainContinuation.complexEndpointCost_attained a (a i) (_root_.DerivativeChainPhaseLock.actual_chain_at_source_slot a i)
      let zz : Fin (n+2) → ℂ := Fin.snoc (Fin.init z) (a j)
      have hzz : _root_.DerivativeChainPrivate.IsChain a zz := by
        intro k
        induction k using Fin.lastCases with
        | last =>
          simp only [zz,Fin.snoc_last,Fin.val_last,_root_.DerivativeChainPrivate.row,tsub_self,Function.iterate_zero_apply]
          simp only [_root_.DerivativeChainPrivate.fromRoots,eval_prod,eval_sub,eval_X,eval_C]
          exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self _)
        | cast k => simpa only [zz,Fin.snoc_castSucc,Fin.init,Fin.val_castSucc] using hz k.castSucc
      have hb := _root_.DerivativeChainPrefixLaws.endpoint_cost_le_chain a zz hzz
      have hlast : zz (Fin.last (n+1))=a j := by simp [zz]
      rw [hlast] at hb
      have heq : z=Fin.snoc (Fin.init z) (a i) := by
        funext k
        induction k using Fin.lastCases with
        | last => simpa only [Fin.snoc_last] using he
        | cast k => simp only [Fin.snoc_castSucc,Fin.init]
      have hc : _root_.DerivativeChainPrivate.chainCost zz ≤ _root_.DerivativeChainPrivate.chainCost z+‖a i-a j‖ := by
        conv_rhs => rw [heq,_root_.DerivativeChainContinuation.complex_chainCost_snoc]
        rw [show zz=Fin.snoc (Fin.init z) (a j) from rfl,_root_.DerivativeChainContinuation.complex_chainCost_snoc]
        have ht := norm_sub_le_norm_sub_add_norm_sub (a j) (a i) ((Fin.init z) (Fin.last n))
        rw [norm_sub_rev (a j) (a i)] at ht
        linarith
      exact hb.trans (by rwa [hcost] at hc)
    apply abs_le.mpr
    constructor
    · have h := hstep i j
      linarith
    · have h := hstep j i
      rw [norm_sub_rev (a j) (a i)] at h
      linarith
