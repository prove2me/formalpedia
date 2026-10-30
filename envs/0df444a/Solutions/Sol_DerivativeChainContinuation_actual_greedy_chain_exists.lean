-- Prove2me | solution 1 for DerivativeChainContinuation.actual_greedy_chain_exists
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:10:05.990282+00:00
-- url     : https://prove2.me/submissions/d83b1505-c16c-494a-a22b-d1329a6244f5

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyActual
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators













theorem complex_iterate_derivative_natDegree (p : Polynomial ℂ) (j : ℕ) :
    (derivative^[j] p).natDegree=p.natDegree-j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',natDegree_derivative,ih]
    omega










end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp

theorem actual_complex_row_natDegree {n : ℕ} (a : Fin (n+1) → ℂ)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) : (row a m).natDegree=m := by
  rw [row,complex_iterate_derivative_natDegree,actual_complex_source_natDegree]
  omega






















end DerivativeChainContinuation

theorem solution (n : ℕ) (a : Fin (n+1) → ℂ) :
    ∃ z : Fin (n+1) → ℂ,IsGreedyChain a z := by
  classical
  have hrowroot (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) :
      ∃ w : ℂ,(row a m).eval w=0 := by
    apply Complex.exists_root (f := row a m)
    apply Polynomial.natDegree_pos_iff_degree_pos.mp
    rw [actual_complex_row_natDegree a m hm hmn]
    omega
  have hprefix (m : ℕ) (hm : m ≤ n) :
      ∃ z : Fin (m+1) → ℂ,
        (∀ i : Fin (m+1),(row a (i.val+1)).eval (z i)=0) ∧
        ∀ i : Fin m,∀ w : ℂ,(row a (i.val+2)).eval w=0 →
          ‖z i.succ-z i.castSucc‖ ≤ ‖w-z i.castSucc‖ := by
    induction m with
    | zero =>
      obtain ⟨w,hw⟩ := hrowroot 1 (by omega) (by omega)
      refine ⟨fun _ => w,?_,?_⟩
      · intro i
        have he : i=0 := Fin.eq_zero i
        subst i
        exact hw
      · intro i
        exact Fin.elim0 i
    | succ m ih =>
      obtain ⟨z,hroots,hnear⟩ := ih (by omega)
      let S := {w : ℂ | (row a (m+2)).eval w=0}
      have hne : row a (m+2)≠0 := by
        intro he
        have hd := actual_complex_row_natDegree a (m+2) (by omega) (by omega)
        rw [he,natDegree_zero] at hd
        omega
      have hs : S.Finite := by
        simpa only [S,Polynomial.IsRoot] using Polynomial.finite_setOfPred_isRoot hne
      have hex : S.Nonempty := hrowroot (m+2) (by omega) (by omega)
      obtain ⟨v,hv,hmin⟩ := Set.exists_min_image S (fun w => ‖w-z (Fin.last m)‖) hs hex
      refine ⟨Fin.snoc z v,?_,?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa only [S,Set.mem_ofPred_eq,Fin.val_last,Fin.snoc_last] using hv
        | cast i => simpa only [Fin.val_castSucc,Fin.snoc_castSucc] using hroots i
      · intro i w hw
        induction i using Fin.lastCases with
        | last =>
          simpa only [Fin.val_last,Fin.succ_last,Fin.snoc_last,Fin.snoc_castSucc] using hmin w hw
        | cast i =>
          simpa only [Fin.val_castSucc,Fin.succ_castSucc,Fin.snoc_castSucc] using hnear i w hw
  obtain ⟨z,hroots,hnear⟩ := hprefix n le_rfl
  exact ⟨z,hroots,hnear⟩
