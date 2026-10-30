-- Prove2me | solution 1 for DerivativeChainContinuation.strict_real_derivative_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:33:43.956995+00:00
-- url     : https://prove2.me/submissions/a0acf2f3-deb3-439c-9308-6d67891b4e4e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial
open scoped BigOperators



theorem realRootProduct_monic {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).Monic := Polynomial.monic_prod_X_sub_C a Finset.univ

theorem realRootProduct_degree {n : ℕ} (a : Fin n → ℝ) :
    (realRootProduct a).natDegree = n := by
  unfold realRootProduct
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (a i))]
  simp

theorem realRootProduct_eval {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    (realRootProduct a).eval (a i) = 0 := by
  simp only [realRootProduct, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+2) → ℝ)
    (ha : StrictMono a) :
    ∃ b : Fin (n+1) → ℝ, StrictMono b ∧
      (∀ i, a i.castSucc < b i ∧ b i < a i.succ) ∧
      (realRootProduct a).derivative = C (n+2 : ℝ) * realRootProduct b := by
  classical
  let p := realRootProduct a
  have hd : p.natDegree = n+2 := realRootProduct_degree a
  have hp : p.Monic := realRootProduct_monic a
  have hd' : p.derivative.natDegree = n+1 := by rw [natDegree_derivative, hd]; omega
  have hp' : p.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  have ex (i : Fin (n+1)) : ∃ b : ℝ, a i.castSucc < b ∧ b < a i.succ ∧ p.derivative.eval b=0 := by
    have hi : i.castSucc < i.succ := by exact Fin.castSucc_lt_succ
    obtain ⟨b,hb,hdb⟩ := exists_deriv_eq_zero (ha hi) p.continuousOn
      ((realRootProduct_eval a i.castSucc).trans (realRootProduct_eval a i.succ).symm)
    refine ⟨b,hb.1,hb.2,?_⟩
    simpa only [p.deriv] using hdb
  choose b hb using ex
  have hmono : StrictMono b := by
    intro i j hij
    have hle : i.succ ≤ j.castSucc := by simpa using hij
    exact (hb i).2.1.trans_le ((ha.monotone hle).trans (hb j).1.le)
  let s : Multiset ℝ := Finset.univ.val.map b
  have hnodup : s.Nodup := Finset.univ.nodup.map hmono.injective
  have hsub : s ≤ p.derivative.roots := by
    apply (Multiset.le_iff_subset hnodup).mpr
    intro x hx
    obtain ⟨i,_,rfl⟩ := Multiset.mem_map.mp hx
    exact (Polynomial.mem_roots hp').mpr (hb i).2.2
  have hcard : s.card = n+1 := by simp [s]
  have hle := p.derivative.card_roots'
  have heq : s = p.derivative.roots :=
    Multiset.eq_of_le_of_card_le hsub (by simpa [hd',hcard] using hle)
  have hc : p.derivative.roots.card = p.derivative.natDegree := by rw [←heq,hcard,hd']
  have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  have hlead : p.derivative.leadingCoeff = (n+2 : ℝ) := by
    rw [leadingCoeff_derivative, hp.leadingCoeff, one_mul,hd]; push_cast; rfl
  refine ⟨b,hmono,(fun i => ⟨(hb i).1,(hb i).2.1⟩),?_⟩
  rw [hlead,←heq] at hprod
  have hbprod : (s.map fun x => (X-C x : Polynomial ℝ)).prod = realRootProduct b := by
    simp only [s,Multiset.map_map,Function.comp_def]
    rfl
  rw [hbprod] at hprod
  change p.derivative = C (n+2 : ℝ)*realRootProduct b
  exact hprod.symm
