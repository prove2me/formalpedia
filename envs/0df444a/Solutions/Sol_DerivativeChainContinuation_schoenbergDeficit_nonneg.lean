-- Prove2me | solution 1 for DerivativeChainContinuation.schoenbergDeficit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:33:01.723747+00:00
-- url     : https://prove2.me/submissions/fdfaa326-1ee9-4623-a867-9c26391e228f

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_schoenbergDeficit_product_nonneg
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators

theorem roots_fin_product {n : ℕ} (a : Fin n → ℂ) :
    (∏ i, (X-C (a i))).roots = Finset.univ.val.map a := by
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod] using
    roots_multiset_prod_X_sub_C (Finset.univ.val.map a)







end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators







theorem exists_product_root_slots (p : Polynomial ℂ) (hp : p.Monic) :
    ∃ (n : ℕ) (a : Fin n → ℂ), p = ∏ i, (X-C (a i)) := by
  refine ⟨p.roots.toList.length, p.roots.toList.get, ?_⟩
  have he : Finset.univ.val.map p.roots.toList.get = p.roots := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have hh := congrArg (fun s : Multiset ℂ => (s.map fun z => X-C z).prod) he
  have hh' : (∏ i, (X-C (p.roots.toList.get i))) =
      (p.roots.map fun z => X-C z).prod := by
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod] using hh
  exact ((IsAlgClosed.splits p).eq_prod_roots_of_monic hp).trans hh'.symm



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) (hc : p.roots.sum = 0) :
    0 ≤ schoenbergDeficit p := by
  obtain ⟨n, a, rfl⟩ := exists_product_root_slots p hp
  have hn : 2 ≤ n := by simpa using hdeg
  have hca : ∑ i, a i = 0 := by
    rw [roots_fin_product] at hc
    exact hc
  exact schoenbergDeficit_product_nonneg hn a hca
