-- Prove2me | solution 1 for DerivativeChainContinuation.positive_quotient_sorted_factor
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:38:55.984036+00:00
-- url     : https://prove2.me/submissions/cd30a963-2fe5-40b1-b85e-6f005eb7493b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (Q : Polynomial ℝ) (hQ : PositiveQuotient Q) :
    ∃ n : ℕ,∃ a : Fin n → ℝ, Monotone a ∧ (∀ i,0<a i) ∧
      n=Q.natDegree ∧ Q=C Q.leadingCoeff*realRootProduct a := by
  classical
  let l := Q.roots.sort (·≤·)
  have hl : (l : Multiset ℝ)=Q.roots := Multiset.sort_eq _ _
  have hlen : l.length=Q.natDegree := by
    have hc := congrArg Multiset.card hl
    simpa only [Multiset.coe_card,←hQ.2.1.natDegree_eq_card_roots] using hc
  have hm : Monotone l.get := (Multiset.pairwise_sort Q.roots (·≤·)).sortedLE
  have hp (i : Fin l.length) : 0<l.get i := by
    apply hQ.2.2
    rw [←hl]
    exact List.get_mem _ _
  have hprod : realRootProduct l.get=
      (Q.roots.map (fun x => (X-C x : Polynomial ℝ))).prod := by
    rw [←hl]
    change (∏ i,(X-C (l.get i) : Polynomial ℝ))=(l.map (fun x => X-C x)).prod
    have h := Fin.prod_ofFn (fun i : Fin l.length => (X-C (l.get i) : Polynomial ℝ))
    change (List.ofFn ((fun x : ℝ => (X-C x : Polynomial ℝ)) ∘ l.get)).prod=_ at h
    rw [←List.map_ofFn,List.ofFn_get] at h
    exact h.symm
  refine ⟨l.length,l.get,hm,hp,hlen,?_⟩
  rw [hprod]
  exact (C_leadingCoeff_mul_prod_multiset_X_sub_C hQ.2.1.natDegree_eq_card_roots.symm).symm
