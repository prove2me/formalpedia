-- Prove2me | solution 1 for DerivativeChainContinuation.positive_quotient_outer_root
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:26:44.198711+00:00
-- url     : https://prove2.me/submissions/30a004b6-b409-4c5e-845e-90ae0aea8cd1

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (Q : Polynomial ℝ) (hQ : PositiveQuotient Q)
    (hQdegree : 0<Q.natDegree) :
    ∃ b : ℝ,0<b ∧ Q.eval b=0 ∧ ∀ y : ℝ,Q.eval y=0 → y ≤ b := by
  classical
  have hne : Q.roots≠0 := by
    intro h
    have hc := hQ.2.1.natDegree_eq_card_roots
    rw [h,Multiset.card_zero] at hc
    omega
  obtain ⟨a,ha⟩ := Multiset.exists_mem_of_ne_zero hne
  let S := Q.roots.toFinset
  have hs : S.Nonempty := ⟨a,by simpa only [S,Multiset.mem_toFinset] using ha⟩
  let b := S.max' hs
  have hbmem : b∈Q.roots := by
    have h := Finset.max'_mem S hs
    simpa only [S,Multiset.mem_toFinset] using h
  refine ⟨b,hQ.2.2 b hbmem,(mem_roots hQ.1).mp hbmem,?_⟩
  intro y hy
  exact Finset.le_max' S y (by simpa only [S,Multiset.mem_toFinset] using (mem_roots hQ.1).mpr hy)
