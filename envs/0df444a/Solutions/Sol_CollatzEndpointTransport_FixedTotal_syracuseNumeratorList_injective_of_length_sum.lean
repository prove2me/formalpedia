-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_injective_of_length_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:10.537931+00:00
-- url     : https://prove2.me/submissions/650358f2-a407-405b-9faa-3a6b1a6d4a94

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_mod_two
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_eq_exponent_of_pow_two_mul_eq
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (s : ℕ) :
    ∀ {ks ls : List ℕ},
      ks.length = s →
      ls.length = s →
      (∀ k ∈ ks, 0 < k) →
      (∀ l ∈ ls, 0 < l) →
      ks.sum = ls.sum →
      syracuseNumeratorList ks = syracuseNumeratorList ls →
      ks = ls := by
  induction s with
  | zero =>
      intro ks ls hks hls _ _ _ _
      have hksNil : ks = [] := List.length_eq_zero_iff.mp hks
      have hlsNil : ls = [] := List.length_eq_zero_iff.mp hls
      simpa [hksNil, hlsNil]
  | succ s ih =>
      intro ks ls hks hls hksPos hlsPos hsum hnum
      obtain ⟨k, kt, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < ks.length)
      obtain ⟨l, lt, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < ls.length)
      have hktLen : kt.length = s := by simpa using hks
      have hltLen : lt.length = s := by simpa using hls
      have hkPos : 0 < k := hksPos k (by simp)
      have hlPos : 0 < l := hlsPos l (by simp)
      have hktPos : ∀ x ∈ kt, 0 < x := by
        intro x hx
        exact hksPos x (by simp [hx])
      have hltPos : ∀ x ∈ lt, 0 < x := by
        intro x hx
        exact hlsPos x (by simp [hx])
      by_cases hs0 : s = 0
      · have hktZero : kt.length = 0 := hktLen.trans hs0
        have hltZero : lt.length = 0 := hltLen.trans hs0
        have hktNil : kt = [] := List.length_eq_zero_iff.mp hktZero
        have hltNil : lt = [] := List.length_eq_zero_iff.mp hltZero
        subst kt
        subst lt
        simp only [List.sum_cons, List.sum_nil, add_zero] at hsum
        subst l
        rfl
      · have hktNonempty : kt ≠ [] := by
          intro h
          rw [h, List.length_nil] at hktLen
          exact hs0 hktLen.symm
        have hltNonempty : lt ≠ [] := by
          intro h
          rw [h, List.length_nil] at hltLen
          exact hs0 hltLen.symm
        obtain ⟨k', ktt, hkt⟩ := List.exists_cons_of_ne_nil hktNonempty
        obtain ⟨l', ltt, hlt⟩ := List.exists_cons_of_ne_nil hltNonempty
        have hk'Pos : 0 < k' := by
          exact hktPos k' (hkt ▸ by simp)
        have hl'Pos : 0 < l' := by
          exact hltPos l' (hlt ▸ by simp)
        have htailMul :
            2 ^ k * syracuseNumeratorList kt =
              2 ^ l * syracuseNumeratorList lt := by
          rw [syracuseNumeratorList_cons, syracuseNumeratorList_cons] at hnum
          have hpowLen : 3 ^ kt.length = 3 ^ lt.length := by
            rw [hktLen, hltLen]
          omega
        have hfirst : k = l := by
          apply eq_exponent_of_pow_two_mul_eq
          · exact hkt ▸ syracuseNumeratorList_mod_two hk'Pos ktt
          · exact hlt ▸ syracuseNumeratorList_mod_two hl'Pos ltt
          · exact htailMul
        have htailNum :
            syracuseNumeratorList kt = syracuseNumeratorList lt := by
          subst l
          exact Nat.eq_of_mul_eq_mul_left
            (pow_pos (by norm_num : 0 < (2 : ℕ)) k) htailMul
        have htailSum : kt.sum = lt.sum := by
          subst l
          simpa using hsum
        have htailEq :
            kt = lt :=
          ih hktLen hltLen hktPos hltPos htailSum htailNum
        simpa [hfirst, htailEq]
end CollatzEndpointTransport.FixedTotal
