-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.cohortCriticalNumerator_eq_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:38.685741+00:00
-- url     : https://prove2.me/submissions/e1a69f58-ec52-4444-81f9-32f555afeb15

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_sqrt_mapFiberCardAt_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortEndpoint_mapFiberCardAt_eq_numerator
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_cohortNumerator_mapFiber_eq_residueFiber

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (u : Fin M) (s : ℕ) :
    cohortCriticalNumerator M u s =
      fixedCriticalNumerator (M - (u : ℕ)) s := by
  let W := fixedSet (M - (u : ℕ)) s
  let f := cohortEndpoint u
  let g : Composition (M - (u : ℕ)) → Fin (3 ^ s) :=
    cohortNumeratorResidue
  have hsum :
      (∑ c ∈ W, Real.sqrt (mapFiberCardAt W f c)) =
        ∑ c ∈ W, Real.sqrt (mapFiberCardAt W g c) := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [cohortEndpoint_mapFiberCardAt_eq_numerator u hc]
  have hreindex :
      (∑ c ∈ W, Real.sqrt (mapFiberCardAt W g c)) =
        ∑ a : Fin (3 ^ s),
          (fixedFiberCard (M - (u : ℕ)) s a : ℝ) *
            Real.sqrt (fixedFiberCard (M - (u : ℕ)) s a) := by
    rw [sum_sqrt_mapFiberCardAt_eq W g]
    apply Finset.sum_congr rfl
    intro a ha
    rw [cohortNumerator_mapFiber_eq_residueFiber]
    rfl
  calc
    cohortCriticalNumerator M u s =
        Real.sqrt (3 ^ s) *
          ∑ c ∈ W, Real.sqrt (mapFiberCardAt W f c) := by
      rfl
    _ = Real.sqrt (3 ^ s) *
          ∑ c ∈ W, Real.sqrt (mapFiberCardAt W g c) := by rw [hsum]
    _ = fixedCriticalNumerator (M - (u : ℕ)) s := by
      rw [hreindex]
      rfl
end CollatzEndpointTransport.FixedTotal
