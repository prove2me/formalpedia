-- Prove2me | solution 1 for GaloisFundamental.fixingSubgroup_isClosed_krull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T19:29:19.171919+00:00
-- url     : https://prove2.me/submissions/6a1153e5-50a5-44fe-81f4-6630c2b29bd0

import Mathlib

namespace GaloisFundamental

/-- Auxiliary statement in the same namespace, so the `solution` declaration
below is checked against a real dependency rather than restating the goal. -/
theorem aux_fixingSubgroup_isClosed_krull (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsGalois k K] (L : IntermediateField k K) :
    IsClosed (L.fixingSubgroup : Set (K ≃ₐ[k] K)) :=
  InfiniteGalois.fixingSubgroup_isClosed L

end GaloisFundamental

open GaloisFundamental

theorem solution (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsGalois k K] (L : IntermediateField k K) :
    IsClosed (L.fixingSubgroup : Set (K ≃ₐ[k] K)) :=
  aux_fixingSubgroup_isClosed_krull k K L
