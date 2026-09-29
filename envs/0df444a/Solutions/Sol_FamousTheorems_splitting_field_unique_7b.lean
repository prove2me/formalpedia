-- Prove2me | solution 1 for FamousTheorems.splitting_field_unique_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:39:38.133986+00:00
-- url     : https://prove2.me/submissions/77482445-fbad-4b71-a21b-911221689cc5

import Mathlib

theorem solution {K : Type*} (L M : Type*) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (f : Polynomial K) [Polynomial.IsSplittingField K L f] [Polynomial.IsSplittingField K M f] :
    Nonempty (L ≃ₐ[K] M) :=
  ⟨(Polynomial.IsSplittingField.algEquiv L f).trans (Polynomial.IsSplittingField.algEquiv M f).symm⟩
