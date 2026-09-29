-- Prove2me | solution 1 for FamousTheorems.algebraic_closure_unique_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:33:03.889109+00:00
-- url     : https://prove2.me/submissions/c2cfe2f3-fea8-4c61-8720-bffe4d064d6e

import Mathlib

theorem solution (K L M : Type*) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [IsAlgClosure K L] [IsAlgClosure K M] : Nonempty (L ≃ₐ[K] M) :=
  ⟨IsAlgClosure.equiv K L M⟩
