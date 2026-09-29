-- Prove2me | solution 1 for FamousTheorems.steinitz_uncountable_alg_closed_classification_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:01:25.75698+00:00
-- url     : https://prove2.me/submissions/01d1f141-5916-4ec6-be1a-ba0e5eca8948

import Mathlib

theorem solution {K L : Type*} [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L] [CharZero K] [CharZero L]
    (hK : Cardinal.aleph0 < Cardinal.mk K) (hKL : Nonempty (K ≃ L)) : Nonempty (K ≃+* L) :=
  IsAlgClosed.ringEquiv_of_equiv_of_charZero hK hKL
