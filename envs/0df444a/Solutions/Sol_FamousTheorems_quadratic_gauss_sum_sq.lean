-- Prove2me | solution 1 for FamousTheorems.quadratic_gauss_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:12:44.742984+00:00
-- url     : https://prove2.me/submissions/c4209500-c4a9-4bc0-bed9-b15692d6ddbc

import Mathlib

theorem solution {R : Type*} [Field R] [Fintype R] {R' : Type*} [CommRing R'] [IsDomain R'] {χ : MulChar R R'}
    (hχ₁ : χ ≠ 1) (hχ : χ.IsQuadratic) {ψ : AddChar R R'} (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R :=
  gaussSum_sq hχ₁ hχ hψ
