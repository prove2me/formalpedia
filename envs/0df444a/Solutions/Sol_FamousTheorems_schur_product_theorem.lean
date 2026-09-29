-- Prove2me | solution 1 for FamousTheorems.schur_product_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:25:26.040224+00:00
-- url     : https://prove2.me/submissions/15f2dac2-63bb-4080-8019-3f6d3875186f

import Mathlib

open scoped ComplexOrder

theorem solution {𝕜 ι : Type*} [RCLike 𝕜] {A B : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A.hadamard B).PosSemidef :=
  hA.hadamard hB
