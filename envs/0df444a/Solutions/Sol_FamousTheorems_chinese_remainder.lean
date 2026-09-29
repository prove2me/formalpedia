-- Prove2me | solution 1 for FamousTheorems.chinese_remainder
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T01:51:16.50637+00:00
-- url     : https://prove2.me/submissions/aa9a00bc-43fa-4df7-adcf-2b37ea8bf20a

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

theorem solution {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → Ideal R) (hf : Pairwise (Function.onFun IsCoprime f)) :
    Nonempty ((R ⧸ ⨅ i, f i) ≃+* ∀ i, R ⧸ f i) :=
  ⟨Ideal.quotientInfRingEquivPiQuotient f hf⟩
