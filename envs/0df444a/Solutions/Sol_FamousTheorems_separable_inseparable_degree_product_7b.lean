-- Prove2me | solution 1 for FamousTheorems.separable_inseparable_degree_product_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:04:36.395982+00:00
-- url     : https://prove2.me/submissions/53a243d9-2144-48de-8bdf-55a8f8a1e382

import Mathlib

theorem solution (F E : Type*) [Field F] [Field E] [Algebra F E] :
    Field.finSepDegree F E * Field.finInsepDegree F E = Module.finrank F E :=
  Field.finSepDegree_mul_finInsepDegree F E
