-- Prove2me | solution 1 for FairSelling.disjoint_compl_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:11:34.978801+00:00
-- url     : https://prove2.me/submissions/ed015edd-7d76-4742-9c71-421202cc9bff

import Mathlib
variable {G : Type*} [Fintype G] [DecidableEq G]


theorem solution {Y U : Finset G} (hYU : Y ⊆ U) :
    Disjoint Y (Finset.univ \ U) := by
  exact Finset.disjoint_left.mpr fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hYU hx)
