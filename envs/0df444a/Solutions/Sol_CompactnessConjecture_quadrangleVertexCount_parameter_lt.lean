-- Prove2me | solution 1 for CompactnessConjecture.quadrangleVertexCount_parameter_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/bb997cad-1931-447a-be19-335584fbd107

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution (q : ℕ) :
    q < quadrangleVertexCount q := by
  unfold quadrangleVertexCount
  nlinarith [sq_nonneg q]
end CompactnessConjecture
