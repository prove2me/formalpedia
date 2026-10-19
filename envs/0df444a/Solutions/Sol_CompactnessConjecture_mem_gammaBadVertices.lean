-- Prove2me | solution 1 for CompactnessConjecture.mem_gammaBadVertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/29ed8263-36d4-49a5-964f-80a5498e7dca

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution (G : SimpleGraph V) (v : V) :
    v ∈ gammaBadVertices G ↔ ¬ GammaGood G v := by
  classical
  simp [gammaBadVertices]
end CompactnessConjecture
