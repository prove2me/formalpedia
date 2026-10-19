-- Prove2me | solution 1 for CompactnessConjecture.inJCopy_iff_exists_jThetaVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/16dec4a8-88ee-43f6-815c-c0080cb7be86

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (copy : Fin 2) (vertex : JVertex) :
    InJCopy copy vertex ↔
      ∃ source : SubdivisionVertex 2,
        jThetaVertex copy source = vertex := by
  constructor
  · intro h
    rcases vertex with (base | center) | (pair | joining)
    · obtain ⟨source, hsource⟩ := h
      refine ⟨.inl (.inl source), ?_⟩
      simpa [jThetaVertex] using congrArg
        (fun value : Fin 4 => (Sum.inl (Sum.inl value) : JVertex))
        hsource.symm
    · rcases center with ⟨index, center⟩
      change copy = index at h
      subst index
      exact ⟨.inl (.inr center), rfl⟩
    · rcases pair with ⟨index, base, center⟩
      change copy = index at h
      subst index
      exact ⟨.inr (base, center), rfl⟩
    · exact False.elim h
  · rintro ⟨source, rfl⟩
    exact jThetaVertex_mem copy source
end CompactnessConjecture
