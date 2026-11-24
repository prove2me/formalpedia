-- Prove2me | solution 1 for ChromaticReconstruction.neighborFinset_eq_of_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:39:15.21527+00:00
-- url     : https://prove2.me/submissions/b21bee42-0af2-4b9b-a365-873e265ec810

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] {S : SimpleGraph K}
namespace ChromaticReconstruction
theorem _root_.solution {x y : K} (hx : S.degree x = 1) (hxy : S.Adj x y) :
    S.neighborFinset x = {y} := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, card_eq_one] at hx
  obtain ⟨z, hz⟩ := hx
  have : y ∈ S.neighborFinset x := (S.mem_neighborFinset x y).2 hxy
  rw [hz, mem_singleton] at this
  rw [hz, this]
end ChromaticReconstruction
