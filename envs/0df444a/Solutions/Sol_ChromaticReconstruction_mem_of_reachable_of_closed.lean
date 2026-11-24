-- Prove2me | solution 1 for ChromaticReconstruction.mem_of_reachable_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:07:47.34626+00:00
-- url     : https://prove2.me/submissions/c82fd3f1-18ef-4bf9-998e-ac9aee4a2d5a

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
namespace ChromaticReconstruction
theorem _root_.solution {A : Set (Sym2 V)} {B : Set V}
    (hclosed : ∀ u ∈ B, ∀ w, s(u, w) ∈ A → w ∈ B) {u v : V} (hu : u ∈ B)
    (huv : (SimpleGraph.fromEdgeSet A).Reachable u v) : v ∈ B := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => exact hu
  | tail _ hbc ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hbc
    exact hclosed _ ih _ hbc.1
end ChromaticReconstruction
