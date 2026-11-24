-- Prove2me | solution 1 for ChromaticReconstruction.reachable_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:07:37.57455+00:00
-- url     : https://prove2.me/submissions/ae842634-d254-4b02-9c12-1c076a7eb4bc

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
namespace ChromaticReconstruction
theorem _root_.solution {A : Set (Sym2 V)} {u v : V} (h : s(u, v) ∈ A) :
    (SimpleGraph.fromEdgeSet A).Reachable u v := by
  by_cases huv : u = v
  · subst huv; rfl
  · exact SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨h, huv⟩)
end ChromaticReconstruction
