-- Prove2me | solution 1 for ChromaticReconstruction.reachable_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:41:17.803805+00:00
-- url     : https://prove2.me/submissions/25096ba4-ff34-4f13-bde0-455f5ef500c4

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
import Theorems.Thm_ChromaticReconstruction_reachable_map

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
namespace ChromaticReconstruction
theorem _root_.solution {A B : Set (Sym2 V)} (hAB : A ⊆ B) {u v : V}
    (huv : (SimpleGraph.fromEdgeSet A).Reachable u v) :
    (SimpleGraph.fromEdgeSet B).Reachable u v := by
  simpa using reachable_map id A B (fun u v h _ => Or.inr (hAB h)) huv
end ChromaticReconstruction
