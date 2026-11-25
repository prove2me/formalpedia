-- Prove2me | solution 1 for ChromaticReconstruction.miso_of_multiplicityIsolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:10:31.805078+00:00
-- url     : https://prove2.me/submissions/1cea6a3a-ac62-447b-9769-a50bc126ab6a

import Definitions.Def_RequestProject_WeightedIso
import Definitions.Def_RequestProject_ProperTree
import Theorems.Thm_ChromaticReconstruction_skelWeight_eq_leafCount

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V] {T : SimpleGraph V}
namespace ChromaticReconstruction
theorem _root_.solution (h : MultiplicityIsolated T) :
    MIso (skeleton T) (fun c => leafCount T c + 1) := by
  intro u v huv hw
  apply h u v huv
  rw [skelWeight_eq_leafCount, skelWeight_eq_leafCount]
  exact hw
end ChromaticReconstruction
