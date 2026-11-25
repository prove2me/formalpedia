-- Prove2me | solution 1 for ChromaticReconstruction.skelWeight_eq_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:02:42.731154+00:00
-- url     : https://prove2.me/submissions/6e70b311-48b3-49d2-a52f-da849c199d94

import Definitions.Def_RequestProject_WeightedIso
import Definitions.Def_RequestProject_ProperTree

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V] {T : SimpleGraph V}
namespace ChromaticReconstruction
theorem _root_.solution (c : SkelVert T) : skelWeight T c = leafCount T c + 1 := by
  unfold skelWeight leafCount leafNbrs
  omega
end ChromaticReconstruction
