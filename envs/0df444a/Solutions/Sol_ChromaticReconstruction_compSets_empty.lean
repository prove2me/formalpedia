-- Prove2me | solution 1 for ChromaticReconstruction.compSets_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:00:03.281465+00:00
-- url     : https://prove2.me/submissions/a7c07ea6-9df8-4602-8246-c45d9cc872f9

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_compOf_empty
import Theorems.Thm_ChromaticReconstruction_compSets_eq_image_compOf


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution :
    compSets (∅ : Set (Sym2 V)) = univ.image fun v : V => ({v} : Finset V) := by
  rw [compSets_eq_image_compOf]
  congr 1
  funext v
  exact compOf_empty v
end ChromaticReconstruction
