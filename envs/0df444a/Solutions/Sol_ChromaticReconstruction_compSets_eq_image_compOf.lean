-- Prove2me | solution 1 for ChromaticReconstruction.compSets_eq_image_compOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:28.684211+00:00
-- url     : https://prove2.me/submissions/42ffb774-ffef-4a50-bdcd-426f60173295

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) : compSets A = univ.image (compOf A) := rfl
end ChromaticReconstruction
