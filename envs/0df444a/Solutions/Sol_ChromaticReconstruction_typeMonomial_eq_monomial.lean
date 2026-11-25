-- Prove2me | solution 1 for ChromaticReconstruction.typeMonomial_eq_monomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:19.97279+00:00
-- url     : https://prove2.me/submissions/101a4bdc-f608-4ec1-8f7c-b3dfdb65c473

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_prod_X_multiset

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) :
    typeMonomial A = monomial (Multiset.toFinsupp (compType A)) 1 := by
  rw [typeMonomial, ← prod_X_multiset, compType, Multiset.map_map]
  rfl
end ChromaticReconstruction
