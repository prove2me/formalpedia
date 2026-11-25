-- Prove2me | solution 1 for ChromaticReconstruction.masterTerm_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:55:21.911798+00:00
-- url     : https://prove2.me/submissions/5cef37ad-7cdc-40ea-b4a0-dc678a9f5280

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_isHomogeneous_killP1_prod_X

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
variable (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (F : Finset (Sym2 K)) :
    (masterTerm m F).IsHomogeneous (compSets (F : Set (Sym2 K))).card := by
  unfold masterTerm
  apply IsHomogeneous.sum
  intro i _
  have := (isHomogeneous_C ℕ ((m i : ℕ) : ℚ)).mul (isHomogeneous_killP1_prod_X
    (compSets (F : Set (Sym2 K))) (fun C => (∑ j ∈ C, (m j + 1)) - if i ∈ C then 1 else 0))
  rw [zero_add, map_natCast] at this
  exact this
end ChromaticReconstruction
