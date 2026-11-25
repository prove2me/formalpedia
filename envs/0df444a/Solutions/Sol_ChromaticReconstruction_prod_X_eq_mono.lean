-- Prove2me | solution 1 for ChromaticReconstruction.prod_X_eq_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:45.988641+00:00
-- url     : https://prove2.me/submissions/d7dd1abb-d0d7-40d9-b328-95a94976ee35

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_prod_X_multiset


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    ∏ j ∈ s, (X (f j) : MvPolynomial ℕ ℚ) = mono (s.val.map f) := by
  unfold mono
  rw [← prod_X_multiset, Multiset.map_map]
  rfl
end ChromaticReconstruction
