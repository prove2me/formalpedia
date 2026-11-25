-- Prove2me | solution 1 for ChromaticReconstruction.eq_replicate_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:09.030205+00:00
-- url     : https://prove2.me/submissions/f7f990f6-237a-4d43-80e9-03df96bedd1e

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_eq_two_of_not_big
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) (hb : bigWeights W = ∅) :
    W = Multiset.replicate (Multiset.card W) 2 := by
  rw [Multiset.eq_replicate]
  exact ⟨rfl, fun x hx => eq_two_of_not_big hW hx (by simp [hb])⟩
end ChromaticReconstruction
