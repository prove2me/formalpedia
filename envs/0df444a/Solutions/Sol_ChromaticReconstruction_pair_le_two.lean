-- Prove2me | solution 1 for ChromaticReconstruction.pair_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:11.776012+00:00
-- url     : https://prove2.me/submissions/2641bd7a-45f8-4c7d-ac6d-22678352a5a5

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {a b : ℕ} (hab : {a, b} ≤ W) :
    2 ≤ a ∧ 2 ≤ b :=
  ⟨hW a (Multiset.mem_of_le hab (by simp)), hW b (Multiset.mem_of_le hab (by simp))⟩
end ChromaticReconstruction
