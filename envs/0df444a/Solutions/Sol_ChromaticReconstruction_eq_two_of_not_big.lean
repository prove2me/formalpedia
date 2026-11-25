-- Prove2me | solution 1 for ChromaticReconstruction.eq_two_of_not_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:07.933114+00:00
-- url     : https://prove2.me/submissions/0baf678f-c58f-4eac-8913-d4454cbddb5b

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {x : ℕ} (hx : x ∈ W)
    (hnb : x ∉ bigWeights W) : x = 2 := by
  simp only [bigWeights, mem_filter, Multiset.mem_toFinset, not_and, not_le] at hnb
  have := hW x hx
  have := hnb hx
  omega
end ChromaticReconstruction
