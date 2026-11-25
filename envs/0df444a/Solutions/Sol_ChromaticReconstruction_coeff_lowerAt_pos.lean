-- Prove2me | solution 1 for ChromaticReconstruction.coeff_lowerAt_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:06.250635+00:00
-- url     : https://prove2.me/submissions/ed92dea2-cd75-4fa8-9372-683e8dd1c2d9

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
theorem _root_.solution {W : Multiset ℕ} {a : ℕ} (ha : a ∈ bigWeights W) :
    (((a - 1) * W.count a : ℕ) : ℚ) ≠ 0 := by
  simp only [bigWeights, mem_filter, Multiset.mem_toFinset] at ha
  have : 0 < W.count a := Multiset.count_pos.2 ha.1
  have : 0 < (a - 1) * W.count a := Nat.mul_pos (by omega) this
  exact_mod_cast this.ne'
end ChromaticReconstruction
