-- Prove2me | solution 1 for ChromaticReconstruction.lowerAt_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:30:50.25704+00:00
-- url     : https://prove2.me/submissions/976f8866-f237-45cb-8c37-c9e9383ebd71

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_lowerAt_add
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} {a b : ℕ} (ha : a ∈ W) (hb : b ∈ W) (ha1 : 1 ≤ a)
    (hb1 : 1 ≤ b) (h : lowerAt W a = lowerAt W b) : a = b := by
  have e1 := lowerAt_add ha
  have e2 := lowerAt_add hb
  have : W + {a - 1} + {b} = W + {b - 1} + {a} := by
    rw [← e1, ← e2, h, add_assoc, add_assoc, Multiset.add_comm {b}]
  rw [add_assoc, add_assoc] at this
  have h2 := add_left_cancel this
  have hm : a - 1 ∈ ({b - 1} + {a} : Multiset ℕ) := by
    rw [← h2]; simp
  simp only [Multiset.singleton_add, Multiset.mem_cons, Multiset.mem_singleton] at hm
  omega
end ChromaticReconstruction
