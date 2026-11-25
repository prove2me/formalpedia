-- Prove2me | solution 1 for ChromaticReconstruction.psum_partner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:18.601878+00:00
-- url     : https://prove2.me/submissions/92d78df0-1e24-4a4e-843d-c3e9e74ec3dc

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_RecoverP
import Theorems.Thm_ChromaticReconstruction_lowerAt_add
import Theorems.Thm_ChromaticReconstruction_psum_add
import Theorems.Thm_ChromaticReconstruction_psum_singleton
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W W' : Multiset ℕ} {a a' : ℕ} (ha : a ∈ W) (ha' : a' ∈ W') (h1 : 1 ≤ a)
    (h1' : 1 ≤ a') (h : lowerAt W a = lowerAt W' a') (j : ℕ) :
    psum j W - psum j W' = ((a' : ℤ) - 1) ^ j + (a : ℤ) ^ j - ((a : ℤ) - 1) ^ j - (a' : ℤ) ^ j := by
  have e : W + {a - 1} + {a'} = W' + {a' - 1} + {a} := by
    rw [← lowerAt_add ha, ← lowerAt_add ha', h, add_assoc, add_assoc, Multiset.add_comm {a}]
  have := congrArg (psum j) e
  simp only [psum_add, psum_singleton] at this
  push_cast [Nat.cast_sub h1, Nat.cast_sub h1'] at this
  linarith
end ChromaticReconstruction
