-- Prove2me | solution 1 for ChromaticReconstruction.PL_adj_vx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:36:09.888862+00:00
-- url     : https://prove2.me/submissions/87ae7596-178e-4f85-b622-c96e488f78ba

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
import Theorems.Thm_ChromaticReconstruction_vx_val
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.vx_val

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c x y : ℕ} (hx : x ≤ n) (hy : y ≤ n) :
    (PL n c).Adj (vx n x) (vx n y) ↔ (x + 1 = y ∧ y < n) ∨ (y + 1 = x ∧ x < n) ∨
      (x = c ∧ y = n ∧ c < n) ∨ (y = c ∧ x = n ∧ c < n) := by
  show ((vx n x).val + 1 = (vx n y).val ∧ _) ∨ _ ↔ _
  simp only [vx_val, min_eq_left hx, min_eq_left hy]
end ChromaticReconstruction
