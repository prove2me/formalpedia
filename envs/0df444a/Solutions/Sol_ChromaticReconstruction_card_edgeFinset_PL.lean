-- Prove2me | solution 1 for ChromaticReconstruction.card_edgeFinset_PL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:16:36.345899+00:00
-- url     : https://prove2.me/submissions/51385a3d-ee8e-413e-b2bf-7a7326ff4da9

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
import Theorems.Thm_ChromaticReconstruction_vx_val
import Theorems.Thm_ChromaticReconstruction_pe_inj
import Theorems.Thm_ChromaticReconstruction_pe_ne_lf
import Theorems.Thm_ChromaticReconstruction_edgeFinset_PL
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.vx_val

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c : ℕ} (hc : c < n) : (PL n c).edgeFinset.card = n := by
  rw [edgeFinset_PL hc, card_insert_of_notMem, card_image_of_injOn]
  · simp; omega
  · intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact (pe_inj (by omega) (by omega)).1 h
  · rw [mem_image]
    rintro ⟨i, hi, h⟩
    rw [mem_range] at hi
    exact pe_ne_lf (by omega) hc.le h
end ChromaticReconstruction
