-- Prove2me | solution 1 for ChromaticReconstruction.isHomogeneous_killP1_prod_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:48:08.722361+00:00
-- url     : https://prove2.me/submissions/ed522f47-2075-4837-b647-465f81fe1810

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
import Theorems.Thm_ChromaticReconstruction_killP1_X
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {ι : Type*} (P : Finset ι) (f : ι → ℕ) :
    (killP1 (∏ C ∈ P, (X (f C) : MvPolynomial ℕ ℚ))).IsHomogeneous P.card := by
  rw [map_prod]
  have := IsHomogeneous.prod P (fun C => killP1 (X (f C))) (fun _ => 1) (fun C _ => by
    show (killP1 (X (f C))).IsHomogeneous 1
    rw [killP1_X]
    split_ifs
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_X _ _)
  simpa using this
end ChromaticReconstruction
