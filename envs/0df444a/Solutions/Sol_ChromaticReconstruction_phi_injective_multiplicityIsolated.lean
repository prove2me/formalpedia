-- Prove2me | solution 1 for ChromaticReconstruction.phi_injective_multiplicityIsolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:01.209332+00:00
-- url     : https://prove2.me/submissions/1c1b63fb-394f-44ae-94c7-92a2f10f1237

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Theorem2
import Definitions.Def_RequestProject_ProperTree
import Definitions.Def_RequestProject_CountingLimit
import Definitions.Def_RequestProject_TauBound
import Definitions.Def_RequestProject_MainTheorems
import Theorems.Thm_ChromaticReconstruction_card_skel_add_leafCount
import Theorems.Thm_ChromaticReconstruction_exists_weighted_iso
import Theorems.Thm_ChromaticReconstruction_leafCount_pos
import Theorems.Thm_ChromaticReconstruction_leafExt_recovery
import Theorems.Thm_ChromaticReconstruction_miso_of_multiplicityIsolated
import Theorems.Thm_ChromaticReconstruction_phi_iso
import Theorems.Thm_ChromaticReconstruction_skeleton_isTree


set_option autoImplicit true
open MvPolynomial Finset Filter Topology
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {V W : Type*} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (T' : SimpleGraph W) (hT : IsProperTree T) (hT' : IsProperTree T')
    (hiso : MultiplicityIsolated T) (h : phi T = phi T') : Nonempty (T ≃g T') := by
  let e := properIso hT
  let e' := properIso hT'
  have h' : phi (leafExt (skeleton T) (leafCount T)) =
      phi (leafExt (skeleton T') (leafCount T')) := by
    rw [phi_iso e, phi_iso e', h]
  have hn := card_skel_add_leafCount hT
  have hn' := card_skel_add_leafCount hT'
  obtain ⟨-, hW, hE⟩ := leafExt_recovery (skeleton_isTree hT) (skeleton_isTree hT')
    (leafCount_pos hT) (leafCount_pos hT') (by rw [hn]; exact hT.2.1) (by rw [hn']; exact hT'.2.1)
    h'
  obtain ⟨φ, hφ⟩ := exists_weighted_iso (skeleton_isTree hT) (skeleton_isTree hT')
    (w := fun c => leafCount T c + 1) (w' := fun c => leafCount T' c + 1) hW hE
    (miso_of_multiplicityIsolated hiso)
  have hφ' : ∀ c, leafCount T' (φ c) = leafCount T c := fun c => by
    have := hφ c
    omega
  exact ⟨e.symm.trans ((leafExtIso φ hφ').trans e')⟩
end ChromaticReconstruction
