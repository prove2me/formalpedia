-- Prove2me | solution 1 for ChromaticReconstruction.exists_weighted_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:27.285566+00:00
-- url     : https://prove2.me/submissions/0ac4aa23-a17c-4ada-a24e-aef4abecc194

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
import Theorems.Thm_ChromaticReconstruction_card_wts
import Theorems.Thm_ChromaticReconstruction_exists_equiv_of_wts_eq
import Theorems.Thm_ChromaticReconstruction_adj_iff_ne_of_card_le_two
import Theorems.Thm_ChromaticReconstruction_card_key_fiber
import Theorems.Thm_ChromaticReconstruction_miso_transfer
import Theorems.Thm_ChromaticReconstruction_adj_map
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
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K K' : Type*} [Fintype K] [Fintype K'] {S : SimpleGraph K} {S' : SimpleGraph K'}
  {w : K → ℕ} {w' : K' → ℕ}
namespace ChromaticReconstruction
theorem _root_.solution (hS : S.IsTree) (hS' : S'.IsTree) (hW : wts w = wts w')
    (hE : edgeTypes S w = edgeTypes S' w') (hMI : MIso S w) :
    ∃ φ : S ≃g S', ∀ x, w' (φ x) = w x := by
  have hcard : Fintype.card K = Fintype.card K' := by rw [← card_wts w, hW, card_wts]
  by_cases hk : 3 ≤ Fintype.card K
  · have hk' : 3 ≤ Fintype.card K' := hcard ▸ hk
    have hMI' := miso_transfer hS'.1 (by omega) hW hE hMI
    have hfib : ∀ κ : ℕ × Multiset ℕ, Fintype.card {x // keyOf S w x = κ} =
        Fintype.card {x' // keyOf S' w' x' = κ} := by
      rintro ⟨a, M⟩
      rw [Fintype.card_subtype, Fintype.card_subtype, card_key_fiber hS.1 hk hMI,
        card_key_fiber hS'.1 hk' hMI', hW, hE]
    let φ : K ≃ K' := Equiv.ofFiberEquiv fun κ => Fintype.equivOfCardEq (hfib κ)
    have hkey : ∀ x, keyOf S' w' (φ x) = keyOf S w x := Equiv.ofFiberEquiv_map _
    have hkey' : ∀ x', keyOf S w (φ.symm x') = keyOf S' w' x' := fun x' => by
      rw [← hkey, φ.apply_symm_apply]
    refine ⟨⟨φ, fun {a b} => ⟨fun h => ?_, fun h => adj_map hS.1 hk hMI hW hE φ hkey h⟩⟩,
      fun x => congrArg Prod.fst (hkey x)⟩
    have := adj_map hS'.1 hk' hMI' hW.symm hE.symm φ.symm hkey' h
    simpa using this
  · obtain ⟨e, he⟩ := exists_equiv_of_wts_eq hW
    refine ⟨⟨e, fun {a b} => ?_⟩, he⟩
    rw [adj_iff_ne_of_card_le_two hS'.1 (by omega), adj_iff_ne_of_card_le_two hS.1 (by omega)]
    exact e.injective.ne_iff
end ChromaticReconstruction
