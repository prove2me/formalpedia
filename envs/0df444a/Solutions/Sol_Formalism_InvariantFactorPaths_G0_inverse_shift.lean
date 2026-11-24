-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G0.inverse_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:44:11.119693+00:00
-- url     : https://prove2.me/submissions/74ae2c96-2617-40ef-b5af-cfb30f817aaf

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G0_invariant_factors_submodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
open Formalism.G0
namespace Formalism.InvariantFactorPaths.G0
theorem _root_.solution : InvShift := by
  intro R X _ _ _ _ _ π A B NA NB g E e hBA hNA hNANB hNBB h
  classical
  obtain ⟨C, hC, hCg, hCx⟩ :=
    invariant_factors_submodule π A (B ⊔ NA) NA g E le_sup_right (sup_le hBA hNA) h
  refine ⟨C.image (fun c => π ^ e • c), ?_, Finset.card_image_le.trans hCg, ?_⟩
  · intro z hz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
    obtain ⟨b, hb, k, hk, hbk⟩ := Submodule.mem_sup.mp (hC hc)
    rw [← hbk, smul_add]
    exact B.add_mem (B.smul_mem _ hb)
      (hNBB (hNANB (Submodule.smul_mem_pointwise_smul k _ _ hk)))
  · intro x hx
    obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp (hCx x (le_sup_left (a := B) hx))
    rw [pow_add, mul_comm, mul_smul, ← hpz, smul_add]
    have hz' : π ^ e • z ∈ Submodule.span R (↑(C.image (fun c => π ^ e • c)) : Set X) := by
      refine Submodule.span_induction (p := fun z _ => π ^ e • z ∈
        Submodule.span R (↑(C.image (fun c => π ^ e • c)) : Set X)) ?_ ?_ ?_ ?_ hz
      · intro c hc
        exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hc))
      · simp
      · intro a b _ _ ha hb
        rw [smul_add]
        exact add_mem ha hb
      · intro r a _ ha
        rw [smul_comm]
        exact Submodule.smul_mem _ _ ha
    exact Submodule.mem_sup.mpr ⟨_, hNANB (Submodule.smul_mem_pointwise_smul _ _ _ hp), _, hz', rfl⟩
end Formalism.InvariantFactorPaths.G0
