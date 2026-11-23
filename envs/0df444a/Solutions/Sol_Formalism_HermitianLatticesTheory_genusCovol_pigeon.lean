-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_pigeon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:45.589573+00:00
-- url     : https://prove2.me/submissions/92a4b274-f8e9-4497-8143-e7283700b043

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {X Y : Submodule R W}
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) (r : R) {z : W} (hz : z ∈ Y) :
    ∃ m k : ℕ, 0 < k ∧ r ^ m • z - r ^ (m + k) • z ∈ X := by
  classical
  have : (X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup).FiniteIndex := ⟨hfin⟩
  have : Finite (Y.toAddSubgroup ⧸ X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  let f : ℕ → Y.toAddSubgroup ⧸ X.toAddSubgroup.addSubgroupOf Y.toAddSubgroup :=
    fun n => QuotientAddGroup.mk (⟨r ^ n • z, Y.smul_mem _ hz⟩ : Y.toAddSubgroup)
  obtain ⟨a, b, hab, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, f a = f b → r ^ a • z - r ^ b • z ∈ X := by
    intro a b e
    have := (QuotientAddGroup.eq).mp e
    rw [AddSubgroup.mem_addSubgroupOf] at this
    have h2 : -(r ^ a • z) + r ^ b • z ∈ X := this
    have h3 := X.neg_mem h2
    simpa [sub_eq_add_neg, add_comm] using h3
  rcases lt_or_gt_of_ne hab with h | h
  · refine ⟨a, b - a, Nat.sub_pos_of_lt h, ?_⟩
    rw [Nat.add_sub_cancel' h.le]
    exact key a b hf
  · refine ⟨b, a - b, Nat.sub_pos_of_lt h, ?_⟩
    rw [Nat.add_sub_cancel' h.le]
    exact key b a hf.symm
end Formalism.HermitianLatticesTheory
