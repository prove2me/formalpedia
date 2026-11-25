-- Prove2me | solution 1 for ChromaticReconstruction.singletonFiberCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:01:55.192966+00:00
-- url     : https://prove2.me/submissions/5e162c69-9bdf-4777-83a5-2d55e276ea69

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper
import Theorems.Thm_ChromaticReconstruction_card_rankPartitions_le
import Theorems.Thm_ChromaticReconstruction_truncationClass_le
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (k t : ℕ) :
    singletonFiberCount k t ≤ (k ^ t + 1) ^ ((t + 1) ^ (t + 2)) := by
  unfold singletonFiberCount
  let f : {T : TreeClass k // truncationClass k t ⁻¹' {truncationClass k t T} = {T}} →
      ({μ : Nat.Partition k // k - t ≤ Multiset.card μ.parts} → Fin (k ^ t + 1)) :=
    fun T μ => ⟨truncationClass k t T.1 μ, Nat.lt_succ_of_le (truncationClass_le T.1 μ)⟩
  have hf : Function.Injective f := by
    intro T T' h
    have h' : truncationClass k t T'.1 = truncationClass k t T.1 := by
      funext μ
      have := congrFun h μ
      simp only [f, Fin.mk.injEq] at this
      exact this.symm
    have hmem : T'.1 ∈ truncationClass k t ⁻¹' {truncationClass k t T.1} := h'
    rw [T.2] at hmem
    exact Subtype.ext hmem.symm
  refine (Nat.card_le_card_of_injective f hf).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_le_pow_right (Nat.succ_pos _) (card_rankPartitions_le k t)
end ChromaticReconstruction
