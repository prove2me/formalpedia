-- Prove2me | solution 1 for DeletionCode.FiniteRelationBlocks.selected_block_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:25:58.550988+00:00
-- url     : https://prove2.me/submissions/1df3363c-c918-4d8e-bf1d-6046bbda4e3b

import Definitions.Def_DeletionCode_RelationBlockSupport
import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_RelationBlockSavings
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Theorems.Thm_DeletionCode_FiniteRelationBlocks_mem_selectedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
import Theorems.Thm_DeletionCode_RelationBlockSupport_block_restriction_nonzero
import Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber
attribute [local simp] DeletionCode.SupportInclusion.supportComponentMap_mk


attribute [local simp] DeletionCode.FiniteRelationBlocks.mem_selectedBlocks
section
namespace DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators
private theorem subtype_connected {k : ℕ} (G : RuleSet k) {u v : G}
    (h : GeneratingBlocks.Connected (fun z : G => z.val) u v) :
    ConnectedIn G u.val v.val := by
  induction h with
  | rel u v huv => exact Relation.EqvGen.rel _ _ ⟨u.property, v.property, huv⟩
  | refl u => exact Relation.EqvGen.refl _
  | symm u v huv ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v z huv hvz ihuv ihvz => exact Relation.EqvGen.trans _ _ _ ihuv ihvz
private theorem indexed_relation {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    RelationSupport.Relation (fun u : G => u.val) w
      (fun u : G => if u.val ∈ I then a u.val else 0) := by
  classical
  intro g
  rw [hrel g]
  symm
  calc
    (∑ u : G, (if u.val ∈ I then a u.val else 0) * (u.val g : ℚ)) =
        ∑ u ∈ G, (if u ∈ I then a u else 0) * (u g : ℚ) := by
      apply Finset.sum_bij (fun (u : G) _ => u.val)
      · intro u _
        exact u.property
      · intro u _ v _ huv
        exact Subtype.ext huv
      · intro u hu
        exact ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩
      · intro u _
        rfl
    _ = ∑ u ∈ I, (if u ∈ I then a u else 0) * (u g : ℚ) := by
      symm
      apply Finset.sum_subset hIG
      intro u _ hu
      simp [hu]
    _ = ∑ u ∈ I, a u * (u g : ℚ) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [if_pos hu]
end DeletionCode.FiniteRelationBlocks
end

set_option autoImplicit true
open DeletionCode DeletionCode.FiniteRelationBlocks
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph BlockPartition
open scoped BigOperators
namespace DeletionCode.FiniteRelationBlocks
theorem _root_.solution {k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ)
    (a : (Gram (windowLength k) → ℤ) → ℚ)
    (hind : LinearIndependent ℚ (fun (u : G) g => (u.val g : ℚ)))
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (B : RuleSet k) (hB : B ∈ selectedBlocks G I) :
    ∃ g u, u ∈ B ∧ u g ≠ 0 ∧ w g ≠ 0 := by
  classical
  obtain ⟨hBblock, hBI⟩ := (mem_selectedBlocks G I B).mp hB
  let T : Finset G := Finset.univ.filter (fun u => u.val ∈ B)
  let coeff : G → ℚ := fun u => if u.val ∈ I then a u.val else 0
  have hmem (u : G) : u ∈ T ↔ u.val ∈ B := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
  have hactive : ∃ u ∈ T, coeff u ≠ 0 := by
    obtain ⟨u, hu⟩ := hBI
    obtain ⟨huB, huI⟩ := Finset.mem_inter.mp hu
    let uG : G := ⟨u, hIG huI⟩
    refine ⟨uG, (hmem uG).mpr huB, ?_⟩
    simpa only [coeff, uG, if_pos huI] using ha u huI
  have hclosed : GeneratingBlocks.BlockClosed (fun u : G => u.val) (↑T : Set G) := by
    intro u hu v huv
    obtain ⟨r, _, hr⟩ := (mem_blocks G B).mp hBblock
    have huB : u.val ∈ blockOf G r := by rw [hr]; exact (hmem u).mp hu
    have hru := ((mem_blockOf G r u.val).mp huB).2
    apply (hmem v).mpr
    rw [← hr]
    exact (mem_blockOf G r v.val).mpr ⟨v.property,
      Relation.EqvGen.trans _ _ _ hru (subtype_connected G huv)⟩
  obtain ⟨g, hw, u, hu, hug⟩ := RelationBlockSupport.block_restriction_nonzero
    (fun u : G => u.val) w coeff hind (indexed_relation G I hIG w a hrel)
    T hactive hclosed
  exact ⟨g, u.val, (hmem u).mp hu, hug, hw⟩
end DeletionCode.FiniteRelationBlocks
