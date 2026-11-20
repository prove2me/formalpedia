-- Prove2me | solution 1 for DeletionCode.BlockAdjunction.blockOf_insert_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:24:04.278876+00:00
-- url     : https://prove2.me/submissions/eef10dc5-5584-454f-b70c-a6404db3b7e4

import Definitions.Def_DeletionCode_BlockPartition
import Definitions.Def_DeletionCode_CatalogueVertexBound
import Definitions.Def_DeletionCode_BlockAdjunction
import Theorems.Thm_DeletionCode_BlockAdjunction_connectedIn_mono
import Theorems.Thm_DeletionCode_BlockPartition_incident_iff_rule
import Theorems.Thm_DeletionCode_BlockPartition_mem_attachedBlocks
import Theorems.Thm_DeletionCode_BlockPartition_mem_blockOf
import Theorems.Thm_DeletionCode_BlockPartition_mem_blocks
import Theorems.Thm_DeletionCode_ConnectedBlocks_RuleAdjacent_symm
attribute [local simp] DeletionCode.BlockPartition.mem_attachedBlocks
attribute [local simp] DeletionCode.BlockPartition.mem_blockOf
attribute [local simp] DeletionCode.BlockPartition.mem_blocks


section
namespace DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition
private theorem adjacent_mem_attached_union {k : ℕ} (U : RuleSet k)
    (w b : Gram (windowLength k) → ℤ) (hb : b ∈ U) (hwb : RuleAdjacent w b) :
    b ∈ (attachedBlocks U w).biUnion id := by
  classical
  have hbblock : b ∈ blockOf U b :=
    (mem_blockOf U b b).mpr ⟨hb, Relation.EqvGen.refl _⟩
  obtain ⟨v, hvw, hvb⟩ := hwb
  have hvblock : Incident (blockOf U b) v :=
    ComponentBounds.incident_mono (Finset.singleton_subset_iff.mpr hbblock) hvb
  have hblock : blockOf U b ∈ attachedBlocks U w :=
    (mem_attachedBlocks U (blockOf U b) w).mpr
      ⟨(mem_blocks U (blockOf U b)).mpr ⟨b, hb, rfl⟩, v, hvblock, hvw⟩
  exact Finset.mem_biUnion.mpr ⟨blockOf U b, hblock, hbblock⟩
private theorem attached_union_closed {k : ℕ} (U : RuleSet k)
    (w a b : Gram (windowLength k) → ℤ)
    (ha : a ∈ (attachedBlocks U w).biUnion id) (hb : b ∈ U)
    (hab : RuleAdjacent a b) : b ∈ (attachedBlocks U w).biUnion id := by
  classical
  obtain ⟨B, hB, haB⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨d, hd, hBvalue⟩ := (mem_blocks U B).mp ((mem_attachedBlocks U B w).mp hB).1
  have had : a ∈ blockOf U d := by simpa only [id_eq, hBvalue] using haB
  obtain ⟨haU, hda⟩ := (mem_blockOf U d a).mp had
  have hdb : ConnectedIn U d b := Relation.EqvGen.trans _ _ _ hda
    (Relation.EqvGen.rel _ _ ⟨haU, hb, hab⟩)
  have hbB : b ∈ B := by
    rw [← hBvalue]
    exact (mem_blockOf U d b).mpr ⟨hb, hdb⟩
  exact Finset.mem_biUnion.mpr ⟨B, hB, hbB⟩
end DeletionCode.BlockAdjunction
end

set_option autoImplicit true
open DeletionCode DeletionCode.BlockAdjunction
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition
namespace DeletionCode.BlockAdjunction
theorem _root_.solution {k : ℕ} (U : RuleSet k)
    (w : Gram (windowLength k) → ℤ) :
    blockOf (insert w U) w = insert w ((attachedBlocks U w).biUnion id) := by
  classical
  let M := insert w ((attachedBlocks U w).biUnion id)
  have hstep (a b : Gram (windowLength k) → ℤ)
      (ha : a ∈ insert w U) (hb : b ∈ insert w U) (hab : RuleAdjacent a b) :
      a ∈ M → b ∈ M := by
    intro haM
    by_cases hbw : b = w
    · subst b
      exact Finset.mem_insert_self _ _
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hbw
      rcases Finset.mem_insert.mp haM with haw | haUnion
      · subst a
        exact Finset.mem_insert_of_mem (adjacent_mem_attached_union U w b hbU hab)
      · exact Finset.mem_insert_of_mem (attached_union_closed U w a b haUnion hbU hab)
  have hpreserve (a b : Gram (windowLength k) → ℤ)
      (h : ConnectedIn (insert w U) a b) : a ∈ M ↔ b ∈ M := by
    induction h with
    | rel a b hab =>
      exact ⟨hstep a b hab.1 hab.2.1 hab.2.2,
        hstep b a hab.2.1 hab.1 hab.2.2.symm⟩
    | refl a => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  ext b
  constructor
  · intro hb
    have hpath := ((mem_blockOf (insert w U) w b).mp hb).2
    exact (hpreserve w b hpath).mp (Finset.mem_insert_self _ _)
  · intro hb
    rcases Finset.mem_insert.mp hb with hbw | hbUnion
    · subst b
      exact (mem_blockOf (insert w U) w w).mpr
        ⟨Finset.mem_insert_self _ _, Relation.EqvGen.refl _⟩
    · obtain ⟨B, hB, hbB⟩ := Finset.mem_biUnion.mp hbUnion
      obtain ⟨hBold, v, hvB, hvw⟩ := (mem_attachedBlocks U B w).mp hB
      obtain ⟨a, haB, hva⟩ := (incident_iff_rule B v).mp hvB
      obtain ⟨d, hd, hBvalue⟩ := (mem_blocks U B).mp hBold
      have haBlock : a ∈ blockOf U d := by simpa only [id_eq, hBvalue] using haB
      have hbBlock : b ∈ blockOf U d := by simpa only [id_eq, hBvalue] using hbB
      obtain ⟨haU, hda⟩ := (mem_blockOf U d a).mp haBlock
      obtain ⟨hbU, hdb⟩ := (mem_blockOf U d b).mp hbBlock
      have habOld : ConnectedIn U a b :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hda) hdb
      have habNew : ConnectedIn (insert w U) a b :=
        connectedIn_mono (Finset.subset_insert _ _) habOld
      have hwa : ConnectedIn (insert w U) w a := Relation.EqvGen.rel _ _
        ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem haU, v, hvw, hva⟩
      exact (mem_blockOf (insert w U) w b).mpr
        ⟨Finset.mem_insert_of_mem hbU, Relation.EqvGen.trans _ _ _ hwa habNew⟩
end DeletionCode.BlockAdjunction
