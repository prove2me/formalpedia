-- Prove2me | solution 1 for Freiman.section14_s0007_coverage0000_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T08:43:26.090983+00:00
-- url     : https://prove2.me/submissions/37afe86f-287f-4e0b-a44c-b7c29b750d67

import Definitions.Def_Freiman_section14Data
import Mathlib.Tactic.IntervalCases

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace M7Section14Sep18.RecordMembership
theorem part0 {r : Section14Record} (h : r ∈ section14DataRecords1Part1) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (([] : List Section14Record)) ++ section14DataRecords1Part1 ++ (section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part1 {r : Section14Record} (h : r ∈ section14DataRecords1Part2) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1) ++ section14DataRecords1Part2 ++ (section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part2 {r : Section14Record} (h : r ∈ section14DataRecords1Part3) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2) ++ section14DataRecords1Part3 ++ (section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part3 {r : Section14Record} (h : r ∈ section14DataRecords1Part4) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3) ++ section14DataRecords1Part4 ++ (section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part4 {r : Section14Record} (h : r ∈ section14DataRecords2Part1) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4) ++ section14DataRecords2Part1 ++ (section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part5 {r : Section14Record} (h : r ∈ section14DataRecords2Part2) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1) ++ section14DataRecords2Part2 ++ (section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part6 {r : Section14Record} (h : r ∈ section14DataRecords2Part3) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2) ++ section14DataRecords2Part3 ++ (section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part7 {r : Section14Record} (h : r ∈ section14DataRecords2Part4) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3) ++ section14DataRecords2Part4 ++ (section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part8 {r : Section14Record} (h : r ∈ section14DataRecords3Part1) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4) ++ section14DataRecords3Part1 ++ (section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part9 {r : Section14Record} (h : r ∈ section14DataRecords3Part2) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1) ++ section14DataRecords3Part2 ++ (section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part10 {r : Section14Record} (h : r ∈ section14DataRecords3Part3) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2) ++ section14DataRecords3Part3 ++ (section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part11 {r : Section14Record} (h : r ∈ section14DataRecords3Part4) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3) ++ section14DataRecords3Part4 ++ (section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part12 {r : Section14Record} (h : r ∈ section14DataRecords4Part1) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4) ++ section14DataRecords4Part1 ++ (section14DataRecords4Part2 ++ section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part13 {r : Section14Record} (h : r ∈ section14DataRecords4Part2) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1) ++ section14DataRecords4Part2 ++ (section14DataRecords4Part3 ++ section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part14 {r : Section14Record} (h : r ∈ section14DataRecords4Part3) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2) ++ section14DataRecords4Part3 ++ (section14DataRecords4Part4) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem part15 {r : Section14Record} (h : r ∈ section14DataRecords4Part4) : r ∈ section14Catalog.records := by
  have he : section14Catalog.records = (section14DataRecords1Part1 ++ section14DataRecords1Part2 ++ section14DataRecords1Part3 ++ section14DataRecords1Part4 ++ section14DataRecords2Part1 ++ section14DataRecords2Part2 ++ section14DataRecords2Part3 ++ section14DataRecords2Part4 ++ section14DataRecords3Part1 ++ section14DataRecords3Part2 ++ section14DataRecords3Part3 ++ section14DataRecords3Part4 ++ section14DataRecords4Part1 ++ section14DataRecords4Part2 ++ section14DataRecords4Part3) ++ section14DataRecords4Part4 ++ (([] : List Section14Record)) := by
    simp only [section14Catalog, section14DataRecords1, section14DataRecords2, section14DataRecords3, section14DataRecords4, List.append_assoc, List.nil_append, List.append_nil]
  rw [he]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h)))
theorem recorded (r : Section14Record) (hr : r ∈ section14Catalog.records) (si parent : ℕ) (hs : si ∈ r.states) (hp : parent ∈ r.parents) : section14Recorded section14Catalog si parent r.goal r.branch := ⟨r,hr,hs,hp,rfl,rfl⟩
end M7Section14Sep18.RecordMembership

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_7_0_p0_16
private theorem rec0 (si parent : ℕ) (hs : si ∈ ([1, 2, 3, 5, 6, 7, 9, 10, 13, 14, 15] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],1⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[0]? = some (⟨1,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],1⟩) from rfl))
private theorem rec17 (si parent : ℕ) (hs : si ∈ ([1, 3, 5, 7, 9, 11, 13, 15] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[1,3,5,7,9,11,13,15],[0],1⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[17]? = some (⟨1,(-1),[1,3,5,7,9,11,13,15],[0],1⟩) from rfl))
private theorem rec27 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[3,4,7,8,12,15,16],[5],5⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[27]? = some (⟨1,(-1),[3,4,7,8,12,15,16],[5],5⟩) from rfl))
private theorem rec28 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([2, 3] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[3,7,15],[2,3],1⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[28]? = some (⟨1,(-1),[3,7,15],[2,3],1⟩) from rfl))
private theorem rec29 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([4, 6, 7] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[3,7,15],[4,6,7],5⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[29]? = some (⟨1,(-1),[3,7,15],[4,6,7],5⟩) from rfl))
private theorem rec30 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[3,7,15],[8],7⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[30]? = some (⟨1,(-1),[3,7,15],[8],7⟩) from rfl))
private theorem rec31 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[3,7,15],[9],9⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[31]? = some (⟨1,(-1),[3,7,15],[9],9⟩) from rfl))
private theorem rec32 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[3,7,15],[11],54⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[32]? = some (⟨1,(-1),[3,7,15],[11],54⟩) from rfl))
private theorem rec33 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([12, 13, 14, 15] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[3,7,15],[12,13,14,15],56⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[33]? = some (⟨1,(-1),[3,7,15],[12,13,14,15],56⟩) from rfl))
private theorem rec111 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(0),[3,4,7,8,15,16],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[111]? = some (⟨5,(0),[3,4,7,8,15,16],[10],10⟩) from rfl))
private theorem rec113 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(1),[3,4,7,8,15,16],[10],11⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[113]? = some (⟨5,(1),[3,4,7,8,15,16],[10],11⟩) from rfl))
private theorem rec115 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(2),[3,4,7,15,16],[10],12⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[115]? = some (⟨5,(2),[3,4,7,15,16],[10],12⟩) from rfl))
private theorem rec119 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(3),[3,4,7,15,16],[10],13⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[119]? = some (⟨5,(3),[3,4,7,15,16],[10],13⟩) from rfl))
private theorem rec123 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(4),[3,4,7,15,16],[10],14⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[123]? = some (⟨5,(4),[3,4,7,15,16],[10],14⟩) from rfl))
private theorem rec127 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(5),[3,4,7,8,15,16],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[127]? = some (⟨5,(5),[3,4,7,8,15,16],[10],10⟩) from rfl))
private theorem rec129 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(6),[3,4,7,8,15,16],[10],11⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[129]? = some (⟨5,(6),[3,4,7,8,15,16],[10],11⟩) from rfl))
private theorem rec131 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(7),[3,4,7,8,15,16],[10],15⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[131]? = some (⟨5,(7),[3,4,7,8,15,16],[10],15⟩) from rfl))
private theorem rec133 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(8),[3,4,7,8,15,16],[10],16⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[133]? = some (⟨5,(8),[3,4,7,8,15,16],[10],16⟩) from rfl))
private theorem rec135 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(9),[3,4,7,8,15,16],[10],17⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[135]? = some (⟨5,(9),[3,4,7,8,15,16],[10],17⟩) from rfl))
private theorem rec137 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(10),[3,4,7,8,15,16],[10],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[137]? = some (⟨5,(10),[3,4,7,8,15,16],[10],18⟩) from rfl))
private theorem rec139 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(11),[3,4,7,8,15,16],[10],19⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[139]? = some (⟨5,(11),[3,4,7,8,15,16],[10],19⟩) from rfl))
private theorem rec141 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(12),[3,4,7,8,15,16],[10],20⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[141]? = some (⟨5,(12),[3,4,7,8,15,16],[10],20⟩) from rfl))
private theorem rec143 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(13),[3,4,7,8,15,16],[10],20⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[143]? = some (⟨5,(13),[3,4,7,8,15,16],[10],20⟩) from rfl))
private theorem rec145 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(14),[3,4,7,8,15,16],[10],17⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[145]? = some (⟨5,(14),[3,4,7,8,15,16],[10],17⟩) from rfl))
private theorem rec147 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(15),[3,4,7,8,15,16],[10],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[147]? = some (⟨5,(15),[3,4,7,8,15,16],[10],21⟩) from rfl))
private theorem rec149 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(16),[3,4,7,8,15,16],[10],22⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[149]? = some (⟨5,(16),[3,4,7,8,15,16],[10],22⟩) from rfl))
private theorem rec151 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(17),[3,4,7,8,15,16],[10],23⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[151]? = some (⟨5,(17),[3,4,7,8,15,16],[10],23⟩) from rfl))
private theorem rec153 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(18),[3,4,7,8,15,16],[10],23⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[153]? = some (⟨5,(18),[3,4,7,8,15,16],[10],23⟩) from rfl))
private theorem rec155 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(19),[3,4,7,8,15,16],[10],23⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[155]? = some (⟨5,(19),[3,4,7,8,15,16],[10],23⟩) from rfl))
private theorem rec157 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(20),[3,4,7,8,15,16],[10],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[157]? = some (⟨5,(20),[3,4,7,8,15,16],[10],24⟩) from rfl))
private theorem rec159 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(21),[3,4,7,8,15,16],[10],25⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[159]? = some (⟨5,(21),[3,4,7,8,15,16],[10],25⟩) from rfl))
private theorem rec161 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(22),[3,4,7,8,15,16],[10],26⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[161]? = some (⟨5,(22),[3,4,7,8,15,16],[10],26⟩) from rfl))
private theorem rec163 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(23),[3,4,7,8,15,16],[10],26⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[163]? = some (⟨5,(23),[3,4,7,8,15,16],[10],26⟩) from rfl))
private theorem rec165 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(24),[3,4,7,8,15,16],[10],26⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[165]? = some (⟨5,(24),[3,4,7,8,15,16],[10],26⟩) from rfl))
private theorem rec242 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(0),[3,4,7,8],[10],41⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[242]? = some (⟨11,(0),[3,4,7,8],[10],41⟩) from rfl))
private theorem rec244 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(1),[3,4,7,8],[10],41⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[244]? = some (⟨11,(1),[3,4,7,8],[10],41⟩) from rfl))
private theorem rec246 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(2),[3,4,7,8],[10],42⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[246]? = some (⟨11,(2),[3,4,7,8],[10],42⟩) from rfl))
private theorem rec248 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(3),[3,4,7,8],[10],43⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[248]? = some (⟨11,(3),[3,4,7,8],[10],43⟩) from rfl))
private theorem rec250 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(4),[3,4,7,8],[10],44⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[250]? = some (⟨11,(4),[3,4,7,8],[10],44⟩) from rfl))
private theorem rec252 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(5),[3,4,7,8],[10],45⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[252]? = some (⟨11,(5),[3,4,7,8],[10],45⟩) from rfl))
private theorem rec254 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(6),[3,4,7,8],[10],45⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[254]? = some (⟨11,(6),[3,4,7,8],[10],45⟩) from rfl))
private theorem rec256 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(7),[3,4,7,8],[10],42⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[256]? = some (⟨11,(7),[3,4,7,8],[10],42⟩) from rfl))
private theorem rec258 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(8),[3,4,7,8],[10],43⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[258]? = some (⟨11,(8),[3,4,7,8],[10],43⟩) from rfl))
private theorem rec260 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(9),[3,4,7,8],[10],44⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[260]? = some (⟨11,(9),[3,4,7,8],[10],44⟩) from rfl))
private theorem rec262 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(10),[3,4,7,8],[10],41⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[262]? = some (⟨11,(10),[3,4,7,8],[10],41⟩) from rfl))
private theorem rec264 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(11),[3,4,7,8],[10],41⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[264]? = some (⟨11,(11),[3,4,7,8],[10],41⟩) from rfl))
private theorem rec266 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(12),[3,4,7,8],[10],42⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[266]? = some (⟨11,(12),[3,4,7,8],[10],42⟩) from rfl))
private theorem rec268 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(13),[3,4,7,8],[10],43⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[268]? = some (⟨11,(13),[3,4,7,8],[10],43⟩) from rfl))
private theorem rec270 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(14),[3,4,7,8],[10],44⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[270]? = some (⟨11,(14),[3,4,7,8],[10],44⟩) from rfl))
private theorem rec272 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(15),[3,4,7,8],[10],46⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[272]? = some (⟨11,(15),[3,4,7,8],[10],46⟩) from rfl))
private theorem rec274 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(16),[3,4,7,8],[10],46⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[274]? = some (⟨11,(16),[3,4,7,8],[10],46⟩) from rfl))
private theorem rec276 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(17),[3,4,7,8],[10],42⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[276]? = some (⟨11,(17),[3,4,7,8],[10],42⟩) from rfl))
private theorem rec278 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(18),[3,4,7,8],[10],43⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[278]? = some (⟨11,(18),[3,4,7,8],[10],43⟩) from rfl))
private theorem rec280 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(19),[3,4,7,8],[10],44⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[280]? = some (⟨11,(19),[3,4,7,8],[10],44⟩) from rfl))
private theorem rec282 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(20),[3,4,7,8],[10],47⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[282]? = some (⟨11,(20),[3,4,7,8],[10],47⟩) from rfl))
private theorem rec284 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(21),[3,4,7,8],[10],47⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[284]? = some (⟨11,(21),[3,4,7,8],[10],47⟩) from rfl))
private theorem rec286 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(22),[3,4,7,8],[10],47⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[286]? = some (⟨11,(22),[3,4,7,8],[10],47⟩) from rfl))
private theorem rec288 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(23),[3,4,7,8],[10],43⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[288]? = some (⟨11,(23),[3,4,7,8],[10],43⟩) from rfl))
private theorem rec290 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 11 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨11,(24),[3,4,7,8],[10],44⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[290]? = some (⟨11,(24),[3,4,7,8],[10],44⟩) from rfl))
private theorem rec293 (si parent : ℕ) (hs : si ∈ ([7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 14 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨14,(5),[7,15],[10],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[293]? = some (⟨14,(5),[7,15],[10],105⟩) from rfl))
private theorem rec296 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 14 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨14,(7),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[296]? = some (⟨14,(7),[3,7,15],[10],3⟩) from rfl))
private theorem rec300 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 14 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨14,(8),[7],[10],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[300]? = some (⟨14,(8),[7],[10],48⟩) from rfl))
private theorem rec304 (si parent : ℕ) (hs : si ∈ ([7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 14 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨14,(9),[7,15],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[304]? = some (⟨14,(9),[7,15],[10],143⟩) from rfl))
private theorem rec308 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 14 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨14,(15),[7],[10],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[308]? = some (⟨14,(15),[7],[10],48⟩) from rfl))
private theorem rec312 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 14 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨14,(16),[7],[10],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[312]? = some (⟨14,(16),[7],[10],48⟩) from rfl))
private theorem rec314 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 14 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨14,(17),[3,7,15],[10],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[314]? = some (⟨14,(17),[3,7,15],[10],48⟩) from rfl))
private theorem rec317 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 14 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨14,(19),[3,7],[10],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[317]? = some (⟨14,(19),[3,7],[10],48⟩) from rfl))
private theorem rec14675 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(0),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1072]? = some (⟨325,(0),[3,7,15],[10],3⟩) from rfl))
private theorem rec14677 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(1),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1074]? = some (⟨325,(1),[3,7,15],[10],3⟩) from rfl))
private theorem rec14679 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(2),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1076]? = some (⟨325,(2),[3,7,15],[10],3⟩) from rfl))
private theorem rec14681 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(3),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1078]? = some (⟨325,(3),[3,7,15],[10],3⟩) from rfl))
private theorem rec14683 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(4),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1080]? = some (⟨325,(4),[3,7,15],[10],3⟩) from rfl))
private theorem rec14685 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(5),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1082]? = some (⟨325,(5),[3,7,15],[10],3⟩) from rfl))
private theorem rec14687 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(6),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1084]? = some (⟨325,(6),[3,7,15],[10],3⟩) from rfl))
private theorem rec14689 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(7),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1086]? = some (⟨325,(7),[3,7,15],[10],3⟩) from rfl))
private theorem rec14691 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(8),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1088]? = some (⟨325,(8),[3,7,15],[10],3⟩) from rfl))
private theorem rec14693 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 325 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨325,(9),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1090]? = some (⟨325,(9),[3,7,15],[10],3⟩) from rfl))
private theorem rec14695 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(0),[3,7,15],[10],28⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1092]? = some (⟨330,(0),[3,7,15],[10],28⟩) from rfl))
private theorem rec14697 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(1),[3,7,15],[10],30⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1094]? = some (⟨330,(1),[3,7,15],[10],30⟩) from rfl))
private theorem rec14699 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(2),[3,7,15],[10],925⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1096]? = some (⟨330,(2),[3,7,15],[10],925⟩) from rfl))
private theorem rec14701 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(3),[3,7,15],[10],926⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1098]? = some (⟨330,(3),[3,7,15],[10],926⟩) from rfl))
private theorem rec14703 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(4),[3,7,15],[10],927⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1100]? = some (⟨330,(4),[3,7,15],[10],927⟩) from rfl))
private theorem rec14705 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(5),[3,7,15],[10],928⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1102]? = some (⟨330,(5),[3,7,15],[10],928⟩) from rfl))
private theorem rec14707 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(6),[3,7,15],[10],929⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1104]? = some (⟨330,(6),[3,7,15],[10],929⟩) from rfl))
private theorem rec14709 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(7),[3,7,15],[10],929⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1106]? = some (⟨330,(7),[3,7,15],[10],929⟩) from rfl))
private theorem rec14711 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(8),[3,7,15],[10],930⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1108]? = some (⟨330,(8),[3,7,15],[10],930⟩) from rfl))
private theorem rec14713 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 330 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨330,(9),[3,7,15],[10],930⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1110]? = some (⟨330,(9),[3,7,15],[10],930⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 7).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 7)).drop 0).take 16, section14Recorded section14Catalog 7 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 7).plans.drop 0).take 1 = [⟨1,1,[([1],[]),([],[1])],false,[(324,⟨([1],[]),true,([1],[]),false,false,[]⟩),(325,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(326,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(5,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(327,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(328,⟨([],[1]),true,([],[1]),false,false,[]⟩),(329,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(330,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(10,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(11,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(331,⟨([1],[]),true,([],[1]),false,false,[]⟩),(332,⟨([],[1]),true,([1],[]),false,false,[]⟩),(14,⟨([1],[]),true,([],[]),true,false,[]⟩),(333,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 7)).drop 0).take 16 = [⟨2,0,[⟨true,false,12⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨2,1,[⟨true,false,12⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨2,2,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,3,[⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,4,[⟨true,false,16⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,5,[⟨true,false,16⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,6,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨2,7,[⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,8,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,9,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,10,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨2,11,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,12,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,13,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,14,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨2,15,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec17 7 0 (by decide) (by decide)
  · left
    exact rec0 7 1 (by decide) (by decide)
  · left
    exact rec28 7 2 (by decide) (by decide)
  · left
    exact rec28 7 3 (by decide) (by decide)
  · left
    exact rec29 7 4 (by decide) (by decide)
  · left
    exact rec27 7 5 (by decide) (by decide)
  · left
    exact rec29 7 6 (by decide) (by decide)
  · left
    exact rec29 7 7 (by decide) (by decide)
  · left
    exact rec30 7 8 (by decide) (by decide)
  · left
    exact rec31 7 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(324,⟨([1],[]),true,([1],[]),false,false,[]⟩),(325,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(326,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(5,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(327,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(328,⟨([],[1]),true,([],[1]),false,false,[]⟩),(329,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(330,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(10,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(11,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(331,⟨([1],[]),true,([],[1]),false,false,[]⟩),(332,⟨([],[1]),true,([1],[]),false,false,[]⟩),(14,⟨([1],[]),true,([],[]),true,false,[]⟩),(333,⟨([],[]),false,([],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 324)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 325)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14675 7 10 (by decide) (by decide)
      · right
        exact rec14677 7 10 (by decide) (by decide)
      · right
        exact rec14679 7 10 (by decide) (by decide)
      · right
        exact rec14681 7 10 (by decide) (by decide)
      · right
        exact rec14683 7 10 (by decide) (by decide)
      · right
        exact rec14685 7 10 (by decide) (by decide)
      · right
        exact rec14687 7 10 (by decide) (by decide)
      · right
        exact rec14689 7 10 (by decide) (by decide)
      · right
        exact rec14691 7 10 (by decide) (by decide)
      · right
        exact rec14693 7 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 326)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 5)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec111 7 10 (by decide) (by decide)
      · right
        exact rec113 7 10 (by decide) (by decide)
      · right
        exact rec115 7 10 (by decide) (by decide)
      · right
        exact rec119 7 10 (by decide) (by decide)
      · right
        exact rec123 7 10 (by decide) (by decide)
      · right
        exact rec127 7 10 (by decide) (by decide)
      · right
        exact rec129 7 10 (by decide) (by decide)
      · right
        exact rec131 7 10 (by decide) (by decide)
      · right
        exact rec133 7 10 (by decide) (by decide)
      · right
        exact rec135 7 10 (by decide) (by decide)
      · right
        exact rec137 7 10 (by decide) (by decide)
      · right
        exact rec139 7 10 (by decide) (by decide)
      · right
        exact rec141 7 10 (by decide) (by decide)
      · right
        exact rec143 7 10 (by decide) (by decide)
      · right
        exact rec145 7 10 (by decide) (by decide)
      · right
        exact rec147 7 10 (by decide) (by decide)
      · right
        exact rec149 7 10 (by decide) (by decide)
      · right
        exact rec151 7 10 (by decide) (by decide)
      · right
        exact rec153 7 10 (by decide) (by decide)
      · right
        exact rec155 7 10 (by decide) (by decide)
      · right
        exact rec157 7 10 (by decide) (by decide)
      · right
        exact rec159 7 10 (by decide) (by decide)
      · right
        exact rec161 7 10 (by decide) (by decide)
      · right
        exact rec163 7 10 (by decide) (by decide)
      · right
        exact rec165 7 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 327)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 328)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 329)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 330)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14695 7 10 (by decide) (by decide)
      · right
        exact rec14697 7 10 (by decide) (by decide)
      · right
        exact rec14699 7 10 (by decide) (by decide)
      · right
        exact rec14701 7 10 (by decide) (by decide)
      · right
        exact rec14703 7 10 (by decide) (by decide)
      · right
        exact rec14705 7 10 (by decide) (by decide)
      · right
        exact rec14707 7 10 (by decide) (by decide)
      · right
        exact rec14709 7 10 (by decide) (by decide)
      · right
        exact rec14711 7 10 (by decide) (by decide)
      · right
        exact rec14713 7 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 10)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 11)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec242 7 10 (by decide) (by decide)
      · right
        exact rec244 7 10 (by decide) (by decide)
      · right
        exact rec246 7 10 (by decide) (by decide)
      · right
        exact rec248 7 10 (by decide) (by decide)
      · right
        exact rec250 7 10 (by decide) (by decide)
      · right
        exact rec252 7 10 (by decide) (by decide)
      · right
        exact rec254 7 10 (by decide) (by decide)
      · right
        exact rec256 7 10 (by decide) (by decide)
      · right
        exact rec258 7 10 (by decide) (by decide)
      · right
        exact rec260 7 10 (by decide) (by decide)
      · right
        exact rec262 7 10 (by decide) (by decide)
      · right
        exact rec264 7 10 (by decide) (by decide)
      · right
        exact rec266 7 10 (by decide) (by decide)
      · right
        exact rec268 7 10 (by decide) (by decide)
      · right
        exact rec270 7 10 (by decide) (by decide)
      · right
        exact rec272 7 10 (by decide) (by decide)
      · right
        exact rec274 7 10 (by decide) (by decide)
      · right
        exact rec276 7 10 (by decide) (by decide)
      · right
        exact rec278 7 10 (by decide) (by decide)
      · right
        exact rec280 7 10 (by decide) (by decide)
      · right
        exact rec282 7 10 (by decide) (by decide)
      · right
        exact rec284 7 10 (by decide) (by decide)
      · right
        exact rec286 7 10 (by decide) (by decide)
      · right
        exact rec288 7 10 (by decide) (by decide)
      · right
        exact rec290 7 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 331)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 332)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 14)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · right
        exact rec293 7 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec296 7 10 (by decide) (by decide)
      · right
        exact rec300 7 10 (by decide) (by decide)
      · right
        exact rec304 7 10 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · right
        exact rec308 7 10 (by decide) (by decide)
      · right
        exact rec312 7 10 (by decide) (by decide)
      · right
        exact rec314 7 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec317 7 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 333)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec32 7 11 (by decide) (by decide)
  · left
    exact rec33 7 12 (by decide) (by decide)
  · left
    exact rec33 7 13 (by decide) (by decide)
  · left
    exact rec33 7 14 (by decide) (by decide)
  · left
    exact rec33 7 15 (by decide) (by decide)
end Section14Coverage_7_0_p0_16

#print axioms solution
