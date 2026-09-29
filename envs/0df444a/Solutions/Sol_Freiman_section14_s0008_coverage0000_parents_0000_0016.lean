-- Prove2me | solution 1 for Freiman.section14_s0008_coverage0000_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:10:58.312996+00:00
-- url     : https://prove2.me/submissions/2b42f8c6-475c-425f-80b9-562d9ae32f62

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
namespace Section14Coverage_8_0_p0_16
private theorem rec22 (si parent : ℕ) (hs : si ∈ ([2, 4, 6, 8, 10, 12, 14, 16] : List ℕ)) (hp : parent ∈ ([0, 4] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[2,4,6,8,10,12,14,16],[0,4],4⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[22]? = some (⟨1,(-1),[2,4,6,8,10,12,14,16],[0,4],4⟩) from rfl))
private theorem rec27 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[3,4,7,8,12,15,16],[5],5⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[27]? = some (⟨1,(-1),[3,4,7,8,12,15,16],[5],5⟩) from rfl))
private theorem rec34 (si parent : ℕ) (hs : si ∈ ([4, 8, 10, 12, 16] : List ℕ)) (hp : parent ∈ ([8, 12] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[4,8,10,12,16],[8,12],4⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[34]? = some (⟨1,(-1),[4,8,10,12,16],[8,12],4⟩) from rfl))
private theorem rec35 (si parent : ℕ) (hs : si ∈ ([4, 8, 11, 12, 16] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[4,8,11,12,16],[1],5⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[35]? = some (⟨1,(-1),[4,8,11,12,16],[1],5⟩) from rfl))
private theorem rec36 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([9, 13] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[4,8,12,16],[9,13],5⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[36]? = some (⟨1,(-1),[4,8,12,16],[9,13],5⟩) from rfl))
private theorem rec37 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[4,8,12,16],[2],6⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[37]? = some (⟨1,(-1),[4,8,12,16],[2],6⟩) from rfl))
private theorem rec38 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([7, 11, 15] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[4,8,12,16],[7,11,15],8⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[38]? = some (⟨1,(-1),[4,8,12,16],[7,11,15],8⟩) from rfl))
private theorem rec39 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[4,8,12,16],[6],9⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[39]? = some (⟨1,(-1),[4,8,12,16],[6],9⟩) from rfl))
private theorem rec40 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[4,8,12,16],[14],55⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[40]? = some (⟨1,(-1),[4,8,12,16],[14],55⟩) from rfl))
private theorem rec44 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[8,12],[3],8⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[44]? = some (⟨1,(-1),[8,12],[3],8⟩) from rfl))
private theorem rec111 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(0),[3,4,7,8,15,16],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[111]? = some (⟨5,(0),[3,4,7,8,15,16],[10],10⟩) from rfl))
private theorem rec113 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(1),[3,4,7,8,15,16],[10],11⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[113]? = some (⟨5,(1),[3,4,7,8,15,16],[10],11⟩) from rfl))
private theorem rec117 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(2),[8],[10],15⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[117]? = some (⟨5,(2),[8],[10],15⟩) from rfl))
private theorem rec121 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(3),[8],[10],16⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[121]? = some (⟨5,(3),[8],[10],16⟩) from rfl))
private theorem rec125 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 5 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨5,(4),[8],[10],17⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[125]? = some (⟨5,(4),[8],[10],17⟩) from rfl))
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
private theorem rec167 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(0),[4,8,12,16],[10],6⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[167]? = some (⟨9,(0),[4,8,12,16],[10],6⟩) from rfl))
private theorem rec170 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(1),[4,8,12,16],[10],27⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[170]? = some (⟨9,(1),[4,8,12,16],[10],27⟩) from rfl))
private theorem rec173 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(2),[4,8,12,16],[10],28⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[173]? = some (⟨9,(2),[4,8,12,16],[10],28⟩) from rfl))
private theorem rec176 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(3),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[176]? = some (⟨9,(3),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec179 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(4),[4,8,12,16],[10],30⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[179]? = some (⟨9,(4),[4,8,12,16],[10],30⟩) from rfl))
private theorem rec182 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(5),[4,8,12,16],[10],6⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[182]? = some (⟨9,(5),[4,8,12,16],[10],6⟩) from rfl))
private theorem rec185 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(6),[4,8,12,16],[10],27⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[185]? = some (⟨9,(6),[4,8,12,16],[10],27⟩) from rfl))
private theorem rec188 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(7),[4,8,12,16],[10],31⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[188]? = some (⟨9,(7),[4,8,12,16],[10],31⟩) from rfl))
private theorem rec191 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(8),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[191]? = some (⟨9,(8),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec194 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(9),[4,8,12,16],[10],32⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[194]? = some (⟨9,(9),[4,8,12,16],[10],32⟩) from rfl))
private theorem rec197 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(10),[4,8,12,16],[10],6⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[197]? = some (⟨9,(10),[4,8,12,16],[10],6⟩) from rfl))
private theorem rec200 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(11),[4,8,12,16],[10],27⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[200]? = some (⟨9,(11),[4,8,12,16],[10],27⟩) from rfl))
private theorem rec203 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(12),[4,8,12,16],[10],33⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[203]? = some (⟨9,(12),[4,8,12,16],[10],33⟩) from rfl))
private theorem rec206 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(13),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[206]? = some (⟨9,(13),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec209 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(14),[4,8,12,16],[10],34⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[209]? = some (⟨9,(14),[4,8,12,16],[10],34⟩) from rfl))
private theorem rec212 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(15),[4,8,12,16],[10],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[212]? = some (⟨9,(15),[4,8,12,16],[10],35⟩) from rfl))
private theorem rec215 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(16),[4,8,12,16],[10],36⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[215]? = some (⟨9,(16),[4,8,12,16],[10],36⟩) from rfl))
private theorem rec218 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(17),[4,8,12,16],[10],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[218]? = some (⟨9,(17),[4,8,12,16],[10],37⟩) from rfl))
private theorem rec221 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(18),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[221]? = some (⟨9,(18),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec224 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(19),[4,8,12,16],[10],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[224]? = some (⟨9,(19),[4,8,12,16],[10],37⟩) from rfl))
private theorem rec227 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(20),[4,8,12,16],[10],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[227]? = some (⟨9,(20),[4,8,12,16],[10],38⟩) from rfl))
private theorem rec230 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(21),[4,8,12,16],[10],39⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[230]? = some (⟨9,(21),[4,8,12,16],[10],39⟩) from rfl))
private theorem rec233 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(22),[4,8,12,16],[10],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[233]? = some (⟨9,(22),[4,8,12,16],[10],40⟩) from rfl))
private theorem rec236 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(23),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[236]? = some (⟨9,(23),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec239 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 9 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(24),[4,8,12,16],[10],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[239]? = some (⟨9,(24),[4,8,12,16],[10],40⟩) from rfl))
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
private theorem rec320 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 15 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(1),[4,8,12],[10],49⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[320]? = some (⟨15,(1),[4,8,12],[10],49⟩) from rfl))
private theorem rec323 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 15 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(3),[4,8,12],[10],50⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[323]? = some (⟨15,(3),[4,8,12],[10],50⟩) from rfl))
private theorem rec328 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 15 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(5),[8,12],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[328]? = some (⟨15,(5),[8,12],[10],143⟩) from rfl))
private theorem rec333 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 15 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(7),[8,12],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[333]? = some (⟨15,(7),[8,12],[10],143⟩) from rfl))
private theorem rec339 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 15 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(11),[8,12],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[339]? = some (⟨15,(11),[8,12],[10],143⟩) from rfl))
private theorem rec345 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 15 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(13),[8,12],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[345]? = some (⟨15,(13),[8,12],[10],143⟩) from rfl))
private theorem rec350 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 15 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(15),[4,8],[10],53⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[350]? = some (⟨15,(15),[4,8],[10],53⟩) from rfl))
private theorem rec356 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 15 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(17),[8,12],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[356]? = some (⟨15,(17),[8,12],[10],143⟩) from rfl))
private theorem rec15940 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(0),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1019]? = some (⟨478,(0),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15941 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(1),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1020]? = some (⟨478,(1),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15942 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(2),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1021]? = some (⟨478,(2),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15943 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(3),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1022]? = some (⟨478,(3),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15944 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(4),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1023]? = some (⟨478,(4),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15945 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(5),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1024]? = some (⟨478,(5),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15946 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(6),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1025]? = some (⟨478,(6),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15947 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(7),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1026]? = some (⟨478,(7),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15948 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(8),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1027]? = some (⟨478,(8),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec15949 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 478 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨478,(9),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1028]? = some (⟨478,(9),[4,8,12,16],[10],3⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 8).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 8)).drop 0).take 16, section14Recorded section14Catalog 8 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 8 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 8).plans.drop 0).take 1 = [⟨1,1,[([1],[]),([],[1])],false,[(477,⟨([1],[]),true,([1],[]),false,false,[]⟩),(478,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(479,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(5,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(6,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(7,⟨([],[1]),true,([],[1]),false,false,[]⟩),(8,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(9,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(10,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(11,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(480,⟨([1],[]),true,([],[1]),false,false,[]⟩),(13,⟨([],[1]),true,([1],[]),false,false,[]⟩),(481,⟨([1],[]),true,([],[]),true,false,[]⟩),(15,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 8)).drop 0).take 16 = [⟨3,0,[⟨true,false,15⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨3,1,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,2,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,3,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,4,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨3,5,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,6,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,7,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,8,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨3,9,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨3,10,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨3,11,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨3,12,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨3,13,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨3,14,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨3,15,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec22 8 0 (by decide) (by decide)
  · left
    exact rec35 8 1 (by decide) (by decide)
  · left
    exact rec37 8 2 (by decide) (by decide)
  · left
    exact rec44 8 3 (by decide) (by decide)
  · left
    exact rec22 8 4 (by decide) (by decide)
  · left
    exact rec27 8 5 (by decide) (by decide)
  · left
    exact rec39 8 6 (by decide) (by decide)
  · left
    exact rec38 8 7 (by decide) (by decide)
  · left
    exact rec34 8 8 (by decide) (by decide)
  · left
    exact rec36 8 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(477,⟨([1],[]),true,([1],[]),false,false,[]⟩),(478,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(479,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(5,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(6,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(7,⟨([],[1]),true,([],[1]),false,false,[]⟩),(8,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(9,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(10,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(11,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(480,⟨([1],[]),true,([],[1]),false,false,[]⟩),(13,⟨([],[1]),true,([1],[]),false,false,[]⟩),(481,⟨([1],[]),true,([],[]),true,false,[]⟩),(15,⟨([],[]),false,([],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 477)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 478)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15940 8 10 (by decide) (by decide)
      · right
        exact rec15941 8 10 (by decide) (by decide)
      · right
        exact rec15942 8 10 (by decide) (by decide)
      · right
        exact rec15943 8 10 (by decide) (by decide)
      · right
        exact rec15944 8 10 (by decide) (by decide)
      · right
        exact rec15945 8 10 (by decide) (by decide)
      · right
        exact rec15946 8 10 (by decide) (by decide)
      · right
        exact rec15947 8 10 (by decide) (by decide)
      · right
        exact rec15948 8 10 (by decide) (by decide)
      · right
        exact rec15949 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 479)).length = 10 := by decide +kernel
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
        exact rec111 8 10 (by decide) (by decide)
      · right
        exact rec113 8 10 (by decide) (by decide)
      · right
        exact rec117 8 10 (by decide) (by decide)
      · right
        exact rec121 8 10 (by decide) (by decide)
      · right
        exact rec125 8 10 (by decide) (by decide)
      · right
        exact rec127 8 10 (by decide) (by decide)
      · right
        exact rec129 8 10 (by decide) (by decide)
      · right
        exact rec131 8 10 (by decide) (by decide)
      · right
        exact rec133 8 10 (by decide) (by decide)
      · right
        exact rec135 8 10 (by decide) (by decide)
      · right
        exact rec137 8 10 (by decide) (by decide)
      · right
        exact rec139 8 10 (by decide) (by decide)
      · right
        exact rec141 8 10 (by decide) (by decide)
      · right
        exact rec143 8 10 (by decide) (by decide)
      · right
        exact rec145 8 10 (by decide) (by decide)
      · right
        exact rec147 8 10 (by decide) (by decide)
      · right
        exact rec149 8 10 (by decide) (by decide)
      · right
        exact rec151 8 10 (by decide) (by decide)
      · right
        exact rec153 8 10 (by decide) (by decide)
      · right
        exact rec155 8 10 (by decide) (by decide)
      · right
        exact rec157 8 10 (by decide) (by decide)
      · right
        exact rec159 8 10 (by decide) (by decide)
      · right
        exact rec161 8 10 (by decide) (by decide)
      · right
        exact rec163 8 10 (by decide) (by decide)
      · right
        exact rec165 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 6)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 7)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 8)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 9)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec167 8 10 (by decide) (by decide)
      · right
        exact rec170 8 10 (by decide) (by decide)
      · right
        exact rec173 8 10 (by decide) (by decide)
      · right
        exact rec176 8 10 (by decide) (by decide)
      · right
        exact rec179 8 10 (by decide) (by decide)
      · right
        exact rec182 8 10 (by decide) (by decide)
      · right
        exact rec185 8 10 (by decide) (by decide)
      · right
        exact rec188 8 10 (by decide) (by decide)
      · right
        exact rec191 8 10 (by decide) (by decide)
      · right
        exact rec194 8 10 (by decide) (by decide)
      · right
        exact rec197 8 10 (by decide) (by decide)
      · right
        exact rec200 8 10 (by decide) (by decide)
      · right
        exact rec203 8 10 (by decide) (by decide)
      · right
        exact rec206 8 10 (by decide) (by decide)
      · right
        exact rec209 8 10 (by decide) (by decide)
      · right
        exact rec212 8 10 (by decide) (by decide)
      · right
        exact rec215 8 10 (by decide) (by decide)
      · right
        exact rec218 8 10 (by decide) (by decide)
      · right
        exact rec221 8 10 (by decide) (by decide)
      · right
        exact rec224 8 10 (by decide) (by decide)
      · right
        exact rec227 8 10 (by decide) (by decide)
      · right
        exact rec230 8 10 (by decide) (by decide)
      · right
        exact rec233 8 10 (by decide) (by decide)
      · right
        exact rec236 8 10 (by decide) (by decide)
      · right
        exact rec239 8 10 (by decide) (by decide)
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
        exact rec242 8 10 (by decide) (by decide)
      · right
        exact rec244 8 10 (by decide) (by decide)
      · right
        exact rec246 8 10 (by decide) (by decide)
      · right
        exact rec248 8 10 (by decide) (by decide)
      · right
        exact rec250 8 10 (by decide) (by decide)
      · right
        exact rec252 8 10 (by decide) (by decide)
      · right
        exact rec254 8 10 (by decide) (by decide)
      · right
        exact rec256 8 10 (by decide) (by decide)
      · right
        exact rec258 8 10 (by decide) (by decide)
      · right
        exact rec260 8 10 (by decide) (by decide)
      · right
        exact rec262 8 10 (by decide) (by decide)
      · right
        exact rec264 8 10 (by decide) (by decide)
      · right
        exact rec266 8 10 (by decide) (by decide)
      · right
        exact rec268 8 10 (by decide) (by decide)
      · right
        exact rec270 8 10 (by decide) (by decide)
      · right
        exact rec272 8 10 (by decide) (by decide)
      · right
        exact rec274 8 10 (by decide) (by decide)
      · right
        exact rec276 8 10 (by decide) (by decide)
      · right
        exact rec278 8 10 (by decide) (by decide)
      · right
        exact rec280 8 10 (by decide) (by decide)
      · right
        exact rec282 8 10 (by decide) (by decide)
      · right
        exact rec284 8 10 (by decide) (by decide)
      · right
        exact rec286 8 10 (by decide) (by decide)
      · right
        exact rec288 8 10 (by decide) (by decide)
      · right
        exact rec290 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 480)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 13)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 481)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 15)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · right
        exact rec320 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec323 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec328 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec333 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · right
        exact rec339 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec345 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec350 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec356 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec38 8 11 (by decide) (by decide)
  · left
    exact rec34 8 12 (by decide) (by decide)
  · left
    exact rec36 8 13 (by decide) (by decide)
  · left
    exact rec40 8 14 (by decide) (by decide)
  · left
    exact rec38 8 15 (by decide) (by decide)
end Section14Coverage_8_0_p0_16

#print axioms solution
