-- Prove2me | solution 1 for Freiman.section14_s0007_coverage0003_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T08:50:59.980253+00:00
-- url     : https://prove2.me/submissions/dc1720de-5623-44bb-996f-527dfa517c4d

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
namespace Section14Coverage_7_3_p0_16
private theorem rec4484 (si parent : ℕ) (hs : si ∈ ([1, 2, 3, 5, 6, 7, 9, 10, 13, 14, 15] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],341⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[335]? = some (⟨60,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],341⟩) from rfl))
private theorem rec4515 (si parent : ℕ) (hs : si ∈ ([1, 3, 5, 7, 9, 11, 13, 15] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,3,5,7,9,11,13,15],[0],341⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[366]? = some (⟨60,(-1),[1,3,5,7,9,11,13,15],[0],341⟩) from rfl))
private theorem rec4538 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[389]? = some (⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩) from rfl))
private theorem rec4539 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,7,15],[2],60⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[390]? = some (⟨60,(-1),[3,7,15],[2],60⟩) from rfl))
private theorem rec4540 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,7,15],[6],68⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[391]? = some (⟨60,(-1),[3,7,15],[6],68⟩) from rfl))
private theorem rec4541 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,7,15],[14],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[392]? = some (⟨60,(-1),[3,7,15],[14],243⟩) from rfl))
private theorem rec4542 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([4] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,7,15],[4],343⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[393]? = some (⟨60,(-1),[3,7,15],[4],343⟩) from rfl))
private theorem rec4543 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,7,15],[8],346⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[394]? = some (⟨60,(-1),[3,7,15],[8],346⟩) from rfl))
private theorem rec4544 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,7,15],[10],367⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[395]? = some (⟨60,(-1),[3,7,15],[10],367⟩) from rfl))
private theorem rec4545 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([12, 13] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,7,15],[12,13],385⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[396]? = some (⟨60,(-1),[3,7,15],[12,13],385⟩) from rfl))
private theorem rec4571 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[7],[3],62⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[422]? = some (⟨60,(-1),[7],[3],62⟩) from rfl))
private theorem rec4572 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([7] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[7],[7],72⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[423]? = some (⟨60,(-1),[7],[7],72⟩) from rfl))
private theorem rec4573 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([15] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[7],[15],245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[424]? = some (⟨60,(-1),[7],[15],245⟩) from rfl))
private theorem rec4710 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(0),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[561]? = some (⟨64,(0),[3,7],[9],3⟩) from rfl))
private theorem rec4711 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(0),[3,7,15],[11],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[562]? = some (⟨64,(0),[3,7,15],[11],368⟩) from rfl))
private theorem rec4716 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(1),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[567]? = some (⟨64,(1),[3,7],[9],3⟩) from rfl))
private theorem rec4717 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(1),[3,7,15],[11],369⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[568]? = some (⟨64,(1),[3,7,15],[11],369⟩) from rfl))
private theorem rec4722 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(2),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[573]? = some (⟨64,(2),[3,7],[9],3⟩) from rfl))
private theorem rec4723 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(2),[3,7,15],[11],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[574]? = some (⟨64,(2),[3,7,15],[11],368⟩) from rfl))
private theorem rec4728 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(3),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[579]? = some (⟨64,(3),[3,7],[9],3⟩) from rfl))
private theorem rec4729 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(3),[3,7,15],[11],370⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[580]? = some (⟨64,(3),[3,7,15],[11],370⟩) from rfl))
private theorem rec4734 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(4),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[585]? = some (⟨64,(4),[3,7],[9],3⟩) from rfl))
private theorem rec4735 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(4),[3,7,15],[11],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[586]? = some (⟨64,(4),[3,7,15],[11],371⟩) from rfl))
private theorem rec4740 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(5),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[591]? = some (⟨64,(5),[3,7],[9],3⟩) from rfl))
private theorem rec4741 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(5),[3,7,15],[11],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[592]? = some (⟨64,(5),[3,7,15],[11],368⟩) from rfl))
private theorem rec4746 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(6),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[597]? = some (⟨64,(6),[3,7],[9],3⟩) from rfl))
private theorem rec4747 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(6),[3,7,15],[11],369⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[598]? = some (⟨64,(6),[3,7,15],[11],369⟩) from rfl))
private theorem rec4752 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(7),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[603]? = some (⟨64,(7),[3,7],[9],3⟩) from rfl))
private theorem rec4753 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(7),[3,7,15],[11],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[604]? = some (⟨64,(7),[3,7,15],[11],368⟩) from rfl))
private theorem rec4758 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(8),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[609]? = some (⟨64,(8),[3,7],[9],3⟩) from rfl))
private theorem rec4759 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(8),[3,7,15],[11],370⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[610]? = some (⟨64,(8),[3,7,15],[11],370⟩) from rfl))
private theorem rec4764 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(9),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[615]? = some (⟨64,(9),[3,7],[9],3⟩) from rfl))
private theorem rec4765 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(9),[3,7,15],[11],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[616]? = some (⟨64,(9),[3,7,15],[11],371⟩) from rfl))
private theorem rec4770 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(10),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[621]? = some (⟨64,(10),[3,7],[9],3⟩) from rfl))
private theorem rec4771 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(10),[3,7,15],[11],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[622]? = some (⟨64,(10),[3,7,15],[11],372⟩) from rfl))
private theorem rec4776 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(11),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[627]? = some (⟨64,(11),[3,7],[9],3⟩) from rfl))
private theorem rec4777 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(11),[3,7,15],[11],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[628]? = some (⟨64,(11),[3,7,15],[11],372⟩) from rfl))
private theorem rec4782 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(12),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[633]? = some (⟨64,(12),[3,7],[9],3⟩) from rfl))
private theorem rec4783 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(12),[3,7,15],[11],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[634]? = some (⟨64,(12),[3,7,15],[11],372⟩) from rfl))
private theorem rec4788 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(13),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[639]? = some (⟨64,(13),[3,7],[9],3⟩) from rfl))
private theorem rec4789 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(13),[3,7,15],[11],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[640]? = some (⟨64,(13),[3,7,15],[11],372⟩) from rfl))
private theorem rec4794 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(14),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[645]? = some (⟨64,(14),[3,7],[9],3⟩) from rfl))
private theorem rec4795 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(14),[3,7,15],[11],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[646]? = some (⟨64,(14),[3,7,15],[11],371⟩) from rfl))
private theorem rec4800 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(15),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[651]? = some (⟨64,(15),[3,7],[9],3⟩) from rfl))
private theorem rec4801 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(15),[3,7,15],[11],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[652]? = some (⟨64,(15),[3,7,15],[11],373⟩) from rfl))
private theorem rec4806 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(16),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[657]? = some (⟨64,(16),[3,7],[9],3⟩) from rfl))
private theorem rec4807 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(16),[3,7,15],[11],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[658]? = some (⟨64,(16),[3,7,15],[11],373⟩) from rfl))
private theorem rec4812 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(17),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[663]? = some (⟨64,(17),[3,7],[9],3⟩) from rfl))
private theorem rec4813 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(17),[3,7,15],[11],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[664]? = some (⟨64,(17),[3,7,15],[11],373⟩) from rfl))
private theorem rec4818 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(18),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[669]? = some (⟨64,(18),[3,7],[9],3⟩) from rfl))
private theorem rec4819 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(18),[3,7,15],[11],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[670]? = some (⟨64,(18),[3,7,15],[11],373⟩) from rfl))
private theorem rec4824 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(19),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[675]? = some (⟨64,(19),[3,7],[9],3⟩) from rfl))
private theorem rec4825 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(19),[3,7,15],[11],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[676]? = some (⟨64,(19),[3,7,15],[11],373⟩) from rfl))
private theorem rec4830 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(20),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[681]? = some (⟨64,(20),[3,7],[9],3⟩) from rfl))
private theorem rec4831 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(20),[3,7,15],[11],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[682]? = some (⟨64,(20),[3,7,15],[11],374⟩) from rfl))
private theorem rec4836 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(21),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[687]? = some (⟨64,(21),[3,7],[9],3⟩) from rfl))
private theorem rec4837 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(21),[3,7,15],[11],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[688]? = some (⟨64,(21),[3,7,15],[11],374⟩) from rfl))
private theorem rec4842 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(22),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[693]? = some (⟨64,(22),[3,7],[9],3⟩) from rfl))
private theorem rec4843 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(22),[3,7,15],[11],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[694]? = some (⟨64,(22),[3,7,15],[11],374⟩) from rfl))
private theorem rec4848 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(23),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[699]? = some (⟨64,(23),[3,7],[9],3⟩) from rfl))
private theorem rec4849 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(23),[3,7,15],[11],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[700]? = some (⟨64,(23),[3,7,15],[11],374⟩) from rfl))
private theorem rec4854 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 64 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(24),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[705]? = some (⟨64,(24),[3,7],[9],3⟩) from rfl))
private theorem rec4855 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 64 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(24),[3,7,15],[11],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[706]? = some (⟨64,(24),[3,7,15],[11],374⟩) from rfl))
private theorem rec4935 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(0),[3,7],[9],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[786]? = some (⟨69,(0),[3,7],[9],189⟩) from rfl))
private theorem rec4936 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(0),[3,7,15],[11],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[787]? = some (⟨69,(0),[3,7,15],[11],189⟩) from rfl))
private theorem rec4943 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(1),[3,7],[9],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[794]? = some (⟨69,(1),[3,7],[9],190⟩) from rfl))
private theorem rec4944 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(1),[3,7,15],[11],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[795]? = some (⟨69,(1),[3,7,15],[11],260⟩) from rfl))
private theorem rec4953 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[3,7],[9],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[804]? = some (⟨69,(2),[3,7],[9],191⟩) from rfl))
private theorem rec4957 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[7],[11],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[808]? = some (⟨69,(2),[7],[11],375⟩) from rfl))
private theorem rec4965 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[3,7],[9],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[816]? = some (⟨69,(3),[3,7],[9],192⟩) from rfl))
private theorem rec4969 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[7],[11],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[820]? = some (⟨69,(3),[7],[11],376⟩) from rfl))
private theorem rec4977 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[3,7],[9],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[828]? = some (⟨69,(4),[3,7],[9],193⟩) from rfl))
private theorem rec4981 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[7],[11],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[832]? = some (⟨69,(4),[7],[11],377⟩) from rfl))
private theorem rec4988 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(5),[3,7],[9],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[839]? = some (⟨69,(5),[3,7],[9],189⟩) from rfl))
private theorem rec4989 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(5),[3,7,15],[11],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[840]? = some (⟨69,(5),[3,7,15],[11],189⟩) from rfl))
private theorem rec4996 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(6),[3,7],[9],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[847]? = some (⟨69,(6),[3,7],[9],190⟩) from rfl))
private theorem rec4997 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(6),[3,7,15],[11],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[848]? = some (⟨69,(6),[3,7,15],[11],260⟩) from rfl))
private theorem rec5005 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[3,7],[9],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[856]? = some (⟨69,(7),[3,7],[9],191⟩) from rfl))
private theorem rec5006 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[3,7,15],[11],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[857]? = some (⟨69,(7),[3,7,15],[11],375⟩) from rfl))
private theorem rec5015 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[3,7],[9],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[866]? = some (⟨69,(8),[3,7],[9],192⟩) from rfl))
private theorem rec5016 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[3,7,15],[11],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[867]? = some (⟨69,(8),[3,7,15],[11],376⟩) from rfl))
private theorem rec5025 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[3,7],[9],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[876]? = some (⟨69,(9),[3,7],[9],193⟩) from rfl))
private theorem rec5026 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[3,7,15],[11],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[877]? = some (⟨69,(9),[3,7,15],[11],377⟩) from rfl))
private theorem rec5035 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(10),[3,7],[9],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[886]? = some (⟨69,(10),[3,7],[9],194⟩) from rfl))
private theorem rec5036 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(10),[3,7,15],[11],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[887]? = some (⟨69,(10),[3,7,15],[11],194⟩) from rfl))
private theorem rec5043 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(11),[3,7],[9],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[894]? = some (⟨69,(11),[3,7],[9],195⟩) from rfl))
private theorem rec5044 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(11),[3,7,15],[11],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[895]? = some (⟨69,(11),[3,7,15],[11],267⟩) from rfl))
private theorem rec5052 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[3,7],[9],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[903]? = some (⟨69,(12),[3,7],[9],195⟩) from rfl))
private theorem rec5053 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[3,7,15],[11],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[904]? = some (⟨69,(12),[3,7,15],[11],378⟩) from rfl))
private theorem rec5062 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[3,7],[9],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[913]? = some (⟨69,(13),[3,7],[9],195⟩) from rfl))
private theorem rec5063 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[3,7,15],[11],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[914]? = some (⟨69,(13),[3,7,15],[11],378⟩) from rfl))
private theorem rec5072 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[3,7],[9],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[923]? = some (⟨69,(14),[3,7],[9],193⟩) from rfl))
private theorem rec5073 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[3,7,15],[11],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[924]? = some (⟨69,(14),[3,7,15],[11],377⟩) from rfl))
private theorem rec5082 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(15),[3,7],[9],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[933]? = some (⟨69,(15),[3,7],[9],196⟩) from rfl))
private theorem rec5083 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(15),[3,7,15],[11],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[934]? = some (⟨69,(15),[3,7,15],[11],196⟩) from rfl))
private theorem rec5090 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(16),[3,7],[9],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[941]? = some (⟨69,(16),[3,7],[9],197⟩) from rfl))
private theorem rec5091 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(16),[3,7,15],[11],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[942]? = some (⟨69,(16),[3,7,15],[11],269⟩) from rfl))
private theorem rec5099 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[3,7],[9],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[950]? = some (⟨69,(17),[3,7],[9],197⟩) from rfl))
private theorem rec5100 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[3,7,15],[11],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[951]? = some (⟨69,(17),[3,7,15],[11],379⟩) from rfl))
private theorem rec5109 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[3,7],[9],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[960]? = some (⟨69,(18),[3,7],[9],197⟩) from rfl))
private theorem rec5110 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[3,7,15],[11],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[961]? = some (⟨69,(18),[3,7,15],[11],379⟩) from rfl))
private theorem rec5119 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[3,7],[9],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[970]? = some (⟨69,(19),[3,7],[9],197⟩) from rfl))
private theorem rec5120 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[3,7,15],[11],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[971]? = some (⟨69,(19),[3,7,15],[11],379⟩) from rfl))
private theorem rec5129 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(20),[3,7],[9],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[980]? = some (⟨69,(20),[3,7],[9],198⟩) from rfl))
private theorem rec5130 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(20),[3,7,15],[11],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[981]? = some (⟨69,(20),[3,7,15],[11],198⟩) from rfl))
private theorem rec5137 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(21),[3,7],[9],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[988]? = some (⟨69,(21),[3,7],[9],199⟩) from rfl))
private theorem rec5138 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(21),[3,7,15],[11],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[989]? = some (⟨69,(21),[3,7,15],[11],271⟩) from rfl))
private theorem rec5146 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[3,7],[9],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[997]? = some (⟨69,(22),[3,7],[9],199⟩) from rfl))
private theorem rec5147 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[3,7,15],[11],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[998]? = some (⟨69,(22),[3,7,15],[11],380⟩) from rfl))
private theorem rec5156 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[3,7],[9],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1007]? = some (⟨69,(23),[3,7],[9],199⟩) from rfl))
private theorem rec5157 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[3,7,15],[11],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1008]? = some (⟨69,(23),[3,7,15],[11],380⟩) from rfl))
private theorem rec5166 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[3,7],[9],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1017]? = some (⟨69,(24),[3,7],[9],199⟩) from rfl))
private theorem rec5167 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[3,7,15],[11],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1018]? = some (⟨69,(24),[3,7,15],[11],380⟩) from rfl))
private theorem rec5304 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[3,7],[9],360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1155]? = some (⟨75,(0),[3,7],[9],360⟩) from rfl))
private theorem rec5305 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[3,7],[11],381⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1156]? = some (⟨75,(0),[3,7],[11],381⟩) from rfl))
private theorem rec5314 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[3,7],[9],361⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1165]? = some (⟨75,(1),[3,7],[9],361⟩) from rfl))
private theorem rec5315 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[3,7],[11],382⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1166]? = some (⟨75,(1),[3,7],[11],382⟩) from rfl))
private theorem rec5324 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[3,7],[9],362⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1175]? = some (⟨75,(2),[3,7],[9],362⟩) from rfl))
private theorem rec5325 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[3,7],[11],383⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1176]? = some (⟨75,(2),[3,7],[11],383⟩) from rfl))
private theorem rec5334 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[3,7],[9],363⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1185]? = some (⟨75,(3),[3,7],[9],363⟩) from rfl))
private theorem rec5335 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[3,7],[11],384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1186]? = some (⟨75,(3),[3,7],[11],384⟩) from rfl))
private theorem rec5514 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9, 11] : List ℕ)) : section14Recorded section14Catalog si parent 80 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(5),[3,7],[9,11],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[139]? = some (⟨80,(5),[3,7],[9,11],105⟩) from rfl))
private theorem rec5519 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 80 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(7),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[144]? = some (⟨80,(7),[3,7],[9],3⟩) from rfl))
private theorem rec5522 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 80 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(7),[7],[11],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[147]? = some (⟨80,(7),[7],[11],48⟩) from rfl))
private theorem rec5525 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 80 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(8),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[150]? = some (⟨80,(8),[3,7],[9],3⟩) from rfl))
private theorem rec5526 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 80 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(8),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[151]? = some (⟨80,(8),[3,7,15],[11],3⟩) from rfl))
private theorem rec5530 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 80 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(9),[3,7],[9],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[155]? = some (⟨80,(9),[3,7],[9],143⟩) from rfl))
private theorem rec5532 (si parent : ℕ) (hs : si ∈ ([7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 80 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(9),[7,15],[11],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[157]? = some (⟨80,(9),[7,15],[11],143⟩) from rfl))
private theorem rec5535 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 80 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(15),[3,7],[9],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[160]? = some (⟨80,(15),[3,7],[9],105⟩) from rfl))
private theorem rec5536 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 80 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(15),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[161]? = some (⟨80,(15),[3,7,15],[11],3⟩) from rfl))
private theorem rec5539 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 80 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(16),[3,7],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[164]? = some (⟨80,(16),[3,7],[9],3⟩) from rfl))
private theorem rec5540 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 80 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(16),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[165]? = some (⟨80,(16),[3,7,15],[11],3⟩) from rfl))
private theorem rec5544 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 80 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(17),[3,7,15],[11],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[169]? = some (⟨80,(17),[3,7,15],[11],48⟩) from rfl))
private theorem rec5546 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 80 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(17),[7],[9],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[171]? = some (⟨80,(17),[7],[9],48⟩) from rfl))
private theorem rec5550 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 80 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(19),[3,7,15],[11],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[175]? = some (⟨80,(19),[3,7,15],[11],143⟩) from rfl))
private theorem rec5552 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 80 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(19),[7],[9],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[177]? = some (⟨80,(19),[7],[9],143⟩) from rfl))
private theorem rec14960 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(0),[3,7],[9],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[39]? = some (⟨368,(0),[3,7],[9],347⟩) from rfl))
private theorem rec14961 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(0),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[40]? = some (⟨368,(0),[3,7,15],[11],3⟩) from rfl))
private theorem rec14963 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(1),[3,7],[9],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[42]? = some (⟨368,(1),[3,7],[9],347⟩) from rfl))
private theorem rec14964 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(1),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[43]? = some (⟨368,(1),[3,7,15],[11],3⟩) from rfl))
private theorem rec14966 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(2),[3,7],[9],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[45]? = some (⟨368,(2),[3,7],[9],348⟩) from rfl))
private theorem rec14967 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(2),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[46]? = some (⟨368,(2),[3,7,15],[11],3⟩) from rfl))
private theorem rec14969 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(3),[3,7],[9],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[48]? = some (⟨368,(3),[3,7],[9],348⟩) from rfl))
private theorem rec14970 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(3),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[49]? = some (⟨368,(3),[3,7,15],[11],3⟩) from rfl))
private theorem rec14972 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(4),[3,7],[9],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[51]? = some (⟨368,(4),[3,7],[9],349⟩) from rfl))
private theorem rec14973 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(4),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[52]? = some (⟨368,(4),[3,7,15],[11],3⟩) from rfl))
private theorem rec14975 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(5),[3,7],[9],351⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[54]? = some (⟨368,(5),[3,7],[9],351⟩) from rfl))
private theorem rec14976 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(5),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[55]? = some (⟨368,(5),[3,7,15],[11],3⟩) from rfl))
private theorem rec14978 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(6),[3,7],[9],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[57]? = some (⟨368,(6),[3,7],[9],349⟩) from rfl))
private theorem rec14979 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(6),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[58]? = some (⟨368,(6),[3,7,15],[11],3⟩) from rfl))
private theorem rec14981 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(7),[3,7],[9],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[60]? = some (⟨368,(7),[3,7],[9],353⟩) from rfl))
private theorem rec14982 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(7),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[61]? = some (⟨368,(7),[3,7,15],[11],3⟩) from rfl))
private theorem rec14984 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(8),[3,7],[9],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[63]? = some (⟨368,(8),[3,7],[9],349⟩) from rfl))
private theorem rec14985 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(8),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[64]? = some (⟨368,(8),[3,7,15],[11],3⟩) from rfl))
private theorem rec14987 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 368 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(9),[3,7],[9],351⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[66]? = some (⟨368,(9),[3,7],[9],351⟩) from rfl))
private theorem rec14988 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 368 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨368,(9),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[67]? = some (⟨368,(9),[3,7,15],[11],3⟩) from rfl))
private theorem rec14990 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(0),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[69]? = some (⟨372,(0),[3,7],[9],2⟩) from rfl))
private theorem rec14991 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(0),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[70]? = some (⟨372,(0),[3,7,15],[11],2⟩) from rfl))
private theorem rec14993 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(1),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[72]? = some (⟨372,(1),[3,7],[9],2⟩) from rfl))
private theorem rec14994 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(1),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[73]? = some (⟨372,(1),[3,7,15],[11],2⟩) from rfl))
private theorem rec14996 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(2),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[75]? = some (⟨372,(2),[3,7],[9],2⟩) from rfl))
private theorem rec14997 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(2),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[76]? = some (⟨372,(2),[3,7,15],[11],2⟩) from rfl))
private theorem rec14999 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(3),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[78]? = some (⟨372,(3),[3,7],[9],2⟩) from rfl))
private theorem rec15000 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(3),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[79]? = some (⟨372,(3),[3,7,15],[11],2⟩) from rfl))
private theorem rec15002 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(4),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[81]? = some (⟨372,(4),[3,7],[9],2⟩) from rfl))
private theorem rec15003 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(4),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[82]? = some (⟨372,(4),[3,7,15],[11],2⟩) from rfl))
private theorem rec15005 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(5),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[84]? = some (⟨372,(5),[3,7],[9],2⟩) from rfl))
private theorem rec15006 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(5),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[85]? = some (⟨372,(5),[3,7,15],[11],2⟩) from rfl))
private theorem rec15008 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(6),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[87]? = some (⟨372,(6),[3,7],[9],2⟩) from rfl))
private theorem rec15009 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(6),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[88]? = some (⟨372,(6),[3,7,15],[11],2⟩) from rfl))
private theorem rec15011 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(7),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[90]? = some (⟨372,(7),[3,7],[9],2⟩) from rfl))
private theorem rec15012 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(7),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[91]? = some (⟨372,(7),[3,7,15],[11],2⟩) from rfl))
private theorem rec15014 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(8),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[93]? = some (⟨372,(8),[3,7],[9],2⟩) from rfl))
private theorem rec15015 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(8),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[94]? = some (⟨372,(8),[3,7,15],[11],2⟩) from rfl))
private theorem rec15017 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 372 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(9),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[96]? = some (⟨372,(9),[3,7],[9],2⟩) from rfl))
private theorem rec15018 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 372 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨372,(9),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[97]? = some (⟨372,(9),[3,7,15],[11],2⟩) from rfl))
private theorem rec15021 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 376 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨376,(0),[7],[9],1541⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[100]? = some (⟨376,(0),[7],[9],1541⟩) from rfl))
private theorem rec15022 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 376 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨376,(0),[7],[11],1542⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[101]? = some (⟨376,(0),[7],[11],1542⟩) from rfl))
private theorem rec15025 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 376 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨376,(1),[3,7],[9],947⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[104]? = some (⟨376,(1),[3,7],[9],947⟩) from rfl))
private theorem rec15026 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 376 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨376,(1),[7],[11],1543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[105]? = some (⟨376,(1),[7],[11],1543⟩) from rfl))
private theorem rec15029 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 376 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨376,(2),[3,7],[9],946⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[108]? = some (⟨376,(2),[3,7],[9],946⟩) from rfl))
private theorem rec15030 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 376 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨376,(2),[7],[11],1544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[109]? = some (⟨376,(2),[7],[11],1544⟩) from rfl))
private theorem rec15033 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 376 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨376,(3),[3,7],[9],948⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[112]? = some (⟨376,(3),[3,7],[9],948⟩) from rfl))
private theorem rec15034 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 376 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨376,(3),[7],[11],1545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[113]? = some (⟨376,(3),[7],[11],1545⟩) from rfl))
private theorem rec15038 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9, 11] : List ℕ)) : section14Recorded section14Catalog si parent 379 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨379,(0),[7],[9,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[117]? = some (⟨379,(0),[7],[9,11],2⟩) from rfl))
private theorem rec15040 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 379 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨379,(1),[3,7],[9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[119]? = some (⟨379,(1),[3,7],[9],2⟩) from rfl))
private theorem rec15041 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 379 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨379,(1),[3,7,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[120]? = some (⟨379,(1),[3,7,15],[11],2⟩) from rfl))
private theorem rec15043 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 379 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨379,(2),[3,7],[9],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[122]? = some (⟨379,(2),[3,7],[9],159⟩) from rfl))
private theorem rec15044 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 379 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨379,(2),[3,7,15],[11],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[123]? = some (⟨379,(2),[3,7,15],[11],159⟩) from rfl))
private theorem rec15046 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 379 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨379,(3),[3,7],[9],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[125]? = some (⟨379,(3),[3,7],[9],99⟩) from rfl))
private theorem rec15047 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 379 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨379,(3),[3,7,15],[11],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[126]? = some (⟨379,(3),[3,7,15],[11],99⟩) from rfl))
private theorem rec15050 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 381 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(0),[3,7],[9],364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[129]? = some (⟨381,(0),[3,7],[9],364⟩) from rfl))
private theorem rec15051 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 381 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(0),[7],[11],1405⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[130]? = some (⟨381,(0),[7],[11],1405⟩) from rfl))
private theorem rec15054 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 381 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(1),[3,7],[9],949⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[133]? = some (⟨381,(1),[3,7],[9],949⟩) from rfl))
private theorem rec15055 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 381 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(1),[7],[11],1546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[134]? = some (⟨381,(1),[7],[11],1546⟩) from rfl))
private theorem rec15058 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 381 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(2),[3,7],[11],945⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[137]? = some (⟨381,(2),[3,7],[11],945⟩) from rfl))
private theorem rec15059 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 381 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(2),[7],[9],945⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[138]? = some (⟨381,(2),[7],[9],945⟩) from rfl))
private theorem rec15062 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 381 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(3),[3,7],[11],939⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[141]? = some (⟨381,(3),[3,7],[11],939⟩) from rfl))
private theorem rec15063 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 381 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(3),[7],[9],939⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[142]? = some (⟨381,(3),[7],[9],939⟩) from rfl))
private theorem rec15065 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 381 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(4),[3,7],[9],204⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[144]? = some (⟨381,(4),[3,7],[9],204⟩) from rfl))
private theorem rec15066 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 381 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨381,(4),[3,7],[11],950⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[145]? = some (⟨381,(4),[3,7],[11],950⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 7).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 7)).drop 0).take 16, section14Recorded section14Catalog 7 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 7).plans.drop 3).take 1 = [⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(367,⟨([1],[]),true,([1],[]),false,false,[]⟩),(368,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(369,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(370,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(371,⟨([2],[]),true,([2],[]),false,false,[]⟩),(372,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(373,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(374,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(375,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(376,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(377,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(378,⟨([1],[]),true,([2],[]),false,false,[]⟩),(379,⟨([2],[]),true,([1],[]),false,false,[]⟩),(380,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(381,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(382,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec4515 7 0 (by decide) (by decide)
  · left
    exact rec4484 7 1 (by decide) (by decide)
  · left
    exact rec4539 7 2 (by decide) (by decide)
  · left
    exact rec4571 7 3 (by decide) (by decide)
  · left
    exact rec4542 7 4 (by decide) (by decide)
  · left
    exact rec4538 7 5 (by decide) (by decide)
  · left
    exact rec4540 7 6 (by decide) (by decide)
  · left
    exact rec4572 7 7 (by decide) (by decide)
  · left
    exact rec4543 7 8 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(367,⟨([1],[]),true,([1],[]),false,false,[]⟩),(368,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(369,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(370,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(371,⟨([2],[]),true,([2],[]),false,false,[]⟩),(372,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(373,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(374,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(375,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(376,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(377,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(378,⟨([1],[]),true,([2],[]),false,false,[]⟩),(379,⟨([2],[]),true,([1],[]),false,false,[]⟩),(380,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(381,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(382,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 367)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 368)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14960 7 9 (by decide) (by decide)
      · right
        exact rec14963 7 9 (by decide) (by decide)
      · right
        exact rec14966 7 9 (by decide) (by decide)
      · right
        exact rec14969 7 9 (by decide) (by decide)
      · right
        exact rec14972 7 9 (by decide) (by decide)
      · right
        exact rec14975 7 9 (by decide) (by decide)
      · right
        exact rec14978 7 9 (by decide) (by decide)
      · right
        exact rec14981 7 9 (by decide) (by decide)
      · right
        exact rec14984 7 9 (by decide) (by decide)
      · right
        exact rec14987 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 369)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 64)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4710 7 9 (by decide) (by decide)
      · right
        exact rec4716 7 9 (by decide) (by decide)
      · right
        exact rec4722 7 9 (by decide) (by decide)
      · right
        exact rec4728 7 9 (by decide) (by decide)
      · right
        exact rec4734 7 9 (by decide) (by decide)
      · right
        exact rec4740 7 9 (by decide) (by decide)
      · right
        exact rec4746 7 9 (by decide) (by decide)
      · right
        exact rec4752 7 9 (by decide) (by decide)
      · right
        exact rec4758 7 9 (by decide) (by decide)
      · right
        exact rec4764 7 9 (by decide) (by decide)
      · right
        exact rec4770 7 9 (by decide) (by decide)
      · right
        exact rec4776 7 9 (by decide) (by decide)
      · right
        exact rec4782 7 9 (by decide) (by decide)
      · right
        exact rec4788 7 9 (by decide) (by decide)
      · right
        exact rec4794 7 9 (by decide) (by decide)
      · right
        exact rec4800 7 9 (by decide) (by decide)
      · right
        exact rec4806 7 9 (by decide) (by decide)
      · right
        exact rec4812 7 9 (by decide) (by decide)
      · right
        exact rec4818 7 9 (by decide) (by decide)
      · right
        exact rec4824 7 9 (by decide) (by decide)
      · right
        exact rec4830 7 9 (by decide) (by decide)
      · right
        exact rec4836 7 9 (by decide) (by decide)
      · right
        exact rec4842 7 9 (by decide) (by decide)
      · right
        exact rec4848 7 9 (by decide) (by decide)
      · right
        exact rec4854 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 370)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 371)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 372)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14990 7 9 (by decide) (by decide)
      · right
        exact rec14993 7 9 (by decide) (by decide)
      · right
        exact rec14996 7 9 (by decide) (by decide)
      · right
        exact rec14999 7 9 (by decide) (by decide)
      · right
        exact rec15002 7 9 (by decide) (by decide)
      · right
        exact rec15005 7 9 (by decide) (by decide)
      · right
        exact rec15008 7 9 (by decide) (by decide)
      · right
        exact rec15011 7 9 (by decide) (by decide)
      · right
        exact rec15014 7 9 (by decide) (by decide)
      · right
        exact rec15017 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 373)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 69)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4935 7 9 (by decide) (by decide)
      · right
        exact rec4943 7 9 (by decide) (by decide)
      · right
        exact rec4953 7 9 (by decide) (by decide)
      · right
        exact rec4965 7 9 (by decide) (by decide)
      · right
        exact rec4977 7 9 (by decide) (by decide)
      · right
        exact rec4988 7 9 (by decide) (by decide)
      · right
        exact rec4996 7 9 (by decide) (by decide)
      · right
        exact rec5005 7 9 (by decide) (by decide)
      · right
        exact rec5015 7 9 (by decide) (by decide)
      · right
        exact rec5025 7 9 (by decide) (by decide)
      · right
        exact rec5035 7 9 (by decide) (by decide)
      · right
        exact rec5043 7 9 (by decide) (by decide)
      · right
        exact rec5052 7 9 (by decide) (by decide)
      · right
        exact rec5062 7 9 (by decide) (by decide)
      · right
        exact rec5072 7 9 (by decide) (by decide)
      · right
        exact rec5082 7 9 (by decide) (by decide)
      · right
        exact rec5090 7 9 (by decide) (by decide)
      · right
        exact rec5099 7 9 (by decide) (by decide)
      · right
        exact rec5109 7 9 (by decide) (by decide)
      · right
        exact rec5119 7 9 (by decide) (by decide)
      · right
        exact rec5129 7 9 (by decide) (by decide)
      · right
        exact rec5137 7 9 (by decide) (by decide)
      · right
        exact rec5146 7 9 (by decide) (by decide)
      · right
        exact rec5156 7 9 (by decide) (by decide)
      · right
        exact rec5166 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 374)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 375)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 376)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15021 7 9 (by decide) (by decide)
      · right
        exact rec15025 7 9 (by decide) (by decide)
      · right
        exact rec15029 7 9 (by decide) (by decide)
      · right
        exact rec15033 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 377)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 74)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 75)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5304 7 9 (by decide) (by decide)
      · right
        exact rec5314 7 9 (by decide) (by decide)
      · right
        exact rec5324 7 9 (by decide) (by decide)
      · right
        exact rec5334 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 378)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 379)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15038 7 9 (by decide) (by decide)
      · right
        exact rec15040 7 9 (by decide) (by decide)
      · right
        exact rec15043 7 9 (by decide) (by decide)
      · right
        exact rec15046 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 380)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 381)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15050 7 9 (by decide) (by decide)
      · right
        exact rec15054 7 9 (by decide) (by decide)
      · right
        exact rec15059 7 9 (by decide) (by decide)
      · right
        exact rec15063 7 9 (by decide) (by decide)
      · right
        exact rec15065 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 80)).length = 20 := by decide +kernel
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
        exact rec5514 7 9 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec5519 7 9 (by decide) (by decide)
      · right
        exact rec5525 7 9 (by decide) (by decide)
      · right
        exact rec5530 7 9 (by decide) (by decide)
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
        exact rec5535 7 9 (by decide) (by decide)
      · right
        exact rec5539 7 9 (by decide) (by decide)
      · right
        exact rec5546 7 9 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec5552 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 382)).length = 4 := by decide +kernel
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
  · left
    exact rec4544 7 10 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(367,⟨([1],[]),true,([1],[]),false,false,[]⟩),(368,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(369,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(370,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(371,⟨([2],[]),true,([2],[]),false,false,[]⟩),(372,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(373,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(374,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(375,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(376,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(377,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(378,⟨([1],[]),true,([2],[]),false,false,[]⟩),(379,⟨([2],[]),true,([1],[]),false,false,[]⟩),(380,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(381,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(382,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 367)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 368)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14961 7 11 (by decide) (by decide)
      · right
        exact rec14964 7 11 (by decide) (by decide)
      · right
        exact rec14967 7 11 (by decide) (by decide)
      · right
        exact rec14970 7 11 (by decide) (by decide)
      · right
        exact rec14973 7 11 (by decide) (by decide)
      · right
        exact rec14976 7 11 (by decide) (by decide)
      · right
        exact rec14979 7 11 (by decide) (by decide)
      · right
        exact rec14982 7 11 (by decide) (by decide)
      · right
        exact rec14985 7 11 (by decide) (by decide)
      · right
        exact rec14988 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 369)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 64)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4711 7 11 (by decide) (by decide)
      · right
        exact rec4717 7 11 (by decide) (by decide)
      · right
        exact rec4723 7 11 (by decide) (by decide)
      · right
        exact rec4729 7 11 (by decide) (by decide)
      · right
        exact rec4735 7 11 (by decide) (by decide)
      · right
        exact rec4741 7 11 (by decide) (by decide)
      · right
        exact rec4747 7 11 (by decide) (by decide)
      · right
        exact rec4753 7 11 (by decide) (by decide)
      · right
        exact rec4759 7 11 (by decide) (by decide)
      · right
        exact rec4765 7 11 (by decide) (by decide)
      · right
        exact rec4771 7 11 (by decide) (by decide)
      · right
        exact rec4777 7 11 (by decide) (by decide)
      · right
        exact rec4783 7 11 (by decide) (by decide)
      · right
        exact rec4789 7 11 (by decide) (by decide)
      · right
        exact rec4795 7 11 (by decide) (by decide)
      · right
        exact rec4801 7 11 (by decide) (by decide)
      · right
        exact rec4807 7 11 (by decide) (by decide)
      · right
        exact rec4813 7 11 (by decide) (by decide)
      · right
        exact rec4819 7 11 (by decide) (by decide)
      · right
        exact rec4825 7 11 (by decide) (by decide)
      · right
        exact rec4831 7 11 (by decide) (by decide)
      · right
        exact rec4837 7 11 (by decide) (by decide)
      · right
        exact rec4843 7 11 (by decide) (by decide)
      · right
        exact rec4849 7 11 (by decide) (by decide)
      · right
        exact rec4855 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 370)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 371)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 372)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14991 7 11 (by decide) (by decide)
      · right
        exact rec14994 7 11 (by decide) (by decide)
      · right
        exact rec14997 7 11 (by decide) (by decide)
      · right
        exact rec15000 7 11 (by decide) (by decide)
      · right
        exact rec15003 7 11 (by decide) (by decide)
      · right
        exact rec15006 7 11 (by decide) (by decide)
      · right
        exact rec15009 7 11 (by decide) (by decide)
      · right
        exact rec15012 7 11 (by decide) (by decide)
      · right
        exact rec15015 7 11 (by decide) (by decide)
      · right
        exact rec15018 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 373)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 69)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4936 7 11 (by decide) (by decide)
      · right
        exact rec4944 7 11 (by decide) (by decide)
      · right
        exact rec4957 7 11 (by decide) (by decide)
      · right
        exact rec4969 7 11 (by decide) (by decide)
      · right
        exact rec4981 7 11 (by decide) (by decide)
      · right
        exact rec4989 7 11 (by decide) (by decide)
      · right
        exact rec4997 7 11 (by decide) (by decide)
      · right
        exact rec5006 7 11 (by decide) (by decide)
      · right
        exact rec5016 7 11 (by decide) (by decide)
      · right
        exact rec5026 7 11 (by decide) (by decide)
      · right
        exact rec5036 7 11 (by decide) (by decide)
      · right
        exact rec5044 7 11 (by decide) (by decide)
      · right
        exact rec5053 7 11 (by decide) (by decide)
      · right
        exact rec5063 7 11 (by decide) (by decide)
      · right
        exact rec5073 7 11 (by decide) (by decide)
      · right
        exact rec5083 7 11 (by decide) (by decide)
      · right
        exact rec5091 7 11 (by decide) (by decide)
      · right
        exact rec5100 7 11 (by decide) (by decide)
      · right
        exact rec5110 7 11 (by decide) (by decide)
      · right
        exact rec5120 7 11 (by decide) (by decide)
      · right
        exact rec5130 7 11 (by decide) (by decide)
      · right
        exact rec5138 7 11 (by decide) (by decide)
      · right
        exact rec5147 7 11 (by decide) (by decide)
      · right
        exact rec5157 7 11 (by decide) (by decide)
      · right
        exact rec5167 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 374)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 375)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 376)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15022 7 11 (by decide) (by decide)
      · right
        exact rec15026 7 11 (by decide) (by decide)
      · right
        exact rec15030 7 11 (by decide) (by decide)
      · right
        exact rec15034 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 377)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 74)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 75)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5305 7 11 (by decide) (by decide)
      · right
        exact rec5315 7 11 (by decide) (by decide)
      · right
        exact rec5325 7 11 (by decide) (by decide)
      · right
        exact rec5335 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 378)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 379)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15038 7 11 (by decide) (by decide)
      · right
        exact rec15041 7 11 (by decide) (by decide)
      · right
        exact rec15044 7 11 (by decide) (by decide)
      · right
        exact rec15047 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 380)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 381)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15051 7 11 (by decide) (by decide)
      · right
        exact rec15055 7 11 (by decide) (by decide)
      · right
        exact rec15058 7 11 (by decide) (by decide)
      · right
        exact rec15062 7 11 (by decide) (by decide)
      · right
        exact rec15066 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 80)).length = 20 := by decide +kernel
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
        exact rec5514 7 11 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec5522 7 11 (by decide) (by decide)
      · right
        exact rec5526 7 11 (by decide) (by decide)
      · right
        exact rec5532 7 11 (by decide) (by decide)
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
        exact rec5536 7 11 (by decide) (by decide)
      · right
        exact rec5540 7 11 (by decide) (by decide)
      · right
        exact rec5544 7 11 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec5550 7 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 382)).length = 4 := by decide +kernel
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
  · left
    exact rec4545 7 12 (by decide) (by decide)
  · left
    exact rec4545 7 13 (by decide) (by decide)
  · left
    exact rec4541 7 14 (by decide) (by decide)
  · left
    exact rec4573 7 15 (by decide) (by decide)
end Section14Coverage_7_3_p0_16

#print axioms solution
