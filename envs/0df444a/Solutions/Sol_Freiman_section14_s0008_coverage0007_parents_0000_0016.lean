-- Prove2me | solution 1 for Freiman.section14_s0008_coverage0007_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:41:24.430288+00:00
-- url     : https://prove2.me/submissions/eb312b61-9ae3-4e47-ab69-c4781acca84e

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
namespace Section14Coverage_8_7_p0_16
private theorem rec13298 (si parent : ℕ) (hs : si ∈ ([2, 4, 6, 8, 10, 12, 14, 16] : List ℕ)) (hp : parent ∈ ([0, 4] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[850]? = some (⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩) from rfl))
private theorem rec13303 (si parent : ℕ) (hs : si ∈ ([4, 8, 10, 12, 16] : List ℕ)) (hp : parent ∈ ([8, 12] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[4,8,10,12,16],[8,12],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[855]? = some (⟨260,(-1),[4,8,10,12,16],[8,12],882⟩) from rfl))
private theorem rec13304 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([1, 5, 9, 13] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[4,8,12,16],[1,5,9,13],883⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[856]? = some (⟨260,(-1),[4,8,12,16],[1,5,9,13],883⟩) from rfl))
private theorem rec13305 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[4,8,12,16],[2],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[857]? = some (⟨260,(-1),[4,8,12,16],[2],884⟩) from rfl))
private theorem rec13306 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([7, 11, 15] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[4,8,12,16],[7,11,15],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[858]? = some (⟨260,(-1),[4,8,12,16],[7,11,15],886⟩) from rfl))
private theorem rec13307 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[4,8,12,16],[6],887⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[859]? = some (⟨260,(-1),[4,8,12,16],[6],887⟩) from rfl))
private theorem rec13308 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[4,8,12,16],[14],909⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[860]? = some (⟨260,(-1),[4,8,12,16],[14],909⟩) from rfl))
private theorem rec13313 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[8,12],[3],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[865]? = some (⟨260,(-1),[8,12],[3],886⟩) from rfl))
private theorem rec13381 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(0),[8],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[933]? = some (⟨264,(0),[8],[10],10⟩) from rfl))
private theorem rec13383 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(1),[8],[10],1408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[935]? = some (⟨264,(1),[8],[10],1408⟩) from rfl))
private theorem rec13385 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(2),[8],[10],1407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[937]? = some (⟨264,(2),[8],[10],1407⟩) from rfl))
private theorem rec13387 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(3),[8],[10],1409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[939]? = some (⟨264,(3),[8],[10],1409⟩) from rfl))
private theorem rec13389 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(4),[8],[10],1410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[941]? = some (⟨264,(4),[8],[10],1410⟩) from rfl))
private theorem rec13391 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(5),[8],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[943]? = some (⟨264,(5),[8],[10],10⟩) from rfl))
private theorem rec13393 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(6),[8],[10],1408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[945]? = some (⟨264,(6),[8],[10],1408⟩) from rfl))
private theorem rec13395 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(7),[8],[10],1407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[947]? = some (⟨264,(7),[8],[10],1407⟩) from rfl))
private theorem rec13397 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(8),[8],[10],1409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[949]? = some (⟨264,(8),[8],[10],1409⟩) from rfl))
private theorem rec13399 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(9),[8],[10],1410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[951]? = some (⟨264,(9),[8],[10],1410⟩) from rfl))
private theorem rec13401 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(10),[8],[10],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[953]? = some (⟨264,(10),[8],[10],18⟩) from rfl))
private theorem rec13403 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(11),[8],[10],1411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[955]? = some (⟨264,(11),[8],[10],1411⟩) from rfl))
private theorem rec13405 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(12),[8],[10],1411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[957]? = some (⟨264,(12),[8],[10],1411⟩) from rfl))
private theorem rec13407 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(13),[8],[10],1411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[959]? = some (⟨264,(13),[8],[10],1411⟩) from rfl))
private theorem rec13409 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(14),[8],[10],1410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[961]? = some (⟨264,(14),[8],[10],1410⟩) from rfl))
private theorem rec13411 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(15),[8],[10],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[963]? = some (⟨264,(15),[8],[10],21⟩) from rfl))
private theorem rec13413 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(16),[8],[10],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[965]? = some (⟨264,(16),[8],[10],1412⟩) from rfl))
private theorem rec13415 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(17),[8],[10],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[967]? = some (⟨264,(17),[8],[10],1412⟩) from rfl))
private theorem rec13417 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(18),[8],[10],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[969]? = some (⟨264,(18),[8],[10],1412⟩) from rfl))
private theorem rec13419 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(19),[8],[10],1412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[971]? = some (⟨264,(19),[8],[10],1412⟩) from rfl))
private theorem rec13421 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(20),[8],[10],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[973]? = some (⟨264,(20),[8],[10],24⟩) from rfl))
private theorem rec13423 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(21),[8],[10],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[975]? = some (⟨264,(21),[8],[10],1413⟩) from rfl))
private theorem rec13425 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(22),[8],[10],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[977]? = some (⟨264,(22),[8],[10],1413⟩) from rfl))
private theorem rec13427 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(23),[8],[10],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[979]? = some (⟨264,(23),[8],[10],1413⟩) from rfl))
private theorem rec13429 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 264 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨264,(24),[8],[10],1413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[981]? = some (⟨264,(24),[8],[10],1413⟩) from rfl))
private theorem rec13431 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(0),[8,12],[10],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[983]? = some (⟨267,(0),[8,12],[10],1086⟩) from rfl))
private theorem rec13434 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(1),[8,12],[10],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[986]? = some (⟨267,(1),[8,12],[10],1087⟩) from rfl))
private theorem rec13437 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(2),[8,12],[10],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[989]? = some (⟨267,(2),[8,12],[10],1088⟩) from rfl))
private theorem rec13440 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(3),[8,12],[10],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[992]? = some (⟨267,(3),[8,12],[10],1089⟩) from rfl))
private theorem rec13443 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(4),[8,12],[10],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[995]? = some (⟨267,(4),[8,12],[10],1086⟩) from rfl))
private theorem rec13446 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(5),[8,12],[10],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[998]? = some (⟨267,(5),[8,12],[10],1087⟩) from rfl))
private theorem rec13449 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(6),[8,12],[10],1090⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1001]? = some (⟨267,(6),[8,12],[10],1090⟩) from rfl))
private theorem rec13452 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(7),[8,12],[10],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1004]? = some (⟨267,(7),[8,12],[10],1089⟩) from rfl))
private theorem rec13455 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(8),[8,12],[10],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1007]? = some (⟨267,(8),[8,12],[10],1086⟩) from rfl))
private theorem rec13458 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(9),[8,12],[10],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1010]? = some (⟨267,(9),[8,12],[10],1087⟩) from rfl))
private theorem rec13461 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(10),[8,12],[10],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1013]? = some (⟨267,(10),[8,12],[10],1088⟩) from rfl))
private theorem rec13464 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(11),[8,12],[10],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1016]? = some (⟨267,(11),[8,12],[10],1089⟩) from rfl))
private theorem rec13467 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(12),[8,12],[10],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1019]? = some (⟨267,(12),[8,12],[10],1086⟩) from rfl))
private theorem rec13470 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(13),[8,12],[10],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1022]? = some (⟨267,(13),[8,12],[10],1087⟩) from rfl))
private theorem rec13473 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(14),[8,12],[10],1091⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1025]? = some (⟨267,(14),[8,12],[10],1091⟩) from rfl))
private theorem rec13476 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 267 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(15),[8,12],[10],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1028]? = some (⟨267,(15),[8,12],[10],1089⟩) from rfl))
private theorem rec13479 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(0),[8,12],[10],1414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1031]? = some (⟨270,(0),[8,12],[10],1414⟩) from rfl))
private theorem rec13482 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(1),[8,12],[10],1415⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1034]? = some (⟨270,(1),[8,12],[10],1415⟩) from rfl))
private theorem rec13485 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(2),[8,12],[10],1414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1037]? = some (⟨270,(2),[8,12],[10],1414⟩) from rfl))
private theorem rec13488 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(3),[8,12],[10],1416⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1040]? = some (⟨270,(3),[8,12],[10],1416⟩) from rfl))
private theorem rec13491 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(4),[8,12],[10],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1043]? = some (⟨270,(4),[8,12],[10],1417⟩) from rfl))
private theorem rec13494 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(5),[8,12],[10],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1046]? = some (⟨270,(5),[8,12],[10],1417⟩) from rfl))
private theorem rec13497 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(6),[8,12],[10],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1049]? = some (⟨270,(6),[8,12],[10],1417⟩) from rfl))
private theorem rec13500 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(7),[8,12],[10],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1052]? = some (⟨270,(7),[8,12],[10],1417⟩) from rfl))
private theorem rec13503 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(8),[8,12],[10],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1055]? = some (⟨270,(8),[8,12],[10],1418⟩) from rfl))
private theorem rec13506 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(9),[8,12],[10],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1058]? = some (⟨270,(9),[8,12],[10],1418⟩) from rfl))
private theorem rec13509 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(10),[8,12],[10],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1061]? = some (⟨270,(10),[8,12],[10],1418⟩) from rfl))
private theorem rec13512 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(11),[8,12],[10],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1064]? = some (⟨270,(11),[8,12],[10],1418⟩) from rfl))
private theorem rec13515 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(12),[8,12],[10],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1067]? = some (⟨270,(12),[8,12],[10],1419⟩) from rfl))
private theorem rec13518 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(13),[8,12],[10],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1070]? = some (⟨270,(13),[8,12],[10],1419⟩) from rfl))
private theorem rec13521 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(14),[8,12],[10],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1073]? = some (⟨270,(14),[8,12],[10],1419⟩) from rfl))
private theorem rec13524 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 270 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(15),[8,12],[10],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1076]? = some (⟨270,(15),[8,12],[10],1419⟩) from rfl))
private theorem rec13527 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(0),[8,12],[10],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1079]? = some (⟨273,(0),[8,12],[10],1098⟩) from rfl))
private theorem rec13530 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(1),[8,12],[10],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1082]? = some (⟨273,(1),[8,12],[10],1099⟩) from rfl))
private theorem rec13533 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(2),[8,12],[10],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1085]? = some (⟨273,(2),[8,12],[10],1100⟩) from rfl))
private theorem rec13536 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(3),[8,12],[10],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1088]? = some (⟨273,(3),[8,12],[10],1100⟩) from rfl))
private theorem rec13539 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(4),[8,12],[10],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1091]? = some (⟨273,(4),[8,12],[10],1100⟩) from rfl))
private theorem rec13542 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(5),[8,12],[10],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1094]? = some (⟨273,(5),[8,12],[10],1098⟩) from rfl))
private theorem rec13545 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(6),[8,12],[10],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1097]? = some (⟨273,(6),[8,12],[10],1099⟩) from rfl))
private theorem rec13548 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(7),[8,12],[10],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1100]? = some (⟨273,(7),[8,12],[10],1101⟩) from rfl))
private theorem rec13551 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(8),[8,12],[10],1102⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1103]? = some (⟨273,(8),[8,12],[10],1102⟩) from rfl))
private theorem rec13554 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 273 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(9),[8,12],[10],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1106]? = some (⟨273,(9),[8,12],[10],1101⟩) from rfl))
private theorem rec13557 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(0),[8,12],[10],1420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1109]? = some (⟨275,(0),[8,12],[10],1420⟩) from rfl))
private theorem rec13560 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(1),[8,12],[10],1420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1112]? = some (⟨275,(1),[8,12],[10],1420⟩) from rfl))
private theorem rec13563 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(2),[8,12],[10],1421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1115]? = some (⟨275,(2),[8,12],[10],1421⟩) from rfl))
private theorem rec13566 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(3),[8,12],[10],1422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1118]? = some (⟨275,(3),[8,12],[10],1422⟩) from rfl))
private theorem rec13569 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(4),[8,12],[10],1423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1121]? = some (⟨275,(4),[8,12],[10],1423⟩) from rfl))
private theorem rec13572 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(5),[8,12],[10],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1124]? = some (⟨275,(5),[8,12],[10],1424⟩) from rfl))
private theorem rec13575 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(6),[8,12],[10],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1127]? = some (⟨275,(6),[8,12],[10],1424⟩) from rfl))
private theorem rec13578 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(7),[8,12],[10],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1130]? = some (⟨275,(7),[8,12],[10],1424⟩) from rfl))
private theorem rec13581 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(8),[8,12],[10],1422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1133]? = some (⟨275,(8),[8,12],[10],1422⟩) from rfl))
private theorem rec13584 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 275 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(9),[8,12],[10],1423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1136]? = some (⟨275,(9),[8,12],[10],1423⟩) from rfl))
private theorem rec13587 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(0),[8,12],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1139]? = some (⟨278,(0),[8,12],[10],1108⟩) from rfl))
private theorem rec13590 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(1),[8,12],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1142]? = some (⟨278,(1),[8,12],[10],1109⟩) from rfl))
private theorem rec13593 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(2),[8,12],[10],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1145]? = some (⟨278,(2),[8,12],[10],1110⟩) from rfl))
private theorem rec13596 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(3),[8,12],[10],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1148]? = some (⟨278,(3),[8,12],[10],1110⟩) from rfl))
private theorem rec13599 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(4),[8,12],[10],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1151]? = some (⟨278,(4),[8,12],[10],1110⟩) from rfl))
private theorem rec13602 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(5),[8,12],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1154]? = some (⟨278,(5),[8,12],[10],1108⟩) from rfl))
private theorem rec13605 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(6),[8,12],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[2]? = some (⟨278,(6),[8,12],[10],1109⟩) from rfl))
private theorem rec13608 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(7),[8,12],[10],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[5]? = some (⟨278,(7),[8,12],[10],1111⟩) from rfl))
private theorem rec13611 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(8),[8,12],[10],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[8]? = some (⟨278,(8),[8,12],[10],1112⟩) from rfl))
private theorem rec13614 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(9),[8,12],[10],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[11]? = some (⟨278,(9),[8,12],[10],1111⟩) from rfl))
private theorem rec13617 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(10),[8,12],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[14]? = some (⟨278,(10),[8,12],[10],1108⟩) from rfl))
private theorem rec13620 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(11),[8,12],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[17]? = some (⟨278,(11),[8,12],[10],1109⟩) from rfl))
private theorem rec13623 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(12),[8,12],[10],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[20]? = some (⟨278,(12),[8,12],[10],1113⟩) from rfl))
private theorem rec13626 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(13),[8,12],[10],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[23]? = some (⟨278,(13),[8,12],[10],1112⟩) from rfl))
private theorem rec13629 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(14),[8,12],[10],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[26]? = some (⟨278,(14),[8,12],[10],1113⟩) from rfl))
private theorem rec13632 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(15),[8,12],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[29]? = some (⟨278,(15),[8,12],[10],1108⟩) from rfl))
private theorem rec13635 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(16),[8,12],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[32]? = some (⟨278,(16),[8,12],[10],1109⟩) from rfl))
private theorem rec13638 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(17),[8,12],[10],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[35]? = some (⟨278,(17),[8,12],[10],1111⟩) from rfl))
private theorem rec13641 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(18),[8,12],[10],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[38]? = some (⟨278,(18),[8,12],[10],1112⟩) from rfl))
private theorem rec13644 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(19),[8,12],[10],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[41]? = some (⟨278,(19),[8,12],[10],1111⟩) from rfl))
private theorem rec13647 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(20),[8,12],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[44]? = some (⟨278,(20),[8,12],[10],1108⟩) from rfl))
private theorem rec13650 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(21),[8,12],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[47]? = some (⟨278,(21),[8,12],[10],1109⟩) from rfl))
private theorem rec13653 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(22),[8,12],[10],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[50]? = some (⟨278,(22),[8,12],[10],1114⟩) from rfl))
private theorem rec13656 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(23),[8,12],[10],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[53]? = some (⟨278,(23),[8,12],[10],1112⟩) from rfl))
private theorem rec13659 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 278 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(24),[8,12],[10],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[56]? = some (⟨278,(24),[8,12],[10],1114⟩) from rfl))
private theorem rec13662 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(0),[8,12],[10],1425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[59]? = some (⟨280,(0),[8,12],[10],1425⟩) from rfl))
private theorem rec13665 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(1),[8,12],[10],1425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[62]? = some (⟨280,(1),[8,12],[10],1425⟩) from rfl))
private theorem rec13668 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(2),[8,12],[10],1426⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[65]? = some (⟨280,(2),[8,12],[10],1426⟩) from rfl))
private theorem rec13671 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(3),[8,12],[10],1427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[68]? = some (⟨280,(3),[8,12],[10],1427⟩) from rfl))
private theorem rec13674 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(4),[8,12],[10],1428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[71]? = some (⟨280,(4),[8,12],[10],1428⟩) from rfl))
private theorem rec13677 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(5),[8,12],[10],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[74]? = some (⟨280,(5),[8,12],[10],1429⟩) from rfl))
private theorem rec13680 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(6),[8,12],[10],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[77]? = some (⟨280,(6),[8,12],[10],1429⟩) from rfl))
private theorem rec13683 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(7),[8,12],[10],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[80]? = some (⟨280,(7),[8,12],[10],1429⟩) from rfl))
private theorem rec13686 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(8),[8,12],[10],1427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[83]? = some (⟨280,(8),[8,12],[10],1427⟩) from rfl))
private theorem rec13689 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 280 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(9),[8,12],[10],1428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[86]? = some (⟨280,(9),[8,12],[10],1428⟩) from rfl))
private theorem rec13692 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(0),[8,12],[10],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[89]? = some (⟨283,(0),[8,12],[10],1120⟩) from rfl))
private theorem rec13695 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(1),[8,12],[10],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[92]? = some (⟨283,(1),[8,12],[10],1121⟩) from rfl))
private theorem rec13698 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(2),[8,12],[10],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[95]? = some (⟨283,(2),[8,12],[10],1122⟩) from rfl))
private theorem rec13701 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(3),[8,12],[10],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[98]? = some (⟨283,(3),[8,12],[10],1122⟩) from rfl))
private theorem rec13704 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(4),[8,12],[10],1123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[101]? = some (⟨283,(4),[8,12],[10],1123⟩) from rfl))
private theorem rec13707 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(5),[8,12],[10],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[104]? = some (⟨283,(5),[8,12],[10],1120⟩) from rfl))
private theorem rec13710 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(6),[8,12],[10],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[107]? = some (⟨283,(6),[8,12],[10],1121⟩) from rfl))
private theorem rec13713 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(7),[8,12],[10],1124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[110]? = some (⟨283,(7),[8,12],[10],1124⟩) from rfl))
private theorem rec13716 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(8),[8,12],[10],1125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[113]? = some (⟨283,(8),[8,12],[10],1125⟩) from rfl))
private theorem rec13719 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 283 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(9),[8,12],[10],1126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[116]? = some (⟨283,(9),[8,12],[10],1126⟩) from rfl))
private theorem rec13722 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(0),[8,12],[10],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[119]? = some (⟨285,(0),[8,12],[10],1430⟩) from rfl))
private theorem rec13725 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(1),[8,12],[10],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[122]? = some (⟨285,(1),[8,12],[10],1430⟩) from rfl))
private theorem rec13728 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(2),[8,12],[10],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[125]? = some (⟨285,(2),[8,12],[10],1431⟩) from rfl))
private theorem rec13731 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(3),[8,12],[10],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[128]? = some (⟨285,(3),[8,12],[10],1432⟩) from rfl))
private theorem rec13734 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(4),[8,12],[10],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[131]? = some (⟨285,(4),[8,12],[10],1433⟩) from rfl))
private theorem rec13737 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(5),[8,12],[10],1434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[134]? = some (⟨285,(5),[8,12],[10],1434⟩) from rfl))
private theorem rec13740 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(6),[8,12],[10],1434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[137]? = some (⟨285,(6),[8,12],[10],1434⟩) from rfl))
private theorem rec13743 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(7),[8,12],[10],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[140]? = some (⟨285,(7),[8,12],[10],1431⟩) from rfl))
private theorem rec13746 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(8),[8,12],[10],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[143]? = some (⟨285,(8),[8,12],[10],1432⟩) from rfl))
private theorem rec13749 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(9),[8,12],[10],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[146]? = some (⟨285,(9),[8,12],[10],1433⟩) from rfl))
private theorem rec13752 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(10),[8,12],[10],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[149]? = some (⟨285,(10),[8,12],[10],1430⟩) from rfl))
private theorem rec13755 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(11),[8,12],[10],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[152]? = some (⟨285,(11),[8,12],[10],1430⟩) from rfl))
private theorem rec13758 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(12),[8,12],[10],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[155]? = some (⟨285,(12),[8,12],[10],1431⟩) from rfl))
private theorem rec13761 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(13),[8,12],[10],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[158]? = some (⟨285,(13),[8,12],[10],1432⟩) from rfl))
private theorem rec13764 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(14),[8,12],[10],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[161]? = some (⟨285,(14),[8,12],[10],1433⟩) from rfl))
private theorem rec13767 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(15),[8,12],[10],1435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[164]? = some (⟨285,(15),[8,12],[10],1435⟩) from rfl))
private theorem rec13770 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(16),[8,12],[10],1435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[167]? = some (⟨285,(16),[8,12],[10],1435⟩) from rfl))
private theorem rec13773 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(17),[8,12],[10],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[170]? = some (⟨285,(17),[8,12],[10],1431⟩) from rfl))
private theorem rec13776 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(18),[8,12],[10],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[173]? = some (⟨285,(18),[8,12],[10],1432⟩) from rfl))
private theorem rec13779 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(19),[8,12],[10],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[176]? = some (⟨285,(19),[8,12],[10],1433⟩) from rfl))
private theorem rec13782 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(20),[8,12],[10],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[179]? = some (⟨285,(20),[8,12],[10],1436⟩) from rfl))
private theorem rec13785 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(21),[8,12],[10],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[182]? = some (⟨285,(21),[8,12],[10],1436⟩) from rfl))
private theorem rec13788 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(22),[8,12],[10],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[185]? = some (⟨285,(22),[8,12],[10],1436⟩) from rfl))
private theorem rec13791 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(23),[8,12],[10],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[188]? = some (⟨285,(23),[8,12],[10],1432⟩) from rfl))
private theorem rec13794 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 285 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(24),[8,12],[10],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[191]? = some (⟨285,(24),[8,12],[10],1433⟩) from rfl))
private theorem rec13797 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(0),[8,12],[10],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[194]? = some (⟨288,(0),[8,12],[10],1134⟩) from rfl))
private theorem rec13800 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(1),[8,12],[10],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[197]? = some (⟨288,(1),[8,12],[10],1135⟩) from rfl))
private theorem rec13803 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(2),[8,12],[10],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[200]? = some (⟨288,(2),[8,12],[10],1136⟩) from rfl))
private theorem rec13806 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(3),[8,12],[10],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[203]? = some (⟨288,(3),[8,12],[10],1136⟩) from rfl))
private theorem rec13809 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(4),[8,12],[10],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[206]? = some (⟨288,(4),[8,12],[10],1136⟩) from rfl))
private theorem rec13812 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(5),[8,12],[10],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[209]? = some (⟨288,(5),[8,12],[10],1134⟩) from rfl))
private theorem rec13815 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(6),[8,12],[10],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[212]? = some (⟨288,(6),[8,12],[10],1135⟩) from rfl))
private theorem rec13818 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(7),[8,12],[10],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[215]? = some (⟨288,(7),[8,12],[10],1137⟩) from rfl))
private theorem rec13821 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(8),[8,12],[10],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[218]? = some (⟨288,(8),[8,12],[10],1138⟩) from rfl))
private theorem rec13824 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(9),[8,12],[10],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[221]? = some (⟨288,(9),[8,12],[10],1137⟩) from rfl))
private theorem rec13827 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(10),[8,12],[10],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[224]? = some (⟨288,(10),[8,12],[10],1134⟩) from rfl))
private theorem rec13830 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(11),[8,12],[10],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[227]? = some (⟨288,(11),[8,12],[10],1135⟩) from rfl))
private theorem rec13833 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(12),[8,12],[10],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[230]? = some (⟨288,(12),[8,12],[10],1139⟩) from rfl))
private theorem rec13836 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(13),[8,12],[10],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[233]? = some (⟨288,(13),[8,12],[10],1138⟩) from rfl))
private theorem rec13839 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(14),[8,12],[10],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[236]? = some (⟨288,(14),[8,12],[10],1139⟩) from rfl))
private theorem rec13842 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(15),[8,12],[10],1140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[239]? = some (⟨288,(15),[8,12],[10],1140⟩) from rfl))
private theorem rec13845 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(16),[8,12],[10],1141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[242]? = some (⟨288,(16),[8,12],[10],1141⟩) from rfl))
private theorem rec13848 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(17),[8,12],[10],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[245]? = some (⟨288,(17),[8,12],[10],1142⟩) from rfl))
private theorem rec13851 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(18),[8,12],[10],1143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[248]? = some (⟨288,(18),[8,12],[10],1143⟩) from rfl))
private theorem rec13854 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(19),[8,12],[10],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[251]? = some (⟨288,(19),[8,12],[10],1142⟩) from rfl))
private theorem rec13857 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(20),[8,12],[10],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[254]? = some (⟨288,(20),[8,12],[10],1134⟩) from rfl))
private theorem rec13860 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(21),[8,12],[10],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[257]? = some (⟨288,(21),[8,12],[10],1135⟩) from rfl))
private theorem rec13863 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(22),[8,12],[10],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[260]? = some (⟨288,(22),[8,12],[10],1144⟩) from rfl))
private theorem rec13866 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(23),[8,12],[10],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[263]? = some (⟨288,(23),[8,12],[10],1138⟩) from rfl))
private theorem rec13869 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 288 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(24),[8,12],[10],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[266]? = some (⟨288,(24),[8,12],[10],1144⟩) from rfl))
private theorem rec13872 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(0),[8,12],[10],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[269]? = some (⟨290,(0),[8,12],[10],1437⟩) from rfl))
private theorem rec13875 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(1),[8,12],[10],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[272]? = some (⟨290,(1),[8,12],[10],1437⟩) from rfl))
private theorem rec13878 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(2),[8,12],[10],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[275]? = some (⟨290,(2),[8,12],[10],1438⟩) from rfl))
private theorem rec13881 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(3),[8,12],[10],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[278]? = some (⟨290,(3),[8,12],[10],1439⟩) from rfl))
private theorem rec13884 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(4),[8,12],[10],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[281]? = some (⟨290,(4),[8,12],[10],1440⟩) from rfl))
private theorem rec13887 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(5),[8,12],[10],1441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[284]? = some (⟨290,(5),[8,12],[10],1441⟩) from rfl))
private theorem rec13890 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(6),[8,12],[10],1441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[287]? = some (⟨290,(6),[8,12],[10],1441⟩) from rfl))
private theorem rec13893 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(7),[8,12],[10],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[290]? = some (⟨290,(7),[8,12],[10],1438⟩) from rfl))
private theorem rec13896 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(8),[8,12],[10],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[293]? = some (⟨290,(8),[8,12],[10],1439⟩) from rfl))
private theorem rec13899 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(9),[8,12],[10],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[296]? = some (⟨290,(9),[8,12],[10],1440⟩) from rfl))
private theorem rec13902 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(10),[8,12],[10],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[299]? = some (⟨290,(10),[8,12],[10],1437⟩) from rfl))
private theorem rec13905 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(11),[8,12],[10],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[302]? = some (⟨290,(11),[8,12],[10],1437⟩) from rfl))
private theorem rec13908 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(12),[8,12],[10],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[305]? = some (⟨290,(12),[8,12],[10],1438⟩) from rfl))
private theorem rec13911 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(13),[8,12],[10],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[308]? = some (⟨290,(13),[8,12],[10],1439⟩) from rfl))
private theorem rec13914 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(14),[8,12],[10],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[311]? = some (⟨290,(14),[8,12],[10],1440⟩) from rfl))
private theorem rec13917 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(15),[8,12],[10],1442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[314]? = some (⟨290,(15),[8,12],[10],1442⟩) from rfl))
private theorem rec13920 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(16),[8,12],[10],1442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[317]? = some (⟨290,(16),[8,12],[10],1442⟩) from rfl))
private theorem rec13923 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(17),[8,12],[10],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[320]? = some (⟨290,(17),[8,12],[10],1438⟩) from rfl))
private theorem rec13926 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(18),[8,12],[10],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[323]? = some (⟨290,(18),[8,12],[10],1439⟩) from rfl))
private theorem rec13929 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(19),[8,12],[10],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[326]? = some (⟨290,(19),[8,12],[10],1440⟩) from rfl))
private theorem rec13932 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(20),[8,12],[10],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[329]? = some (⟨290,(20),[8,12],[10],1443⟩) from rfl))
private theorem rec13935 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(21),[8,12],[10],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[332]? = some (⟨290,(21),[8,12],[10],1443⟩) from rfl))
private theorem rec13938 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(22),[8,12],[10],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[335]? = some (⟨290,(22),[8,12],[10],1443⟩) from rfl))
private theorem rec13941 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(23),[8,12],[10],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[338]? = some (⟨290,(23),[8,12],[10],1439⟩) from rfl))
private theorem rec13944 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 290 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(24),[8,12],[10],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[341]? = some (⟨290,(24),[8,12],[10],1440⟩) from rfl))
private theorem rec13947 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(0),[8,12],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[344]? = some (⟨293,(0),[8,12],[10],1152⟩) from rfl))
private theorem rec13950 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(1),[8,12],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[347]? = some (⟨293,(1),[8,12],[10],1153⟩) from rfl))
private theorem rec13953 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(2),[8,12],[10],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[350]? = some (⟨293,(2),[8,12],[10],1154⟩) from rfl))
private theorem rec13956 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(3),[8,12],[10],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[353]? = some (⟨293,(3),[8,12],[10],1154⟩) from rfl))
private theorem rec13959 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(4),[8,12],[10],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[356]? = some (⟨293,(4),[8,12],[10],1154⟩) from rfl))
private theorem rec13962 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(5),[8,12],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[359]? = some (⟨293,(5),[8,12],[10],1152⟩) from rfl))
private theorem rec13965 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(6),[8,12],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[362]? = some (⟨293,(6),[8,12],[10],1153⟩) from rfl))
private theorem rec13968 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(7),[8,12],[10],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[365]? = some (⟨293,(7),[8,12],[10],1155⟩) from rfl))
private theorem rec13971 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(8),[8,12],[10],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[368]? = some (⟨293,(8),[8,12],[10],1156⟩) from rfl))
private theorem rec13974 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(9),[8,12],[10],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[371]? = some (⟨293,(9),[8,12],[10],1155⟩) from rfl))
private theorem rec13977 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(10),[8,12],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[374]? = some (⟨293,(10),[8,12],[10],1152⟩) from rfl))
private theorem rec13980 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(11),[8,12],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[377]? = some (⟨293,(11),[8,12],[10],1153⟩) from rfl))
private theorem rec13983 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(12),[8,12],[10],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[380]? = some (⟨293,(12),[8,12],[10],1157⟩) from rfl))
private theorem rec13986 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(13),[8,12],[10],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[383]? = some (⟨293,(13),[8,12],[10],1156⟩) from rfl))
private theorem rec13989 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(14),[8,12],[10],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[386]? = some (⟨293,(14),[8,12],[10],1157⟩) from rfl))
private theorem rec13992 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(15),[8,12],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[389]? = some (⟨293,(15),[8,12],[10],1152⟩) from rfl))
private theorem rec13995 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(16),[8,12],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[392]? = some (⟨293,(16),[8,12],[10],1153⟩) from rfl))
private theorem rec13998 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(17),[8,12],[10],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[395]? = some (⟨293,(17),[8,12],[10],1155⟩) from rfl))
private theorem rec14001 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(18),[8,12],[10],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[398]? = some (⟨293,(18),[8,12],[10],1156⟩) from rfl))
private theorem rec14004 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(19),[8,12],[10],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[401]? = some (⟨293,(19),[8,12],[10],1155⟩) from rfl))
private theorem rec14007 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(20),[8,12],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[404]? = some (⟨293,(20),[8,12],[10],1152⟩) from rfl))
private theorem rec14010 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(21),[8,12],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[407]? = some (⟨293,(21),[8,12],[10],1153⟩) from rfl))
private theorem rec14013 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(22),[8,12],[10],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[410]? = some (⟨293,(22),[8,12],[10],1158⟩) from rfl))
private theorem rec14016 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(23),[8,12],[10],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[413]? = some (⟨293,(23),[8,12],[10],1156⟩) from rfl))
private theorem rec14019 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 293 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(24),[8,12],[10],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[416]? = some (⟨293,(24),[8,12],[10],1158⟩) from rfl))
private theorem rec14022 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(0),[8,12],[10],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[419]? = some (⟨295,(0),[8,12],[10],1444⟩) from rfl))
private theorem rec14025 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(1),[8,12],[10],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[422]? = some (⟨295,(1),[8,12],[10],1444⟩) from rfl))
private theorem rec14028 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(2),[8,12],[10],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[425]? = some (⟨295,(2),[8,12],[10],1445⟩) from rfl))
private theorem rec14031 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(3),[8,12],[10],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[428]? = some (⟨295,(3),[8,12],[10],1446⟩) from rfl))
private theorem rec14034 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(4),[8,12],[10],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[431]? = some (⟨295,(4),[8,12],[10],1447⟩) from rfl))
private theorem rec14037 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(5),[8,12],[10],1448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[434]? = some (⟨295,(5),[8,12],[10],1448⟩) from rfl))
private theorem rec14040 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(6),[8,12],[10],1448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[437]? = some (⟨295,(6),[8,12],[10],1448⟩) from rfl))
private theorem rec14043 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(7),[8,12],[10],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[440]? = some (⟨295,(7),[8,12],[10],1445⟩) from rfl))
private theorem rec14046 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(8),[8,12],[10],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[443]? = some (⟨295,(8),[8,12],[10],1446⟩) from rfl))
private theorem rec14049 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(9),[8,12],[10],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[446]? = some (⟨295,(9),[8,12],[10],1447⟩) from rfl))
private theorem rec14052 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(10),[8,12],[10],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[449]? = some (⟨295,(10),[8,12],[10],1444⟩) from rfl))
private theorem rec14055 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(11),[8,12],[10],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[452]? = some (⟨295,(11),[8,12],[10],1444⟩) from rfl))
private theorem rec14058 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(12),[8,12],[10],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[455]? = some (⟨295,(12),[8,12],[10],1445⟩) from rfl))
private theorem rec14061 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(13),[8,12],[10],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[458]? = some (⟨295,(13),[8,12],[10],1446⟩) from rfl))
private theorem rec14064 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(14),[8,12],[10],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[461]? = some (⟨295,(14),[8,12],[10],1447⟩) from rfl))
private theorem rec14067 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(15),[8,12],[10],1449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[464]? = some (⟨295,(15),[8,12],[10],1449⟩) from rfl))
private theorem rec14070 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(16),[8,12],[10],1449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[467]? = some (⟨295,(16),[8,12],[10],1449⟩) from rfl))
private theorem rec14073 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(17),[8,12],[10],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[470]? = some (⟨295,(17),[8,12],[10],1445⟩) from rfl))
private theorem rec14076 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(18),[8,12],[10],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[473]? = some (⟨295,(18),[8,12],[10],1446⟩) from rfl))
private theorem rec14079 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(19),[8,12],[10],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[476]? = some (⟨295,(19),[8,12],[10],1447⟩) from rfl))
private theorem rec14082 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(20),[8,12],[10],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[479]? = some (⟨295,(20),[8,12],[10],1450⟩) from rfl))
private theorem rec14085 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(21),[8,12],[10],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[482]? = some (⟨295,(21),[8,12],[10],1450⟩) from rfl))
private theorem rec14088 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(22),[8,12],[10],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[485]? = some (⟨295,(22),[8,12],[10],1450⟩) from rfl))
private theorem rec14091 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(23),[8,12],[10],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[488]? = some (⟨295,(23),[8,12],[10],1446⟩) from rfl))
private theorem rec14094 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 295 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(24),[8,12],[10],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[491]? = some (⟨295,(24),[8,12],[10],1447⟩) from rfl))
private theorem rec14097 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(0),[8,12],[10],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[494]? = some (⟨297,(0),[8,12],[10],1451⟩) from rfl))
private theorem rec14100 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(1),[8,12],[10],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[497]? = some (⟨297,(1),[8,12],[10],1452⟩) from rfl))
private theorem rec14103 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(2),[8,12],[10],1453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[500]? = some (⟨297,(2),[8,12],[10],1453⟩) from rfl))
private theorem rec14106 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(3),[8,12],[10],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[503]? = some (⟨297,(3),[8,12],[10],1454⟩) from rfl))
private theorem rec14109 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(4),[8,12],[10],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[506]? = some (⟨297,(4),[8,12],[10],1451⟩) from rfl))
private theorem rec14112 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(5),[8,12],[10],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[509]? = some (⟨297,(5),[8,12],[10],1452⟩) from rfl))
private theorem rec14115 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(6),[8,12],[10],1455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[512]? = some (⟨297,(6),[8,12],[10],1455⟩) from rfl))
private theorem rec14118 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(7),[8,12],[10],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[515]? = some (⟨297,(7),[8,12],[10],1454⟩) from rfl))
private theorem rec14121 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(8),[8,12],[10],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[518]? = some (⟨297,(8),[8,12],[10],1451⟩) from rfl))
private theorem rec14124 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(9),[8,12],[10],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[521]? = some (⟨297,(9),[8,12],[10],1452⟩) from rfl))
private theorem rec14127 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(10),[8,12],[10],1453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[524]? = some (⟨297,(10),[8,12],[10],1453⟩) from rfl))
private theorem rec14130 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(11),[8,12],[10],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[527]? = some (⟨297,(11),[8,12],[10],1454⟩) from rfl))
private theorem rec14133 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(12),[8,12],[10],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[530]? = some (⟨297,(12),[8,12],[10],1451⟩) from rfl))
private theorem rec14136 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(13),[8,12],[10],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[533]? = some (⟨297,(13),[8,12],[10],1452⟩) from rfl))
private theorem rec14139 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(14),[8,12],[10],1456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[536]? = some (⟨297,(14),[8,12],[10],1456⟩) from rfl))
private theorem rec14142 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 297 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(15),[8,12],[10],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[539]? = some (⟨297,(15),[8,12],[10],1454⟩) from rfl))
private theorem rec14145 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(0),[8,12],[10],1457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[542]? = some (⟨300,(0),[8,12],[10],1457⟩) from rfl))
private theorem rec14148 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(1),[8,12],[10],1458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[545]? = some (⟨300,(1),[8,12],[10],1458⟩) from rfl))
private theorem rec14151 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(2),[8,12],[10],1457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[548]? = some (⟨300,(2),[8,12],[10],1457⟩) from rfl))
private theorem rec14154 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(3),[8,12],[10],1459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[551]? = some (⟨300,(3),[8,12],[10],1459⟩) from rfl))
private theorem rec14157 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(4),[8,12],[10],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[554]? = some (⟨300,(4),[8,12],[10],1460⟩) from rfl))
private theorem rec14160 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(5),[8,12],[10],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[557]? = some (⟨300,(5),[8,12],[10],1460⟩) from rfl))
private theorem rec14163 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(6),[8,12],[10],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[560]? = some (⟨300,(6),[8,12],[10],1460⟩) from rfl))
private theorem rec14166 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(7),[8,12],[10],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[563]? = some (⟨300,(7),[8,12],[10],1460⟩) from rfl))
private theorem rec14169 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(8),[8,12],[10],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[566]? = some (⟨300,(8),[8,12],[10],1461⟩) from rfl))
private theorem rec14172 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(9),[8,12],[10],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[569]? = some (⟨300,(9),[8,12],[10],1461⟩) from rfl))
private theorem rec14175 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(10),[8,12],[10],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[572]? = some (⟨300,(10),[8,12],[10],1461⟩) from rfl))
private theorem rec14178 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(11),[8,12],[10],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[575]? = some (⟨300,(11),[8,12],[10],1461⟩) from rfl))
private theorem rec14181 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(12),[8,12],[10],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[578]? = some (⟨300,(12),[8,12],[10],1462⟩) from rfl))
private theorem rec14184 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(13),[8,12],[10],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[581]? = some (⟨300,(13),[8,12],[10],1462⟩) from rfl))
private theorem rec14187 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(14),[8,12],[10],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[584]? = some (⟨300,(14),[8,12],[10],1462⟩) from rfl))
private theorem rec14190 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 300 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(15),[8,12],[10],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[587]? = some (⟨300,(15),[8,12],[10],1462⟩) from rfl))
private theorem rec14193 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(0),[8,12],[10],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[590]? = some (⟨302,(0),[8,12],[10],1463⟩) from rfl))
private theorem rec14196 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(1),[8,12],[10],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[593]? = some (⟨302,(1),[8,12],[10],1464⟩) from rfl))
private theorem rec14199 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(2),[8,12],[10],1465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[596]? = some (⟨302,(2),[8,12],[10],1465⟩) from rfl))
private theorem rec14202 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(3),[8,12],[10],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[599]? = some (⟨302,(3),[8,12],[10],1466⟩) from rfl))
private theorem rec14205 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(4),[8,12],[10],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[602]? = some (⟨302,(4),[8,12],[10],1463⟩) from rfl))
private theorem rec14208 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(5),[8,12],[10],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[605]? = some (⟨302,(5),[8,12],[10],1464⟩) from rfl))
private theorem rec14211 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(6),[8,12],[10],1467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[608]? = some (⟨302,(6),[8,12],[10],1467⟩) from rfl))
private theorem rec14214 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(7),[8,12],[10],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[611]? = some (⟨302,(7),[8,12],[10],1466⟩) from rfl))
private theorem rec14217 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(8),[8,12],[10],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[614]? = some (⟨302,(8),[8,12],[10],1463⟩) from rfl))
private theorem rec14220 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(9),[8,12],[10],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[617]? = some (⟨302,(9),[8,12],[10],1464⟩) from rfl))
private theorem rec14223 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(10),[8,12],[10],1465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[620]? = some (⟨302,(10),[8,12],[10],1465⟩) from rfl))
private theorem rec14226 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(11),[8,12],[10],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[623]? = some (⟨302,(11),[8,12],[10],1466⟩) from rfl))
private theorem rec14229 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(12),[8,12],[10],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[626]? = some (⟨302,(12),[8,12],[10],1463⟩) from rfl))
private theorem rec14232 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(13),[8,12],[10],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[629]? = some (⟨302,(13),[8,12],[10],1464⟩) from rfl))
private theorem rec14235 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(14),[8,12],[10],1468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[632]? = some (⟨302,(14),[8,12],[10],1468⟩) from rfl))
private theorem rec14238 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 302 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(15),[8,12],[10],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[635]? = some (⟨302,(15),[8,12],[10],1466⟩) from rfl))
private theorem rec14241 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 305 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(0),[8,12],[10],1469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[638]? = some (⟨305,(0),[8,12],[10],1469⟩) from rfl))
private theorem rec14244 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 305 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(1),[8,12],[10],1470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[641]? = some (⟨305,(1),[8,12],[10],1470⟩) from rfl))
private theorem rec14247 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 305 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(2),[8,12],[10],1471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[644]? = some (⟨305,(2),[8,12],[10],1471⟩) from rfl))
private theorem rec14250 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 305 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(3),[8,12],[10],1472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[647]? = some (⟨305,(3),[8,12],[10],1472⟩) from rfl))
private theorem rec14253 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(0),[8,12],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[650]? = some (⟨307,(0),[8,12],[10],1266⟩) from rfl))
private theorem rec14256 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(1),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[653]? = some (⟨307,(1),[8,12],[10],3⟩) from rfl))
private theorem rec14259 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(2),[8,12],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[656]? = some (⟨307,(2),[8,12],[10],1266⟩) from rfl))
private theorem rec14262 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(3),[8,12],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[659]? = some (⟨307,(3),[8,12],[10],29⟩) from rfl))
private theorem rec14265 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(4),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[662]? = some (⟨307,(4),[8,12],[10],3⟩) from rfl))
private theorem rec14268 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(5),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[665]? = some (⟨307,(5),[8,12],[10],3⟩) from rfl))
private theorem rec14271 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(6),[8,12],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[668]? = some (⟨307,(6),[8,12],[10],1266⟩) from rfl))
private theorem rec14274 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(7),[8,12],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[671]? = some (⟨307,(7),[8,12],[10],29⟩) from rfl))
private theorem rec14277 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(8),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[674]? = some (⟨307,(8),[8,12],[10],3⟩) from rfl))
private theorem rec14280 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(9),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[677]? = some (⟨307,(9),[8,12],[10],3⟩) from rfl))
private theorem rec14283 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(10),[8,12],[10],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[680]? = some (⟨307,(10),[8,12],[10],512⟩) from rfl))
private theorem rec14286 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(11),[8,12],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[683]? = some (⟨307,(11),[8,12],[10],29⟩) from rfl))
private theorem rec14289 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(12),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[686]? = some (⟨307,(12),[8,12],[10],3⟩) from rfl))
private theorem rec14292 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(13),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[689]? = some (⟨307,(13),[8,12],[10],3⟩) from rfl))
private theorem rec14295 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(14),[8,12],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[692]? = some (⟨307,(14),[8,12],[10],1266⟩) from rfl))
private theorem rec14298 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(15),[8,12],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[695]? = some (⟨307,(15),[8,12],[10],29⟩) from rfl))
private theorem rec14301 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(16),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[698]? = some (⟨307,(16),[8,12],[10],3⟩) from rfl))
private theorem rec14304 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(17),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[701]? = some (⟨307,(17),[8,12],[10],3⟩) from rfl))
private theorem rec14307 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(18),[8,12],[10],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[704]? = some (⟨307,(18),[8,12],[10],514⟩) from rfl))
private theorem rec14310 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 307 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(19),[8,12],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[707]? = some (⟨307,(19),[8,12],[10],29⟩) from rfl))
private theorem rec14313 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 308 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(8),[8,12],[10],1474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[710]? = some (⟨308,(8),[8,12],[10],1474⟩) from rfl))
private theorem rec14316 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 308 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(9),[8,12],[10],1475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[713]? = some (⟨308,(9),[8,12],[10],1475⟩) from rfl))
private theorem rec14319 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 308 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(10),[8,12],[10],1474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[716]? = some (⟨308,(10),[8,12],[10],1474⟩) from rfl))
private theorem rec14322 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 308 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(11),[8,12],[10],1476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[719]? = some (⟨308,(11),[8,12],[10],1476⟩) from rfl))
private theorem rec14325 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 309 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(0),[8,12],[10],1188⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[722]? = some (⟨309,(0),[8,12],[10],1188⟩) from rfl))
private theorem rec14328 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 309 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(1),[8,12],[10],1189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[725]? = some (⟨309,(1),[8,12],[10],1189⟩) from rfl))
private theorem rec14331 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 309 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(2),[8,12],[10],1190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[728]? = some (⟨309,(2),[8,12],[10],1190⟩) from rfl))
private theorem rec14334 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 309 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(3),[8,12],[10],1191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[731]? = some (⟨309,(3),[8,12],[10],1191⟩) from rfl))
private theorem rec14337 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 309 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(4),[8,12],[10],1192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[734]? = some (⟨309,(4),[8,12],[10],1192⟩) from rfl))
private theorem rec14340 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 311 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(0),[8,12],[10],1478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[737]? = some (⟨311,(0),[8,12],[10],1478⟩) from rfl))
private theorem rec14343 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 311 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(1),[8,12],[10],1479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[740]? = some (⟨311,(1),[8,12],[10],1479⟩) from rfl))
private theorem rec14346 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 311 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(2),[8,12],[10],1480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[743]? = some (⟨311,(2),[8,12],[10],1480⟩) from rfl))
private theorem rec14349 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 311 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(3),[8,12],[10],1481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[746]? = some (⟨311,(3),[8,12],[10],1481⟩) from rfl))
private theorem rec14352 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 312 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(0),[8,12],[10],1482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[749]? = some (⟨312,(0),[8,12],[10],1482⟩) from rfl))
private theorem rec14355 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 312 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(1),[8,12],[10],1483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[752]? = some (⟨312,(1),[8,12],[10],1483⟩) from rfl))
private theorem rec14358 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 312 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(2),[8,12],[10],1482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[755]? = some (⟨312,(2),[8,12],[10],1482⟩) from rfl))
private theorem rec14361 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 312 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(3),[8,12],[10],1484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[758]? = some (⟨312,(3),[8,12],[10],1484⟩) from rfl))
private theorem rec14364 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 313 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(0),[8,12],[10],1200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[761]? = some (⟨313,(0),[8,12],[10],1200⟩) from rfl))
private theorem rec14367 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 313 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(1),[8,12],[10],1201⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[764]? = some (⟨313,(1),[8,12],[10],1201⟩) from rfl))
private theorem rec14370 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 313 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(2),[8,12],[10],1202⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[767]? = some (⟨313,(2),[8,12],[10],1202⟩) from rfl))
private theorem rec14373 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 313 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(3),[8],[10],1203⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[770]? = some (⟨313,(3),[8],[10],1203⟩) from rfl))
private theorem rec14377 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(0),[8,12],[10],1485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[774]? = some (⟨315,(0),[8,12],[10],1485⟩) from rfl))
private theorem rec14380 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(1),[8,12],[10],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[777]? = some (⟨315,(1),[8,12],[10],1486⟩) from rfl))
private theorem rec14383 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(2),[8,12],[10],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[780]? = some (⟨315,(2),[8,12],[10],1487⟩) from rfl))
private theorem rec14386 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(3),[8,12],[10],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[783]? = some (⟨315,(3),[8,12],[10],1488⟩) from rfl))
private theorem rec14389 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(4),[8,12],[10],1489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[786]? = some (⟨315,(4),[8,12],[10],1489⟩) from rfl))
private theorem rec14392 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(5),[8,12],[10],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[789]? = some (⟨315,(5),[8,12],[10],1486⟩) from rfl))
private theorem rec14395 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(6),[8,12],[10],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[792]? = some (⟨315,(6),[8,12],[10],1487⟩) from rfl))
private theorem rec14398 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(7),[8,12],[10],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[795]? = some (⟨315,(7),[8,12],[10],1488⟩) from rfl))
private theorem rec14401 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(8),[8,12],[10],1485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[798]? = some (⟨315,(8),[8,12],[10],1485⟩) from rfl))
private theorem rec14404 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(9),[8,12],[10],1490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[801]? = some (⟨315,(9),[8,12],[10],1490⟩) from rfl))
private theorem rec14407 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(10),[8,12],[10],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[804]? = some (⟨315,(10),[8,12],[10],1487⟩) from rfl))
private theorem rec14410 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(11),[8,12],[10],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[807]? = some (⟨315,(11),[8,12],[10],1488⟩) from rfl))
private theorem rec14413 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(12),[8,12],[10],1491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[810]? = some (⟨315,(12),[8,12],[10],1491⟩) from rfl))
private theorem rec14416 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(13),[8,12],[10],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[813]? = some (⟨315,(13),[8,12],[10],1486⟩) from rfl))
private theorem rec14419 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(14),[8,12],[10],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[816]? = some (⟨315,(14),[8,12],[10],1487⟩) from rfl))
private theorem rec14422 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 315 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(15),[8,12],[10],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[819]? = some (⟨315,(15),[8,12],[10],1488⟩) from rfl))
private theorem rec14425 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(0),[8,12],[10],1211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[822]? = some (⟨317,(0),[8,12],[10],1211⟩) from rfl))
private theorem rec14428 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(1),[8,12],[10],1212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[825]? = some (⟨317,(1),[8,12],[10],1212⟩) from rfl))
private theorem rec14431 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(2),[8,12],[10],1213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[828]? = some (⟨317,(2),[8,12],[10],1213⟩) from rfl))
private theorem rec14434 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(3),[8,12],[10],1214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[831]? = some (⟨317,(3),[8,12],[10],1214⟩) from rfl))
private theorem rec14437 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(4),[8,12],[10],1215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[834]? = some (⟨317,(4),[8,12],[10],1215⟩) from rfl))
private theorem rec14440 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(5),[8,12],[10],1216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[837]? = some (⟨317,(5),[8,12],[10],1216⟩) from rfl))
private theorem rec14443 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(6),[8,12],[10],1217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[840]? = some (⟨317,(6),[8,12],[10],1217⟩) from rfl))
private theorem rec14446 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(7),[8,12],[10],1218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[843]? = some (⟨317,(7),[8,12],[10],1218⟩) from rfl))
private theorem rec14449 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(8),[8,12],[10],1492⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[846]? = some (⟨317,(8),[8,12],[10],1492⟩) from rfl))
private theorem rec14452 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(9),[8,12],[10],1493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[849]? = some (⟨317,(9),[8,12],[10],1493⟩) from rfl))
private theorem rec14455 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(10),[8,12],[10],1494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[852]? = some (⟨317,(10),[8,12],[10],1494⟩) from rfl))
private theorem rec14458 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(11),[8,12],[10],1495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[855]? = some (⟨317,(11),[8,12],[10],1495⟩) from rfl))
private theorem rec14461 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(12),[8,12],[10],1496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[858]? = some (⟨317,(12),[8,12],[10],1496⟩) from rfl))
private theorem rec14464 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(13),[8,12],[10],1493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[861]? = some (⟨317,(13),[8,12],[10],1493⟩) from rfl))
private theorem rec14467 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(14),[8,12],[10],1494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[864]? = some (⟨317,(14),[8,12],[10],1494⟩) from rfl))
private theorem rec14470 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 317 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(15),[8,12],[10],1495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[867]? = some (⟨317,(15),[8,12],[10],1495⟩) from rfl))
private theorem rec14473 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(0),[8,12],[10],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[870]? = some (⟨318,(0),[8,12],[10],882⟩) from rfl))
private theorem rec14476 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(1),[8,12],[10],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[873]? = some (⟨318,(1),[8,12],[10],1497⟩) from rfl))
private theorem rec14479 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(2),[8,12],[10],1498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[876]? = some (⟨318,(2),[8,12],[10],1498⟩) from rfl))
private theorem rec14482 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(3),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[879]? = some (⟨318,(3),[8,12],[10],101⟩) from rfl))
private theorem rec14485 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(4),[8,12],[10],1498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[882]? = some (⟨318,(4),[8,12],[10],1498⟩) from rfl))
private theorem rec14488 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(5),[8,12],[10],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[885]? = some (⟨318,(5),[8,12],[10],882⟩) from rfl))
private theorem rec14491 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(6),[8,12],[10],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[888]? = some (⟨318,(6),[8,12],[10],1497⟩) from rfl))
private theorem rec14494 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(7),[8,12],[10],1499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[891]? = some (⟨318,(7),[8,12],[10],1499⟩) from rfl))
private theorem rec14497 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(8),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[894]? = some (⟨318,(8),[8,12],[10],101⟩) from rfl))
private theorem rec14500 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(9),[8,12],[10],1499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[897]? = some (⟨318,(9),[8,12],[10],1499⟩) from rfl))
private theorem rec14503 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(10),[8,12],[10],1500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[900]? = some (⟨318,(10),[8,12],[10],1500⟩) from rfl))
private theorem rec14506 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(11),[8,12],[10],1501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[903]? = some (⟨318,(11),[8,12],[10],1501⟩) from rfl))
private theorem rec14509 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(12),[8,12],[10],1502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[906]? = some (⟨318,(12),[8,12],[10],1502⟩) from rfl))
private theorem rec14512 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(13),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[909]? = some (⟨318,(13),[8,12],[10],101⟩) from rfl))
private theorem rec14515 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(14),[8,12],[10],1502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[912]? = some (⟨318,(14),[8,12],[10],1502⟩) from rfl))
private theorem rec14518 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(15),[8,12],[10],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[915]? = some (⟨318,(15),[8,12],[10],882⟩) from rfl))
private theorem rec14521 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(16),[8,12],[10],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[918]? = some (⟨318,(16),[8,12],[10],1497⟩) from rfl))
private theorem rec14524 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(17),[8,12],[10],1503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[921]? = some (⟨318,(17),[8,12],[10],1503⟩) from rfl))
private theorem rec14527 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(18),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[924]? = some (⟨318,(18),[8,12],[10],101⟩) from rfl))
private theorem rec14530 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 318 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(19),[8,12],[10],1503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[927]? = some (⟨318,(19),[8,12],[10],1503⟩) from rfl))
private theorem rec14533 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(0),[8,12],[10],1231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[930]? = some (⟨319,(0),[8,12],[10],1231⟩) from rfl))
private theorem rec14536 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(1),[8,12],[10],1229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[933]? = some (⟨319,(1),[8,12],[10],1229⟩) from rfl))
private theorem rec14539 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(2),[8,12],[10],1228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[936]? = some (⟨319,(2),[8,12],[10],1228⟩) from rfl))
private theorem rec14542 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(3),[8,12],[10],1230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[939]? = some (⟨319,(3),[8,12],[10],1230⟩) from rfl))
private theorem rec14545 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(4),[8,12],[10],1231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[942]? = some (⟨319,(4),[8,12],[10],1231⟩) from rfl))
private theorem rec14548 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(5),[8,12],[10],1232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[945]? = some (⟨319,(5),[8,12],[10],1232⟩) from rfl))
private theorem rec14551 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(6),[8,12],[10],1504⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[948]? = some (⟨319,(6),[8,12],[10],1504⟩) from rfl))
private theorem rec14554 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(7),[8,12],[10],1505⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[951]? = some (⟨319,(7),[8,12],[10],1505⟩) from rfl))
private theorem rec14557 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(8),[8,12],[10],1235⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[954]? = some (⟨319,(8),[8,12],[10],1235⟩) from rfl))
private theorem rec14560 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(9),[8,12],[10],1236⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[957]? = some (⟨319,(9),[8,12],[10],1236⟩) from rfl))
private theorem rec14563 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(10),[8,12],[10],1506⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[960]? = some (⟨319,(10),[8,12],[10],1506⟩) from rfl))
private theorem rec14566 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(11),[8,12],[10],1507⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[963]? = some (⟨319,(11),[8,12],[10],1507⟩) from rfl))
private theorem rec14569 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(12),[8,12],[10],1239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[966]? = some (⟨319,(12),[8,12],[10],1239⟩) from rfl))
private theorem rec14572 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(13),[8,12],[10],1240⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[969]? = some (⟨319,(13),[8,12],[10],1240⟩) from rfl))
private theorem rec14575 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(14),[8,12],[10],1508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[972]? = some (⟨319,(14),[8,12],[10],1508⟩) from rfl))
private theorem rec14578 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(15),[8,12],[10],1508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[975]? = some (⟨319,(15),[8,12],[10],1508⟩) from rfl))
private theorem rec14581 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(16),[8,12],[10],1242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[978]? = some (⟨319,(16),[8,12],[10],1242⟩) from rfl))
private theorem rec14584 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(17),[8,12],[10],1243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[981]? = some (⟨319,(17),[8,12],[10],1243⟩) from rfl))
private theorem rec14587 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(18),[8,12],[10],1509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[984]? = some (⟨319,(18),[8,12],[10],1509⟩) from rfl))
private theorem rec14590 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 319 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(19),[8,12],[10],1509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[987]? = some (⟨319,(19),[8,12],[10],1509⟩) from rfl))
private theorem rec14593 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(0),[8,12],[10],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[990]? = some (⟨321,(0),[8,12],[10],882⟩) from rfl))
private theorem rec14596 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(1),[8,12],[10],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[993]? = some (⟨321,(1),[8,12],[10],1497⟩) from rfl))
private theorem rec14599 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(2),[8,12],[10],1245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[996]? = some (⟨321,(2),[8,12],[10],1245⟩) from rfl))
private theorem rec14602 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(3),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[999]? = some (⟨321,(3),[8,12],[10],101⟩) from rfl))
private theorem rec14605 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(4),[8,12],[10],1245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1002]? = some (⟨321,(4),[8,12],[10],1245⟩) from rfl))
private theorem rec14608 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(5),[8,12],[10],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1005]? = some (⟨321,(5),[8,12],[10],882⟩) from rfl))
private theorem rec14611 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(6),[8,12],[10],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1008]? = some (⟨321,(6),[8,12],[10],1497⟩) from rfl))
private theorem rec14614 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(7),[8,12],[10],1510⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1011]? = some (⟨321,(7),[8,12],[10],1510⟩) from rfl))
private theorem rec14617 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(8),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1014]? = some (⟨321,(8),[8,12],[10],101⟩) from rfl))
private theorem rec14620 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(9),[8,12],[10],1510⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1017]? = some (⟨321,(9),[8,12],[10],1510⟩) from rfl))
private theorem rec14623 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(10),[8,12],[10],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1020]? = some (⟨321,(10),[8,12],[10],882⟩) from rfl))
private theorem rec14626 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(11),[8,12],[10],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1023]? = some (⟨321,(11),[8,12],[10],1497⟩) from rfl))
private theorem rec14629 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(12),[8,12],[10],1511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1026]? = some (⟨321,(12),[8,12],[10],1511⟩) from rfl))
private theorem rec14632 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(13),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1029]? = some (⟨321,(13),[8,12],[10],101⟩) from rfl))
private theorem rec14635 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(14),[8,12],[10],1511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1032]? = some (⟨321,(14),[8,12],[10],1511⟩) from rfl))
private theorem rec14638 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(15),[8,12],[10],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1035]? = some (⟨321,(15),[8,12],[10],625⟩) from rfl))
private theorem rec14641 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(16),[8,12],[10],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1038]? = some (⟨321,(16),[8,12],[10],626⟩) from rfl))
private theorem rec14644 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(17),[8,12],[10],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1041]? = some (⟨321,(17),[8,12],[10],286⟩) from rfl))
private theorem rec14647 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(18),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1044]? = some (⟨321,(18),[8,12],[10],101⟩) from rfl))
private theorem rec14650 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(19),[8,12],[10],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1047]? = some (⟨321,(19),[8,12],[10],286⟩) from rfl))
private theorem rec14653 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(20),[8,12],[10],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1050]? = some (⟨321,(20),[8,12],[10],882⟩) from rfl))
private theorem rec14656 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(21),[8,12],[10],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1053]? = some (⟨321,(21),[8,12],[10],1497⟩) from rfl))
private theorem rec14659 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(22),[8,12],[10],1512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1056]? = some (⟨321,(22),[8,12],[10],1512⟩) from rfl))
private theorem rec14662 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(23),[8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1059]? = some (⟨321,(23),[8,12],[10],101⟩) from rfl))
private theorem rec14665 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 321 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(24),[8,12],[10],1512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1062]? = some (⟨321,(24),[8,12],[10],1512⟩) from rfl))
private theorem rec16194 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(0),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1273]? = some (⟨532,(0),[8,12],[10],3⟩) from rfl))
private theorem rec16195 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(1),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1274]? = some (⟨532,(1),[8,12],[10],3⟩) from rfl))
private theorem rec16196 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(2),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1275]? = some (⟨532,(2),[8,12],[10],3⟩) from rfl))
private theorem rec16197 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(3),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1276]? = some (⟨532,(3),[8,12],[10],3⟩) from rfl))
private theorem rec16198 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(4),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1277]? = some (⟨532,(4),[8,12],[10],3⟩) from rfl))
private theorem rec16199 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(5),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1278]? = some (⟨532,(5),[8,12],[10],3⟩) from rfl))
private theorem rec16200 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(6),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1279]? = some (⟨532,(6),[8,12],[10],3⟩) from rfl))
private theorem rec16201 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(7),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1280]? = some (⟨532,(7),[8,12],[10],3⟩) from rfl))
private theorem rec16202 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(8),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1281]? = some (⟨532,(8),[8,12],[10],3⟩) from rfl))
private theorem rec16203 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 532 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨532,(9),[8,12],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1282]? = some (⟨532,(9),[8,12],[10],3⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 8).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 8)).drop 0).take 16, section14Recorded section14Catalog 8 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 8 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 8).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(531,⟨([1],[]),true,([1],[]),false,false,[]⟩),(532,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(533,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(534,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(535,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec13298 8 0 (by decide) (by decide)
  · left
    exact rec13304 8 1 (by decide) (by decide)
  · left
    exact rec13305 8 2 (by decide) (by decide)
  · left
    exact rec13313 8 3 (by decide) (by decide)
  · left
    exact rec13298 8 4 (by decide) (by decide)
  · left
    exact rec13304 8 5 (by decide) (by decide)
  · left
    exact rec13307 8 6 (by decide) (by decide)
  · left
    exact rec13306 8 7 (by decide) (by decide)
  · left
    exact rec13303 8 8 (by decide) (by decide)
  · left
    exact rec13304 8 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(531,⟨([1],[]),true,([1],[]),false,false,[]⟩),(532,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(533,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(534,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(535,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 531)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 532)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16194 8 10 (by decide) (by decide)
      · right
        exact rec16195 8 10 (by decide) (by decide)
      · right
        exact rec16196 8 10 (by decide) (by decide)
      · right
        exact rec16197 8 10 (by decide) (by decide)
      · right
        exact rec16198 8 10 (by decide) (by decide)
      · right
        exact rec16199 8 10 (by decide) (by decide)
      · right
        exact rec16200 8 10 (by decide) (by decide)
      · right
        exact rec16201 8 10 (by decide) (by decide)
      · right
        exact rec16202 8 10 (by decide) (by decide)
      · right
        exact rec16203 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 533)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 264)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13381 8 10 (by decide) (by decide)
      · right
        exact rec13383 8 10 (by decide) (by decide)
      · right
        exact rec13385 8 10 (by decide) (by decide)
      · right
        exact rec13387 8 10 (by decide) (by decide)
      · right
        exact rec13389 8 10 (by decide) (by decide)
      · right
        exact rec13391 8 10 (by decide) (by decide)
      · right
        exact rec13393 8 10 (by decide) (by decide)
      · right
        exact rec13395 8 10 (by decide) (by decide)
      · right
        exact rec13397 8 10 (by decide) (by decide)
      · right
        exact rec13399 8 10 (by decide) (by decide)
      · right
        exact rec13401 8 10 (by decide) (by decide)
      · right
        exact rec13403 8 10 (by decide) (by decide)
      · right
        exact rec13405 8 10 (by decide) (by decide)
      · right
        exact rec13407 8 10 (by decide) (by decide)
      · right
        exact rec13409 8 10 (by decide) (by decide)
      · right
        exact rec13411 8 10 (by decide) (by decide)
      · right
        exact rec13413 8 10 (by decide) (by decide)
      · right
        exact rec13415 8 10 (by decide) (by decide)
      · right
        exact rec13417 8 10 (by decide) (by decide)
      · right
        exact rec13419 8 10 (by decide) (by decide)
      · right
        exact rec13421 8 10 (by decide) (by decide)
      · right
        exact rec13423 8 10 (by decide) (by decide)
      · right
        exact rec13425 8 10 (by decide) (by decide)
      · right
        exact rec13427 8 10 (by decide) (by decide)
      · right
        exact rec13429 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 265)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 266)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 267)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13431 8 10 (by decide) (by decide)
      · right
        exact rec13434 8 10 (by decide) (by decide)
      · right
        exact rec13437 8 10 (by decide) (by decide)
      · right
        exact rec13440 8 10 (by decide) (by decide)
      · right
        exact rec13443 8 10 (by decide) (by decide)
      · right
        exact rec13446 8 10 (by decide) (by decide)
      · right
        exact rec13449 8 10 (by decide) (by decide)
      · right
        exact rec13452 8 10 (by decide) (by decide)
      · right
        exact rec13455 8 10 (by decide) (by decide)
      · right
        exact rec13458 8 10 (by decide) (by decide)
      · right
        exact rec13461 8 10 (by decide) (by decide)
      · right
        exact rec13464 8 10 (by decide) (by decide)
      · right
        exact rec13467 8 10 (by decide) (by decide)
      · right
        exact rec13470 8 10 (by decide) (by decide)
      · right
        exact rec13473 8 10 (by decide) (by decide)
      · right
        exact rec13476 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 268)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 269)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 270)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13479 8 10 (by decide) (by decide)
      · right
        exact rec13482 8 10 (by decide) (by decide)
      · right
        exact rec13485 8 10 (by decide) (by decide)
      · right
        exact rec13488 8 10 (by decide) (by decide)
      · right
        exact rec13491 8 10 (by decide) (by decide)
      · right
        exact rec13494 8 10 (by decide) (by decide)
      · right
        exact rec13497 8 10 (by decide) (by decide)
      · right
        exact rec13500 8 10 (by decide) (by decide)
      · right
        exact rec13503 8 10 (by decide) (by decide)
      · right
        exact rec13506 8 10 (by decide) (by decide)
      · right
        exact rec13509 8 10 (by decide) (by decide)
      · right
        exact rec13512 8 10 (by decide) (by decide)
      · right
        exact rec13515 8 10 (by decide) (by decide)
      · right
        exact rec13518 8 10 (by decide) (by decide)
      · right
        exact rec13521 8 10 (by decide) (by decide)
      · right
        exact rec13524 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 271)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 272)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 273)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13527 8 10 (by decide) (by decide)
      · right
        exact rec13530 8 10 (by decide) (by decide)
      · right
        exact rec13533 8 10 (by decide) (by decide)
      · right
        exact rec13536 8 10 (by decide) (by decide)
      · right
        exact rec13539 8 10 (by decide) (by decide)
      · right
        exact rec13542 8 10 (by decide) (by decide)
      · right
        exact rec13545 8 10 (by decide) (by decide)
      · right
        exact rec13548 8 10 (by decide) (by decide)
      · right
        exact rec13551 8 10 (by decide) (by decide)
      · right
        exact rec13554 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 274)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 275)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13557 8 10 (by decide) (by decide)
      · right
        exact rec13560 8 10 (by decide) (by decide)
      · right
        exact rec13563 8 10 (by decide) (by decide)
      · right
        exact rec13566 8 10 (by decide) (by decide)
      · right
        exact rec13569 8 10 (by decide) (by decide)
      · right
        exact rec13572 8 10 (by decide) (by decide)
      · right
        exact rec13575 8 10 (by decide) (by decide)
      · right
        exact rec13578 8 10 (by decide) (by decide)
      · right
        exact rec13581 8 10 (by decide) (by decide)
      · right
        exact rec13584 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 276)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 277)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 278)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13587 8 10 (by decide) (by decide)
      · right
        exact rec13590 8 10 (by decide) (by decide)
      · right
        exact rec13593 8 10 (by decide) (by decide)
      · right
        exact rec13596 8 10 (by decide) (by decide)
      · right
        exact rec13599 8 10 (by decide) (by decide)
      · right
        exact rec13602 8 10 (by decide) (by decide)
      · right
        exact rec13605 8 10 (by decide) (by decide)
      · right
        exact rec13608 8 10 (by decide) (by decide)
      · right
        exact rec13611 8 10 (by decide) (by decide)
      · right
        exact rec13614 8 10 (by decide) (by decide)
      · right
        exact rec13617 8 10 (by decide) (by decide)
      · right
        exact rec13620 8 10 (by decide) (by decide)
      · right
        exact rec13623 8 10 (by decide) (by decide)
      · right
        exact rec13626 8 10 (by decide) (by decide)
      · right
        exact rec13629 8 10 (by decide) (by decide)
      · right
        exact rec13632 8 10 (by decide) (by decide)
      · right
        exact rec13635 8 10 (by decide) (by decide)
      · right
        exact rec13638 8 10 (by decide) (by decide)
      · right
        exact rec13641 8 10 (by decide) (by decide)
      · right
        exact rec13644 8 10 (by decide) (by decide)
      · right
        exact rec13647 8 10 (by decide) (by decide)
      · right
        exact rec13650 8 10 (by decide) (by decide)
      · right
        exact rec13653 8 10 (by decide) (by decide)
      · right
        exact rec13656 8 10 (by decide) (by decide)
      · right
        exact rec13659 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 279)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 280)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13662 8 10 (by decide) (by decide)
      · right
        exact rec13665 8 10 (by decide) (by decide)
      · right
        exact rec13668 8 10 (by decide) (by decide)
      · right
        exact rec13671 8 10 (by decide) (by decide)
      · right
        exact rec13674 8 10 (by decide) (by decide)
      · right
        exact rec13677 8 10 (by decide) (by decide)
      · right
        exact rec13680 8 10 (by decide) (by decide)
      · right
        exact rec13683 8 10 (by decide) (by decide)
      · right
        exact rec13686 8 10 (by decide) (by decide)
      · right
        exact rec13689 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 281)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 282)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 283)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13692 8 10 (by decide) (by decide)
      · right
        exact rec13695 8 10 (by decide) (by decide)
      · right
        exact rec13698 8 10 (by decide) (by decide)
      · right
        exact rec13701 8 10 (by decide) (by decide)
      · right
        exact rec13704 8 10 (by decide) (by decide)
      · right
        exact rec13707 8 10 (by decide) (by decide)
      · right
        exact rec13710 8 10 (by decide) (by decide)
      · right
        exact rec13713 8 10 (by decide) (by decide)
      · right
        exact rec13716 8 10 (by decide) (by decide)
      · right
        exact rec13719 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 284)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 285)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13722 8 10 (by decide) (by decide)
      · right
        exact rec13725 8 10 (by decide) (by decide)
      · right
        exact rec13728 8 10 (by decide) (by decide)
      · right
        exact rec13731 8 10 (by decide) (by decide)
      · right
        exact rec13734 8 10 (by decide) (by decide)
      · right
        exact rec13737 8 10 (by decide) (by decide)
      · right
        exact rec13740 8 10 (by decide) (by decide)
      · right
        exact rec13743 8 10 (by decide) (by decide)
      · right
        exact rec13746 8 10 (by decide) (by decide)
      · right
        exact rec13749 8 10 (by decide) (by decide)
      · right
        exact rec13752 8 10 (by decide) (by decide)
      · right
        exact rec13755 8 10 (by decide) (by decide)
      · right
        exact rec13758 8 10 (by decide) (by decide)
      · right
        exact rec13761 8 10 (by decide) (by decide)
      · right
        exact rec13764 8 10 (by decide) (by decide)
      · right
        exact rec13767 8 10 (by decide) (by decide)
      · right
        exact rec13770 8 10 (by decide) (by decide)
      · right
        exact rec13773 8 10 (by decide) (by decide)
      · right
        exact rec13776 8 10 (by decide) (by decide)
      · right
        exact rec13779 8 10 (by decide) (by decide)
      · right
        exact rec13782 8 10 (by decide) (by decide)
      · right
        exact rec13785 8 10 (by decide) (by decide)
      · right
        exact rec13788 8 10 (by decide) (by decide)
      · right
        exact rec13791 8 10 (by decide) (by decide)
      · right
        exact rec13794 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 286)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 287)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 288)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13797 8 10 (by decide) (by decide)
      · right
        exact rec13800 8 10 (by decide) (by decide)
      · right
        exact rec13803 8 10 (by decide) (by decide)
      · right
        exact rec13806 8 10 (by decide) (by decide)
      · right
        exact rec13809 8 10 (by decide) (by decide)
      · right
        exact rec13812 8 10 (by decide) (by decide)
      · right
        exact rec13815 8 10 (by decide) (by decide)
      · right
        exact rec13818 8 10 (by decide) (by decide)
      · right
        exact rec13821 8 10 (by decide) (by decide)
      · right
        exact rec13824 8 10 (by decide) (by decide)
      · right
        exact rec13827 8 10 (by decide) (by decide)
      · right
        exact rec13830 8 10 (by decide) (by decide)
      · right
        exact rec13833 8 10 (by decide) (by decide)
      · right
        exact rec13836 8 10 (by decide) (by decide)
      · right
        exact rec13839 8 10 (by decide) (by decide)
      · right
        exact rec13842 8 10 (by decide) (by decide)
      · right
        exact rec13845 8 10 (by decide) (by decide)
      · right
        exact rec13848 8 10 (by decide) (by decide)
      · right
        exact rec13851 8 10 (by decide) (by decide)
      · right
        exact rec13854 8 10 (by decide) (by decide)
      · right
        exact rec13857 8 10 (by decide) (by decide)
      · right
        exact rec13860 8 10 (by decide) (by decide)
      · right
        exact rec13863 8 10 (by decide) (by decide)
      · right
        exact rec13866 8 10 (by decide) (by decide)
      · right
        exact rec13869 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 289)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 290)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13872 8 10 (by decide) (by decide)
      · right
        exact rec13875 8 10 (by decide) (by decide)
      · right
        exact rec13878 8 10 (by decide) (by decide)
      · right
        exact rec13881 8 10 (by decide) (by decide)
      · right
        exact rec13884 8 10 (by decide) (by decide)
      · right
        exact rec13887 8 10 (by decide) (by decide)
      · right
        exact rec13890 8 10 (by decide) (by decide)
      · right
        exact rec13893 8 10 (by decide) (by decide)
      · right
        exact rec13896 8 10 (by decide) (by decide)
      · right
        exact rec13899 8 10 (by decide) (by decide)
      · right
        exact rec13902 8 10 (by decide) (by decide)
      · right
        exact rec13905 8 10 (by decide) (by decide)
      · right
        exact rec13908 8 10 (by decide) (by decide)
      · right
        exact rec13911 8 10 (by decide) (by decide)
      · right
        exact rec13914 8 10 (by decide) (by decide)
      · right
        exact rec13917 8 10 (by decide) (by decide)
      · right
        exact rec13920 8 10 (by decide) (by decide)
      · right
        exact rec13923 8 10 (by decide) (by decide)
      · right
        exact rec13926 8 10 (by decide) (by decide)
      · right
        exact rec13929 8 10 (by decide) (by decide)
      · right
        exact rec13932 8 10 (by decide) (by decide)
      · right
        exact rec13935 8 10 (by decide) (by decide)
      · right
        exact rec13938 8 10 (by decide) (by decide)
      · right
        exact rec13941 8 10 (by decide) (by decide)
      · right
        exact rec13944 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 291)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 292)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 293)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13947 8 10 (by decide) (by decide)
      · right
        exact rec13950 8 10 (by decide) (by decide)
      · right
        exact rec13953 8 10 (by decide) (by decide)
      · right
        exact rec13956 8 10 (by decide) (by decide)
      · right
        exact rec13959 8 10 (by decide) (by decide)
      · right
        exact rec13962 8 10 (by decide) (by decide)
      · right
        exact rec13965 8 10 (by decide) (by decide)
      · right
        exact rec13968 8 10 (by decide) (by decide)
      · right
        exact rec13971 8 10 (by decide) (by decide)
      · right
        exact rec13974 8 10 (by decide) (by decide)
      · right
        exact rec13977 8 10 (by decide) (by decide)
      · right
        exact rec13980 8 10 (by decide) (by decide)
      · right
        exact rec13983 8 10 (by decide) (by decide)
      · right
        exact rec13986 8 10 (by decide) (by decide)
      · right
        exact rec13989 8 10 (by decide) (by decide)
      · right
        exact rec13992 8 10 (by decide) (by decide)
      · right
        exact rec13995 8 10 (by decide) (by decide)
      · right
        exact rec13998 8 10 (by decide) (by decide)
      · right
        exact rec14001 8 10 (by decide) (by decide)
      · right
        exact rec14004 8 10 (by decide) (by decide)
      · right
        exact rec14007 8 10 (by decide) (by decide)
      · right
        exact rec14010 8 10 (by decide) (by decide)
      · right
        exact rec14013 8 10 (by decide) (by decide)
      · right
        exact rec14016 8 10 (by decide) (by decide)
      · right
        exact rec14019 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 294)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 295)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14022 8 10 (by decide) (by decide)
      · right
        exact rec14025 8 10 (by decide) (by decide)
      · right
        exact rec14028 8 10 (by decide) (by decide)
      · right
        exact rec14031 8 10 (by decide) (by decide)
      · right
        exact rec14034 8 10 (by decide) (by decide)
      · right
        exact rec14037 8 10 (by decide) (by decide)
      · right
        exact rec14040 8 10 (by decide) (by decide)
      · right
        exact rec14043 8 10 (by decide) (by decide)
      · right
        exact rec14046 8 10 (by decide) (by decide)
      · right
        exact rec14049 8 10 (by decide) (by decide)
      · right
        exact rec14052 8 10 (by decide) (by decide)
      · right
        exact rec14055 8 10 (by decide) (by decide)
      · right
        exact rec14058 8 10 (by decide) (by decide)
      · right
        exact rec14061 8 10 (by decide) (by decide)
      · right
        exact rec14064 8 10 (by decide) (by decide)
      · right
        exact rec14067 8 10 (by decide) (by decide)
      · right
        exact rec14070 8 10 (by decide) (by decide)
      · right
        exact rec14073 8 10 (by decide) (by decide)
      · right
        exact rec14076 8 10 (by decide) (by decide)
      · right
        exact rec14079 8 10 (by decide) (by decide)
      · right
        exact rec14082 8 10 (by decide) (by decide)
      · right
        exact rec14085 8 10 (by decide) (by decide)
      · right
        exact rec14088 8 10 (by decide) (by decide)
      · right
        exact rec14091 8 10 (by decide) (by decide)
      · right
        exact rec14094 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 296)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 297)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14097 8 10 (by decide) (by decide)
      · right
        exact rec14100 8 10 (by decide) (by decide)
      · right
        exact rec14103 8 10 (by decide) (by decide)
      · right
        exact rec14106 8 10 (by decide) (by decide)
      · right
        exact rec14109 8 10 (by decide) (by decide)
      · right
        exact rec14112 8 10 (by decide) (by decide)
      · right
        exact rec14115 8 10 (by decide) (by decide)
      · right
        exact rec14118 8 10 (by decide) (by decide)
      · right
        exact rec14121 8 10 (by decide) (by decide)
      · right
        exact rec14124 8 10 (by decide) (by decide)
      · right
        exact rec14127 8 10 (by decide) (by decide)
      · right
        exact rec14130 8 10 (by decide) (by decide)
      · right
        exact rec14133 8 10 (by decide) (by decide)
      · right
        exact rec14136 8 10 (by decide) (by decide)
      · right
        exact rec14139 8 10 (by decide) (by decide)
      · right
        exact rec14142 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 298)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 299)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 300)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14145 8 10 (by decide) (by decide)
      · right
        exact rec14148 8 10 (by decide) (by decide)
      · right
        exact rec14151 8 10 (by decide) (by decide)
      · right
        exact rec14154 8 10 (by decide) (by decide)
      · right
        exact rec14157 8 10 (by decide) (by decide)
      · right
        exact rec14160 8 10 (by decide) (by decide)
      · right
        exact rec14163 8 10 (by decide) (by decide)
      · right
        exact rec14166 8 10 (by decide) (by decide)
      · right
        exact rec14169 8 10 (by decide) (by decide)
      · right
        exact rec14172 8 10 (by decide) (by decide)
      · right
        exact rec14175 8 10 (by decide) (by decide)
      · right
        exact rec14178 8 10 (by decide) (by decide)
      · right
        exact rec14181 8 10 (by decide) (by decide)
      · right
        exact rec14184 8 10 (by decide) (by decide)
      · right
        exact rec14187 8 10 (by decide) (by decide)
      · right
        exact rec14190 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 301)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 302)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14193 8 10 (by decide) (by decide)
      · right
        exact rec14196 8 10 (by decide) (by decide)
      · right
        exact rec14199 8 10 (by decide) (by decide)
      · right
        exact rec14202 8 10 (by decide) (by decide)
      · right
        exact rec14205 8 10 (by decide) (by decide)
      · right
        exact rec14208 8 10 (by decide) (by decide)
      · right
        exact rec14211 8 10 (by decide) (by decide)
      · right
        exact rec14214 8 10 (by decide) (by decide)
      · right
        exact rec14217 8 10 (by decide) (by decide)
      · right
        exact rec14220 8 10 (by decide) (by decide)
      · right
        exact rec14223 8 10 (by decide) (by decide)
      · right
        exact rec14226 8 10 (by decide) (by decide)
      · right
        exact rec14229 8 10 (by decide) (by decide)
      · right
        exact rec14232 8 10 (by decide) (by decide)
      · right
        exact rec14235 8 10 (by decide) (by decide)
      · right
        exact rec14238 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 303)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 304)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 305)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14241 8 10 (by decide) (by decide)
      · right
        exact rec14244 8 10 (by decide) (by decide)
      · right
        exact rec14247 8 10 (by decide) (by decide)
      · right
        exact rec14250 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 534)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 307)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14253 8 10 (by decide) (by decide)
      · right
        exact rec14256 8 10 (by decide) (by decide)
      · right
        exact rec14259 8 10 (by decide) (by decide)
      · right
        exact rec14262 8 10 (by decide) (by decide)
      · right
        exact rec14265 8 10 (by decide) (by decide)
      · right
        exact rec14268 8 10 (by decide) (by decide)
      · right
        exact rec14271 8 10 (by decide) (by decide)
      · right
        exact rec14274 8 10 (by decide) (by decide)
      · right
        exact rec14277 8 10 (by decide) (by decide)
      · right
        exact rec14280 8 10 (by decide) (by decide)
      · right
        exact rec14283 8 10 (by decide) (by decide)
      · right
        exact rec14286 8 10 (by decide) (by decide)
      · right
        exact rec14289 8 10 (by decide) (by decide)
      · right
        exact rec14292 8 10 (by decide) (by decide)
      · right
        exact rec14295 8 10 (by decide) (by decide)
      · right
        exact rec14298 8 10 (by decide) (by decide)
      · right
        exact rec14301 8 10 (by decide) (by decide)
      · right
        exact rec14304 8 10 (by decide) (by decide)
      · right
        exact rec14307 8 10 (by decide) (by decide)
      · right
        exact rec14310 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 308)).length = 20 := by decide +kernel
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
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · right
        exact rec14313 8 10 (by decide) (by decide)
      · right
        exact rec14316 8 10 (by decide) (by decide)
      · right
        exact rec14319 8 10 (by decide) (by decide)
      · right
        exact rec14322 8 10 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 309)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14325 8 10 (by decide) (by decide)
      · right
        exact rec14328 8 10 (by decide) (by decide)
      · right
        exact rec14331 8 10 (by decide) (by decide)
      · right
        exact rec14334 8 10 (by decide) (by decide)
      · right
        exact rec14337 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 310)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 311)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14340 8 10 (by decide) (by decide)
      · right
        exact rec14343 8 10 (by decide) (by decide)
      · right
        exact rec14346 8 10 (by decide) (by decide)
      · right
        exact rec14349 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 312)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14352 8 10 (by decide) (by decide)
      · right
        exact rec14355 8 10 (by decide) (by decide)
      · right
        exact rec14358 8 10 (by decide) (by decide)
      · right
        exact rec14361 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 313)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14364 8 10 (by decide) (by decide)
      · right
        exact rec14367 8 10 (by decide) (by decide)
      · right
        exact rec14370 8 10 (by decide) (by decide)
      · right
        exact rec14373 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 314)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 315)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14377 8 10 (by decide) (by decide)
      · right
        exact rec14380 8 10 (by decide) (by decide)
      · right
        exact rec14383 8 10 (by decide) (by decide)
      · right
        exact rec14386 8 10 (by decide) (by decide)
      · right
        exact rec14389 8 10 (by decide) (by decide)
      · right
        exact rec14392 8 10 (by decide) (by decide)
      · right
        exact rec14395 8 10 (by decide) (by decide)
      · right
        exact rec14398 8 10 (by decide) (by decide)
      · right
        exact rec14401 8 10 (by decide) (by decide)
      · right
        exact rec14404 8 10 (by decide) (by decide)
      · right
        exact rec14407 8 10 (by decide) (by decide)
      · right
        exact rec14410 8 10 (by decide) (by decide)
      · right
        exact rec14413 8 10 (by decide) (by decide)
      · right
        exact rec14416 8 10 (by decide) (by decide)
      · right
        exact rec14419 8 10 (by decide) (by decide)
      · right
        exact rec14422 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 316)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 317)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14425 8 10 (by decide) (by decide)
      · right
        exact rec14428 8 10 (by decide) (by decide)
      · right
        exact rec14431 8 10 (by decide) (by decide)
      · right
        exact rec14434 8 10 (by decide) (by decide)
      · right
        exact rec14437 8 10 (by decide) (by decide)
      · right
        exact rec14440 8 10 (by decide) (by decide)
      · right
        exact rec14443 8 10 (by decide) (by decide)
      · right
        exact rec14446 8 10 (by decide) (by decide)
      · right
        exact rec14449 8 10 (by decide) (by decide)
      · right
        exact rec14452 8 10 (by decide) (by decide)
      · right
        exact rec14455 8 10 (by decide) (by decide)
      · right
        exact rec14458 8 10 (by decide) (by decide)
      · right
        exact rec14461 8 10 (by decide) (by decide)
      · right
        exact rec14464 8 10 (by decide) (by decide)
      · right
        exact rec14467 8 10 (by decide) (by decide)
      · right
        exact rec14470 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 318)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14473 8 10 (by decide) (by decide)
      · right
        exact rec14476 8 10 (by decide) (by decide)
      · right
        exact rec14479 8 10 (by decide) (by decide)
      · right
        exact rec14482 8 10 (by decide) (by decide)
      · right
        exact rec14485 8 10 (by decide) (by decide)
      · right
        exact rec14488 8 10 (by decide) (by decide)
      · right
        exact rec14491 8 10 (by decide) (by decide)
      · right
        exact rec14494 8 10 (by decide) (by decide)
      · right
        exact rec14497 8 10 (by decide) (by decide)
      · right
        exact rec14500 8 10 (by decide) (by decide)
      · right
        exact rec14503 8 10 (by decide) (by decide)
      · right
        exact rec14506 8 10 (by decide) (by decide)
      · right
        exact rec14509 8 10 (by decide) (by decide)
      · right
        exact rec14512 8 10 (by decide) (by decide)
      · right
        exact rec14515 8 10 (by decide) (by decide)
      · right
        exact rec14518 8 10 (by decide) (by decide)
      · right
        exact rec14521 8 10 (by decide) (by decide)
      · right
        exact rec14524 8 10 (by decide) (by decide)
      · right
        exact rec14527 8 10 (by decide) (by decide)
      · right
        exact rec14530 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 319)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14533 8 10 (by decide) (by decide)
      · right
        exact rec14536 8 10 (by decide) (by decide)
      · right
        exact rec14539 8 10 (by decide) (by decide)
      · right
        exact rec14542 8 10 (by decide) (by decide)
      · right
        exact rec14545 8 10 (by decide) (by decide)
      · right
        exact rec14548 8 10 (by decide) (by decide)
      · right
        exact rec14551 8 10 (by decide) (by decide)
      · right
        exact rec14554 8 10 (by decide) (by decide)
      · right
        exact rec14557 8 10 (by decide) (by decide)
      · right
        exact rec14560 8 10 (by decide) (by decide)
      · right
        exact rec14563 8 10 (by decide) (by decide)
      · right
        exact rec14566 8 10 (by decide) (by decide)
      · right
        exact rec14569 8 10 (by decide) (by decide)
      · right
        exact rec14572 8 10 (by decide) (by decide)
      · right
        exact rec14575 8 10 (by decide) (by decide)
      · right
        exact rec14578 8 10 (by decide) (by decide)
      · right
        exact rec14581 8 10 (by decide) (by decide)
      · right
        exact rec14584 8 10 (by decide) (by decide)
      · right
        exact rec14587 8 10 (by decide) (by decide)
      · right
        exact rec14590 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 320)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 321)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14593 8 10 (by decide) (by decide)
      · right
        exact rec14596 8 10 (by decide) (by decide)
      · right
        exact rec14599 8 10 (by decide) (by decide)
      · right
        exact rec14602 8 10 (by decide) (by decide)
      · right
        exact rec14605 8 10 (by decide) (by decide)
      · right
        exact rec14608 8 10 (by decide) (by decide)
      · right
        exact rec14611 8 10 (by decide) (by decide)
      · right
        exact rec14614 8 10 (by decide) (by decide)
      · right
        exact rec14617 8 10 (by decide) (by decide)
      · right
        exact rec14620 8 10 (by decide) (by decide)
      · right
        exact rec14623 8 10 (by decide) (by decide)
      · right
        exact rec14626 8 10 (by decide) (by decide)
      · right
        exact rec14629 8 10 (by decide) (by decide)
      · right
        exact rec14632 8 10 (by decide) (by decide)
      · right
        exact rec14635 8 10 (by decide) (by decide)
      · right
        exact rec14638 8 10 (by decide) (by decide)
      · right
        exact rec14641 8 10 (by decide) (by decide)
      · right
        exact rec14644 8 10 (by decide) (by decide)
      · right
        exact rec14647 8 10 (by decide) (by decide)
      · right
        exact rec14650 8 10 (by decide) (by decide)
      · right
        exact rec14653 8 10 (by decide) (by decide)
      · right
        exact rec14656 8 10 (by decide) (by decide)
      · right
        exact rec14659 8 10 (by decide) (by decide)
      · right
        exact rec14662 8 10 (by decide) (by decide)
      · right
        exact rec14665 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 535)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 323)).length = 10 := by decide +kernel
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
  · left
    exact rec13306 8 11 (by decide) (by decide)
  · left
    exact rec13303 8 12 (by decide) (by decide)
  · left
    exact rec13304 8 13 (by decide) (by decide)
  · left
    exact rec13308 8 14 (by decide) (by decide)
  · left
    exact rec13306 8 15 (by decide) (by decide)
end Section14Coverage_8_7_p0_16

#print axioms solution
