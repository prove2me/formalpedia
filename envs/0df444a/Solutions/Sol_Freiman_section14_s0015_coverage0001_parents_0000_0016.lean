-- Prove2me | solution 1 for Freiman.section14_s0015_coverage0001_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:16:31.841652+00:00
-- url     : https://prove2.me/submissions/0c9cd1ed-560e-4bbb-a577-c0ade59e9193

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
namespace Section14Coverage_15_1_p0_16
private theorem rec415 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,4,7,8,12,15,16],[5],66⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[415]? = some (⟨16,(-1),[3,4,7,8,12,15,16],[5],66⟩) from rfl))
private theorem rec416 (si parent : ℕ) (hs : si ∈ ([3, 7, 11, 15] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,11,15],[0],914⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[416]? = some (⟨16,(-1),[3,7,11,15],[0],914⟩) from rfl))
private theorem rec417 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[1],58⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[417]? = some (⟨16,(-1),[3,7,15],[1],58⟩) from rfl))
private theorem rec418 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[2],60⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[418]? = some (⟨16,(-1),[3,7,15],[2],60⟩) from rfl))
private theorem rec419 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[3],62⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[419]? = some (⟨16,(-1),[3,7,15],[3],62⟩) from rfl))
private theorem rec420 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([4] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[4],66⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[420]? = some (⟨16,(-1),[3,7,15],[4],66⟩) from rfl))
private theorem rec421 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[6],68⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[421]? = some (⟨16,(-1),[3,7,15],[6],68⟩) from rfl))
private theorem rec422 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([7] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[7],72⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[422]? = some (⟨16,(-1),[3,7,15],[7],72⟩) from rfl))
private theorem rec423 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[10],208⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[423]? = some (⟨16,(-1),[3,7,15],[10],208⟩) from rfl))
private theorem rec424 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([13] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[13],241⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[424]? = some (⟨16,(-1),[3,7,15],[13],241⟩) from rfl))
private theorem rec425 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([12] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[12],242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[425]? = some (⟨16,(-1),[3,7,15],[12],242⟩) from rfl))
private theorem rec426 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[14],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[426]? = some (⟨16,(-1),[3,7,15],[14],243⟩) from rfl))
private theorem rec427 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([15] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,15],[15],245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[427]? = some (⟨16,(-1),[3,7,15],[15],245⟩) from rfl))
private theorem rec925 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[925]? = some (⟨20,(0),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec926 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[3,15],[11],209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[926]? = some (⟨20,(0),[3,15],[11],209⟩) from rfl))
private theorem rec936 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[936]? = some (⟨20,(1),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec937 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[3,15],[11],210⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[937]? = some (⟨20,(1),[3,15],[11],210⟩) from rfl))
private theorem rec947 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[947]? = some (⟨20,(2),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec948 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[3,15],[11],209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[948]? = some (⟨20,(2),[3,15],[11],209⟩) from rfl))
private theorem rec958 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[958]? = some (⟨20,(3),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec959 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[3,15],[11],211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[959]? = some (⟨20,(3),[3,15],[11],211⟩) from rfl))
private theorem rec969 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[969]? = some (⟨20,(4),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec970 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[3,15],[11],212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[970]? = some (⟨20,(4),[3,15],[11],212⟩) from rfl))
private theorem rec980 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[980]? = some (⟨20,(5),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec981 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[3,15],[11],209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[981]? = some (⟨20,(5),[3,15],[11],209⟩) from rfl))
private theorem rec991 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[991]? = some (⟨20,(6),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec992 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[3,15],[11],210⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[992]? = some (⟨20,(6),[3,15],[11],210⟩) from rfl))
private theorem rec1002 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1002]? = some (⟨20,(7),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1003 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[3,15],[11],209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1003]? = some (⟨20,(7),[3,15],[11],209⟩) from rfl))
private theorem rec1013 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1013]? = some (⟨20,(8),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1014 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[3,15],[11],211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1014]? = some (⟨20,(8),[3,15],[11],211⟩) from rfl))
private theorem rec1024 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1024]? = some (⟨20,(9),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1025 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[3,15],[11],212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1025]? = some (⟨20,(9),[3,15],[11],212⟩) from rfl))
private theorem rec1035 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1035]? = some (⟨20,(10),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1036 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[3,15],[11],213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1036]? = some (⟨20,(10),[3,15],[11],213⟩) from rfl))
private theorem rec1046 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1046]? = some (⟨20,(11),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1047 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[3,15],[11],213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1047]? = some (⟨20,(11),[3,15],[11],213⟩) from rfl))
private theorem rec1057 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1057]? = some (⟨20,(12),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1058 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[3,15],[11],213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1058]? = some (⟨20,(12),[3,15],[11],213⟩) from rfl))
private theorem rec1068 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1068]? = some (⟨20,(13),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1069 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[3,15],[11],213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1069]? = some (⟨20,(13),[3,15],[11],213⟩) from rfl))
private theorem rec1079 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1079]? = some (⟨20,(14),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1080 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[3,15],[11],212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1080]? = some (⟨20,(14),[3,15],[11],212⟩) from rfl))
private theorem rec1090 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1090]? = some (⟨20,(15),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1091 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[3,15],[11],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1091]? = some (⟨20,(15),[3,15],[11],214⟩) from rfl))
private theorem rec1101 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1101]? = some (⟨20,(16),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1102 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[3,15],[11],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1102]? = some (⟨20,(16),[3,15],[11],214⟩) from rfl))
private theorem rec1112 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1112]? = some (⟨20,(17),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1113 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[3,15],[11],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1113]? = some (⟨20,(17),[3,15],[11],214⟩) from rfl))
private theorem rec1123 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1123]? = some (⟨20,(18),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1124 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[3,15],[11],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1124]? = some (⟨20,(18),[3,15],[11],214⟩) from rfl))
private theorem rec1134 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1134]? = some (⟨20,(19),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1135 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[3,15],[11],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1135]? = some (⟨20,(19),[3,15],[11],214⟩) from rfl))
private theorem rec1145 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1145]? = some (⟨20,(20),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1146 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[3,15],[11],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1146]? = some (⟨20,(20),[3,15],[11],215⟩) from rfl))
private theorem rec1156 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1156]? = some (⟨20,(21),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1157 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[3,15],[11],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1157]? = some (⟨20,(21),[3,15],[11],215⟩) from rfl))
private theorem rec1167 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1167]? = some (⟨20,(22),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1168 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[3,15],[11],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1168]? = some (⟨20,(22),[3,15],[11],215⟩) from rfl))
private theorem rec1178 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[9]? = some (⟨20,(23),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1179 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[3,15],[11],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[10]? = some (⟨20,(23),[3,15],[11],215⟩) from rfl))
private theorem rec1189 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[20]? = some (⟨20,(24),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1190 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[3,15],[11],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[21]? = some (⟨20,(24),[3,15],[11],215⟩) from rfl))
private theorem rec1377 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[3,7,15],[8],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[208]? = some (⟨25,(0),[3,7,15],[8],145⟩) from rfl))
private theorem rec1378 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[3,7,15],[9],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[209]? = some (⟨25,(0),[3,7,15],[9],189⟩) from rfl))
private theorem rec1379 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[3,15],[11],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[210]? = some (⟨25,(0),[3,15],[11],189⟩) from rfl))
private theorem rec1398 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[3,7,15],[8],146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[229]? = some (⟨25,(1),[3,7,15],[8],146⟩) from rfl))
private theorem rec1399 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[3,15],[9],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[230]? = some (⟨25,(1),[3,15],[9],190⟩) from rfl))
private theorem rec1400 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[3,15],[11],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[231]? = some (⟨25,(1),[3,15],[11],216⟩) from rfl))
private theorem rec1422 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[3,7,15],[8],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[253]? = some (⟨25,(2),[3,7,15],[8],145⟩) from rfl))
private theorem rec1423 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[3,15],[9],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[254]? = some (⟨25,(2),[3,15],[9],191⟩) from rfl))
private theorem rec1424 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[3,15],[11],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[255]? = some (⟨25,(2),[3,15],[11],217⟩) from rfl))
private theorem rec1446 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[3,7,15],[8],147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[277]? = some (⟨25,(3),[3,7,15],[8],147⟩) from rfl))
private theorem rec1447 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[3,15],[9],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[278]? = some (⟨25,(3),[3,15],[9],192⟩) from rfl))
private theorem rec1448 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[3,15],[11],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[279]? = some (⟨25,(3),[3,15],[11],218⟩) from rfl))
private theorem rec1470 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[3,7,15],[8],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[301]? = some (⟨25,(4),[3,7,15],[8],148⟩) from rfl))
private theorem rec1471 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[3,15],[9],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[302]? = some (⟨25,(4),[3,15],[9],193⟩) from rfl))
private theorem rec1472 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[3,15],[11],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[303]? = some (⟨25,(4),[3,15],[11],219⟩) from rfl))
private theorem rec1494 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[3,7,15],[8],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[325]? = some (⟨25,(5),[3,7,15],[8],145⟩) from rfl))
private theorem rec1495 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[3,7,15],[9],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[326]? = some (⟨25,(5),[3,7,15],[9],189⟩) from rfl))
private theorem rec1496 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[3,15],[11],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[327]? = some (⟨25,(5),[3,15],[11],189⟩) from rfl))
private theorem rec1515 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[3,7,15],[8],146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[346]? = some (⟨25,(6),[3,7,15],[8],146⟩) from rfl))
private theorem rec1516 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[3,15],[9],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[347]? = some (⟨25,(6),[3,15],[9],190⟩) from rfl))
private theorem rec1517 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[3,15],[11],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[348]? = some (⟨25,(6),[3,15],[11],216⟩) from rfl))
private theorem rec1539 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[3,7,15],[8],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[370]? = some (⟨25,(7),[3,7,15],[8],145⟩) from rfl))
private theorem rec1540 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[3,15],[9],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[371]? = some (⟨25,(7),[3,15],[9],191⟩) from rfl))
private theorem rec1541 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[3,15],[11],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[372]? = some (⟨25,(7),[3,15],[11],217⟩) from rfl))
private theorem rec1563 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[3,7,15],[8],147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[394]? = some (⟨25,(8),[3,7,15],[8],147⟩) from rfl))
private theorem rec1564 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[3,15],[9],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[395]? = some (⟨25,(8),[3,15],[9],192⟩) from rfl))
private theorem rec1565 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[3,15],[11],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[396]? = some (⟨25,(8),[3,15],[11],218⟩) from rfl))
private theorem rec1587 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[3,7,15],[8],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[418]? = some (⟨25,(9),[3,7,15],[8],148⟩) from rfl))
private theorem rec1588 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[3,15],[9],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[419]? = some (⟨25,(9),[3,15],[9],193⟩) from rfl))
private theorem rec1589 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[3,15],[11],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[420]? = some (⟨25,(9),[3,15],[11],219⟩) from rfl))
private theorem rec1611 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[3,7,15],[8],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[442]? = some (⟨25,(10),[3,7,15],[8],149⟩) from rfl))
private theorem rec1612 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[3,7,15],[9],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[443]? = some (⟨25,(10),[3,7,15],[9],194⟩) from rfl))
private theorem rec1613 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[3,15],[11],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[444]? = some (⟨25,(10),[3,15],[11],194⟩) from rfl))
private theorem rec1632 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[3,7,15],[8],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[463]? = some (⟨25,(11),[3,7,15],[8],149⟩) from rfl))
private theorem rec1633 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[3,15],[9],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[464]? = some (⟨25,(11),[3,15],[9],195⟩) from rfl))
private theorem rec1634 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[3,15],[11],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[465]? = some (⟨25,(11),[3,15],[11],220⟩) from rfl))
private theorem rec1656 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[3,7,15],[8],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[487]? = some (⟨25,(12),[3,7,15],[8],149⟩) from rfl))
private theorem rec1657 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[3,15],[9],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[488]? = some (⟨25,(12),[3,15],[9],195⟩) from rfl))
private theorem rec1658 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[3,15],[11],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[489]? = some (⟨25,(12),[3,15],[11],220⟩) from rfl))
private theorem rec1680 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[3,7,15],[8],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[511]? = some (⟨25,(13),[3,7,15],[8],149⟩) from rfl))
private theorem rec1681 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[3,15],[9],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[512]? = some (⟨25,(13),[3,15],[9],195⟩) from rfl))
private theorem rec1682 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[3,15],[11],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[513]? = some (⟨25,(13),[3,15],[11],220⟩) from rfl))
private theorem rec1704 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[3,7,15],[8],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[535]? = some (⟨25,(14),[3,7,15],[8],148⟩) from rfl))
private theorem rec1705 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[3,15],[9],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[536]? = some (⟨25,(14),[3,15],[9],193⟩) from rfl))
private theorem rec1706 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[3,15],[11],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[537]? = some (⟨25,(14),[3,15],[11],219⟩) from rfl))
private theorem rec1728 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[559]? = some (⟨25,(15),[3,7,15],[8],150⟩) from rfl))
private theorem rec1729 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[3,7,15],[9],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[560]? = some (⟨25,(15),[3,7,15],[9],196⟩) from rfl))
private theorem rec1730 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[3,15],[11],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[561]? = some (⟨25,(15),[3,15],[11],196⟩) from rfl))
private theorem rec1749 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[580]? = some (⟨25,(16),[3,7,15],[8],150⟩) from rfl))
private theorem rec1750 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[3,15],[9],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[581]? = some (⟨25,(16),[3,15],[9],197⟩) from rfl))
private theorem rec1751 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[3,15],[11],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[582]? = some (⟨25,(16),[3,15],[11],221⟩) from rfl))
private theorem rec1773 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[604]? = some (⟨25,(17),[3,7,15],[8],150⟩) from rfl))
private theorem rec1774 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[3,15],[9],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[605]? = some (⟨25,(17),[3,15],[9],197⟩) from rfl))
private theorem rec1775 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[3,15],[11],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[606]? = some (⟨25,(17),[3,15],[11],221⟩) from rfl))
private theorem rec1797 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[628]? = some (⟨25,(18),[3,7,15],[8],150⟩) from rfl))
private theorem rec1798 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[3,15],[9],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[629]? = some (⟨25,(18),[3,15],[9],197⟩) from rfl))
private theorem rec1799 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[3,15],[11],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[630]? = some (⟨25,(18),[3,15],[11],221⟩) from rfl))
private theorem rec1821 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[652]? = some (⟨25,(19),[3,7,15],[8],150⟩) from rfl))
private theorem rec1822 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[3,15],[9],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[653]? = some (⟨25,(19),[3,15],[9],197⟩) from rfl))
private theorem rec1823 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[3,15],[11],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[654]? = some (⟨25,(19),[3,15],[11],221⟩) from rfl))
private theorem rec1845 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[676]? = some (⟨25,(20),[3,7,15],[8],151⟩) from rfl))
private theorem rec1846 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[3,7,15],[9],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[677]? = some (⟨25,(20),[3,7,15],[9],198⟩) from rfl))
private theorem rec1847 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[3,15],[11],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[678]? = some (⟨25,(20),[3,15],[11],198⟩) from rfl))
private theorem rec1866 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[697]? = some (⟨25,(21),[3,7,15],[8],151⟩) from rfl))
private theorem rec1867 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[3,15],[9],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[698]? = some (⟨25,(21),[3,15],[9],199⟩) from rfl))
private theorem rec1868 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[3,15],[11],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[699]? = some (⟨25,(21),[3,15],[11],222⟩) from rfl))
private theorem rec1890 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[721]? = some (⟨25,(22),[3,7,15],[8],151⟩) from rfl))
private theorem rec1891 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[3,15],[9],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[722]? = some (⟨25,(22),[3,15],[9],199⟩) from rfl))
private theorem rec1892 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[3,15],[11],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[723]? = some (⟨25,(22),[3,15],[11],222⟩) from rfl))
private theorem rec1914 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[745]? = some (⟨25,(23),[3,7,15],[8],151⟩) from rfl))
private theorem rec1915 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[3,15],[9],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[746]? = some (⟨25,(23),[3,15],[9],199⟩) from rfl))
private theorem rec1916 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[3,15],[11],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[747]? = some (⟨25,(23),[3,15],[11],222⟩) from rfl))
private theorem rec1938 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[769]? = some (⟨25,(24),[3,7,15],[8],151⟩) from rfl))
private theorem rec1939 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[3,15],[9],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[770]? = some (⟨25,(24),[3,15],[9],199⟩) from rfl))
private theorem rec1940 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[3,15],[11],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[771]? = some (⟨25,(24),[3,15],[11],222⟩) from rfl))
private theorem rec2906 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[3,7,15],[8,9],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[463]? = some (⟨36,(5),[3,7,15],[8,9],105⟩) from rfl))
private theorem rec2907 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[464]? = some (⟨36,(5),[3,15],[11],3⟩) from rfl))
private theorem rec2916 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[3,7,15],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[473]? = some (⟨36,(7),[3,7,15],[9],3⟩) from rfl))
private theorem rec2917 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([8, 11] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[3,15],[8,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[474]? = some (⟨36,(7),[3,15],[8,11],3⟩) from rfl))
private theorem rec2930 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[3,7,15],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[487]? = some (⟨36,(8),[3,7,15],[9],3⟩) from rfl))
private theorem rec2931 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([8, 11] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[3,15],[8,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[488]? = some (⟨36,(8),[3,15],[8,11],3⟩) from rfl))
private theorem rec2945 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[3,7,15],[9],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[502]? = some (⟨36,(9),[3,7,15],[9],143⟩) from rfl))
private theorem rec2947 (si parent : ℕ) (hs : si ∈ ([15] : List ℕ)) (hp : parent ∈ ([8, 11] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[15],[8,11],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[504]? = some (⟨36,(9),[15],[8,11],143⟩) from rfl))
private theorem rec2954 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[3,7,15],[8],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[511]? = some (⟨36,(15),[3,7,15],[8],3⟩) from rfl))
private theorem rec2955 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9, 11] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[3,15],[9,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[512]? = some (⟨36,(15),[3,15],[9,11],3⟩) from rfl))
private theorem rec2967 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[3,7,15],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[524]? = some (⟨36,(16),[3,7,15],[9],3⟩) from rfl))
private theorem rec2968 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([8, 11] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[3,15],[8,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[525]? = some (⟨36,(16),[3,15],[8,11],3⟩) from rfl))
private theorem rec2975 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[3,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[532]? = some (⟨36,(17),[3,15],[8,9],3⟩) from rfl))
private theorem rec2976 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[3,15],[11],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[533]? = some (⟨36,(17),[3,15],[11],48⟩) from rfl))
private theorem rec2985 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[3,15],[11],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[542]? = some (⟨36,(19),[3,15],[11],143⟩) from rfl))
private theorem rec2990 (si parent : ℕ) (hs : si ∈ ([7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[7,15],[8,9],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[547]? = some (⟨36,(19),[7,15],[8,9],143⟩) from rfl))
private theorem rec14715 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(0),[3,7,15],[8],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1112]? = some (⟨335,(0),[3,7,15],[8],106⟩) from rfl))
private theorem rec14716 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(0),[3,7,15],[9],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1113]? = some (⟨335,(0),[3,7,15],[9],125⟩) from rfl))
private theorem rec14717 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(0),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1114]? = some (⟨335,(0),[3,15],[11],3⟩) from rfl))
private theorem rec14719 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(1),[3,7,15],[8],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1116]? = some (⟨335,(1),[3,7,15],[8],106⟩) from rfl))
private theorem rec14720 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(1),[3,7,15],[9],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1117]? = some (⟨335,(1),[3,7,15],[9],125⟩) from rfl))
private theorem rec14721 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(1),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1118]? = some (⟨335,(1),[3,15],[11],3⟩) from rfl))
private theorem rec14723 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(2),[3,7,15],[8],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1120]? = some (⟨335,(2),[3,7,15],[8],107⟩) from rfl))
private theorem rec14724 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(2),[3,7,15],[9],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1121]? = some (⟨335,(2),[3,7,15],[9],126⟩) from rfl))
private theorem rec14725 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(2),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1122]? = some (⟨335,(2),[3,15],[11],3⟩) from rfl))
private theorem rec14727 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(3),[3,7,15],[8],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1124]? = some (⟨335,(3),[3,7,15],[8],107⟩) from rfl))
private theorem rec14728 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(3),[3,7,15],[9],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1125]? = some (⟨335,(3),[3,7,15],[9],126⟩) from rfl))
private theorem rec14729 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(3),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1126]? = some (⟨335,(3),[3,15],[11],3⟩) from rfl))
private theorem rec14731 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(4),[3,7,15],[8],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1128]? = some (⟨335,(4),[3,7,15],[8],108⟩) from rfl))
private theorem rec14732 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(4),[3,7,15],[9],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1129]? = some (⟨335,(4),[3,7,15],[9],127⟩) from rfl))
private theorem rec14733 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(4),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1130]? = some (⟨335,(4),[3,15],[11],3⟩) from rfl))
private theorem rec14735 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(5),[3,7,15],[8],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1132]? = some (⟨335,(5),[3,7,15],[8],110⟩) from rfl))
private theorem rec14736 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(5),[3,7,15],[9],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1133]? = some (⟨335,(5),[3,7,15],[9],129⟩) from rfl))
private theorem rec14737 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(5),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1134]? = some (⟨335,(5),[3,15],[11],3⟩) from rfl))
private theorem rec14739 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(6),[3,7,15],[8],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1136]? = some (⟨335,(6),[3,7,15],[8],108⟩) from rfl))
private theorem rec14740 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(6),[3,7,15],[9],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1137]? = some (⟨335,(6),[3,7,15],[9],127⟩) from rfl))
private theorem rec14741 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(6),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1138]? = some (⟨335,(6),[3,15],[11],3⟩) from rfl))
private theorem rec14743 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(7),[3,7,15],[8],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1140]? = some (⟨335,(7),[3,7,15],[8],112⟩) from rfl))
private theorem rec14744 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(7),[3,7,15],[9],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1141]? = some (⟨335,(7),[3,7,15],[9],131⟩) from rfl))
private theorem rec14745 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(7),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1142]? = some (⟨335,(7),[3,15],[11],3⟩) from rfl))
private theorem rec14747 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(8),[3,7,15],[8],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1144]? = some (⟨335,(8),[3,7,15],[8],108⟩) from rfl))
private theorem rec14748 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(8),[3,7,15],[9],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1145]? = some (⟨335,(8),[3,7,15],[9],127⟩) from rfl))
private theorem rec14749 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(8),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1146]? = some (⟨335,(8),[3,15],[11],3⟩) from rfl))
private theorem rec14751 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(9),[3,7,15],[8],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1148]? = some (⟨335,(9),[3,7,15],[8],110⟩) from rfl))
private theorem rec14752 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(9),[3,7,15],[9],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1149]? = some (⟨335,(9),[3,7,15],[9],129⟩) from rfl))
private theorem rec14753 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 335 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(9),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1150]? = some (⟨335,(9),[3,15],[11],3⟩) from rfl))
private theorem rec14755 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(0),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1152]? = some (⟨339,(0),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14756 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(0),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1153]? = some (⟨339,(0),[3,15],[11],2⟩) from rfl))
private theorem rec14758 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(1),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1155]? = some (⟨339,(1),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14759 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(1),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1156]? = some (⟨339,(1),[3,15],[11],2⟩) from rfl))
private theorem rec14761 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(2),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1158]? = some (⟨339,(2),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14762 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(2),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1159]? = some (⟨339,(2),[3,15],[11],2⟩) from rfl))
private theorem rec14764 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(3),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1161]? = some (⟨339,(3),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14765 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(3),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1162]? = some (⟨339,(3),[3,15],[11],2⟩) from rfl))
private theorem rec14767 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(4),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1164]? = some (⟨339,(4),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14768 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(4),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1165]? = some (⟨339,(4),[3,15],[11],2⟩) from rfl))
private theorem rec14770 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(5),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1167]? = some (⟨339,(5),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14771 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(5),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1168]? = some (⟨339,(5),[3,15],[11],2⟩) from rfl))
private theorem rec14773 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(6),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1170]? = some (⟨339,(6),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14774 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(6),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1171]? = some (⟨339,(6),[3,15],[11],2⟩) from rfl))
private theorem rec14776 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(7),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1173]? = some (⟨339,(7),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14777 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(7),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1174]? = some (⟨339,(7),[3,15],[11],2⟩) from rfl))
private theorem rec14779 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(8),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1176]? = some (⟨339,(8),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14780 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(8),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1177]? = some (⟨339,(8),[3,15],[11],2⟩) from rfl))
private theorem rec14782 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(9),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1179]? = some (⟨339,(9),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14783 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 339 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(9),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1180]? = some (⟨339,(9),[3,15],[11],2⟩) from rfl))
private theorem rec14825 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([8, 9, 11] : List ℕ)) : section14Recorded section14Catalog si parent 347 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(0),[3,15],[8,9,11],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1222]? = some (⟨347,(0),[3,15],[8,9,11],159⟩) from rfl))
private theorem rec14828 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 347 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(1),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1225]? = some (⟨347,(1),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14829 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 347 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(1),[3,15],[11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1226]? = some (⟨347,(1),[3,15],[11],2⟩) from rfl))
private theorem rec14831 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 347 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(2),[3,7,15],[8,9],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1228]? = some (⟨347,(2),[3,7,15],[8,9],159⟩) from rfl))
private theorem rec14832 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 347 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(2),[3,15],[11],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1229]? = some (⟨347,(2),[3,15],[11],159⟩) from rfl))
private theorem rec14834 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 347 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(3),[3,7,15],[8,9],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1231]? = some (⟨347,(3),[3,7,15],[8,9],99⟩) from rfl))
private theorem rec14835 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 347 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(3),[3,15],[11],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1232]? = some (⟨347,(3),[3,15],[11],99⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 15).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 15)).drop 0).take 16, section14Recorded section14Catalog 15 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 15).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[])],true,[(334,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(337,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(346,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 15)).drop 0).take 16 = [⟨2,0,[⟨true,false,12⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨2,1,[⟨true,false,12⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨2,2,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,3,[⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,4,[⟨true,false,16⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,5,[⟨true,false,16⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,6,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨2,7,[⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,8,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,9,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,10,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨2,11,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,12,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,13,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,14,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨2,15,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec416 15 0 (by decide) (by decide)
  · left
    exact rec417 15 1 (by decide) (by decide)
  · left
    exact rec418 15 2 (by decide) (by decide)
  · left
    exact rec419 15 3 (by decide) (by decide)
  · left
    exact rec420 15 4 (by decide) (by decide)
  · left
    exact rec415 15 5 (by decide) (by decide)
  · left
    exact rec421 15 6 (by decide) (by decide)
  · left
    exact rec422 15 7 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(334,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(337,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(346,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 334)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 335)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14715 15 8 (by decide) (by decide)
      · right
        exact rec14719 15 8 (by decide) (by decide)
      · right
        exact rec14723 15 8 (by decide) (by decide)
      · right
        exact rec14727 15 8 (by decide) (by decide)
      · right
        exact rec14731 15 8 (by decide) (by decide)
      · right
        exact rec14735 15 8 (by decide) (by decide)
      · right
        exact rec14739 15 8 (by decide) (by decide)
      · right
        exact rec14743 15 8 (by decide) (by decide)
      · right
        exact rec14747 15 8 (by decide) (by decide)
      · right
        exact rec14751 15 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 336)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec925 15 8 (by decide) (by decide)
      · right
        exact rec936 15 8 (by decide) (by decide)
      · right
        exact rec947 15 8 (by decide) (by decide)
      · right
        exact rec958 15 8 (by decide) (by decide)
      · right
        exact rec969 15 8 (by decide) (by decide)
      · right
        exact rec980 15 8 (by decide) (by decide)
      · right
        exact rec991 15 8 (by decide) (by decide)
      · right
        exact rec1002 15 8 (by decide) (by decide)
      · right
        exact rec1013 15 8 (by decide) (by decide)
      · right
        exact rec1024 15 8 (by decide) (by decide)
      · right
        exact rec1035 15 8 (by decide) (by decide)
      · right
        exact rec1046 15 8 (by decide) (by decide)
      · right
        exact rec1057 15 8 (by decide) (by decide)
      · right
        exact rec1068 15 8 (by decide) (by decide)
      · right
        exact rec1079 15 8 (by decide) (by decide)
      · right
        exact rec1090 15 8 (by decide) (by decide)
      · right
        exact rec1101 15 8 (by decide) (by decide)
      · right
        exact rec1112 15 8 (by decide) (by decide)
      · right
        exact rec1123 15 8 (by decide) (by decide)
      · right
        exact rec1134 15 8 (by decide) (by decide)
      · right
        exact rec1145 15 8 (by decide) (by decide)
      · right
        exact rec1156 15 8 (by decide) (by decide)
      · right
        exact rec1167 15 8 (by decide) (by decide)
      · right
        exact rec1178 15 8 (by decide) (by decide)
      · right
        exact rec1189 15 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 337)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 338)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 339)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14755 15 8 (by decide) (by decide)
      · right
        exact rec14758 15 8 (by decide) (by decide)
      · right
        exact rec14761 15 8 (by decide) (by decide)
      · right
        exact rec14764 15 8 (by decide) (by decide)
      · right
        exact rec14767 15 8 (by decide) (by decide)
      · right
        exact rec14770 15 8 (by decide) (by decide)
      · right
        exact rec14773 15 8 (by decide) (by decide)
      · right
        exact rec14776 15 8 (by decide) (by decide)
      · right
        exact rec14779 15 8 (by decide) (by decide)
      · right
        exact rec14782 15 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 340)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1377 15 8 (by decide) (by decide)
      · right
        exact rec1398 15 8 (by decide) (by decide)
      · right
        exact rec1422 15 8 (by decide) (by decide)
      · right
        exact rec1446 15 8 (by decide) (by decide)
      · right
        exact rec1470 15 8 (by decide) (by decide)
      · right
        exact rec1494 15 8 (by decide) (by decide)
      · right
        exact rec1515 15 8 (by decide) (by decide)
      · right
        exact rec1539 15 8 (by decide) (by decide)
      · right
        exact rec1563 15 8 (by decide) (by decide)
      · right
        exact rec1587 15 8 (by decide) (by decide)
      · right
        exact rec1611 15 8 (by decide) (by decide)
      · right
        exact rec1632 15 8 (by decide) (by decide)
      · right
        exact rec1656 15 8 (by decide) (by decide)
      · right
        exact rec1680 15 8 (by decide) (by decide)
      · right
        exact rec1704 15 8 (by decide) (by decide)
      · right
        exact rec1728 15 8 (by decide) (by decide)
      · right
        exact rec1749 15 8 (by decide) (by decide)
      · right
        exact rec1773 15 8 (by decide) (by decide)
      · right
        exact rec1797 15 8 (by decide) (by decide)
      · right
        exact rec1821 15 8 (by decide) (by decide)
      · right
        exact rec1845 15 8 (by decide) (by decide)
      · right
        exact rec1866 15 8 (by decide) (by decide)
      · right
        exact rec1890 15 8 (by decide) (by decide)
      · right
        exact rec1914 15 8 (by decide) (by decide)
      · right
        exact rec1938 15 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 341)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 346)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 347)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14825 15 8 (by decide) (by decide)
      · right
        exact rec14828 15 8 (by decide) (by decide)
      · right
        exact rec14831 15 8 (by decide) (by decide)
      · right
        exact rec14834 15 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2906 15 8 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2917 15 8 (by decide) (by decide)
      · right
        exact rec2931 15 8 (by decide) (by decide)
      · right
        exact rec2947 15 8 (by decide) (by decide)
      · left
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
        exact rec2954 15 8 (by decide) (by decide)
      · right
        exact rec2968 15 8 (by decide) (by decide)
      · right
        exact rec2975 15 8 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2990 15 8 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(334,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(337,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(346,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 334)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 335)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14716 15 9 (by decide) (by decide)
      · right
        exact rec14720 15 9 (by decide) (by decide)
      · right
        exact rec14724 15 9 (by decide) (by decide)
      · right
        exact rec14728 15 9 (by decide) (by decide)
      · right
        exact rec14732 15 9 (by decide) (by decide)
      · right
        exact rec14736 15 9 (by decide) (by decide)
      · right
        exact rec14740 15 9 (by decide) (by decide)
      · right
        exact rec14744 15 9 (by decide) (by decide)
      · right
        exact rec14748 15 9 (by decide) (by decide)
      · right
        exact rec14752 15 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 336)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec925 15 9 (by decide) (by decide)
      · right
        exact rec936 15 9 (by decide) (by decide)
      · right
        exact rec947 15 9 (by decide) (by decide)
      · right
        exact rec958 15 9 (by decide) (by decide)
      · right
        exact rec969 15 9 (by decide) (by decide)
      · right
        exact rec980 15 9 (by decide) (by decide)
      · right
        exact rec991 15 9 (by decide) (by decide)
      · right
        exact rec1002 15 9 (by decide) (by decide)
      · right
        exact rec1013 15 9 (by decide) (by decide)
      · right
        exact rec1024 15 9 (by decide) (by decide)
      · right
        exact rec1035 15 9 (by decide) (by decide)
      · right
        exact rec1046 15 9 (by decide) (by decide)
      · right
        exact rec1057 15 9 (by decide) (by decide)
      · right
        exact rec1068 15 9 (by decide) (by decide)
      · right
        exact rec1079 15 9 (by decide) (by decide)
      · right
        exact rec1090 15 9 (by decide) (by decide)
      · right
        exact rec1101 15 9 (by decide) (by decide)
      · right
        exact rec1112 15 9 (by decide) (by decide)
      · right
        exact rec1123 15 9 (by decide) (by decide)
      · right
        exact rec1134 15 9 (by decide) (by decide)
      · right
        exact rec1145 15 9 (by decide) (by decide)
      · right
        exact rec1156 15 9 (by decide) (by decide)
      · right
        exact rec1167 15 9 (by decide) (by decide)
      · right
        exact rec1178 15 9 (by decide) (by decide)
      · right
        exact rec1189 15 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 337)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 338)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 339)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14755 15 9 (by decide) (by decide)
      · right
        exact rec14758 15 9 (by decide) (by decide)
      · right
        exact rec14761 15 9 (by decide) (by decide)
      · right
        exact rec14764 15 9 (by decide) (by decide)
      · right
        exact rec14767 15 9 (by decide) (by decide)
      · right
        exact rec14770 15 9 (by decide) (by decide)
      · right
        exact rec14773 15 9 (by decide) (by decide)
      · right
        exact rec14776 15 9 (by decide) (by decide)
      · right
        exact rec14779 15 9 (by decide) (by decide)
      · right
        exact rec14782 15 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 340)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1378 15 9 (by decide) (by decide)
      · right
        exact rec1399 15 9 (by decide) (by decide)
      · right
        exact rec1423 15 9 (by decide) (by decide)
      · right
        exact rec1447 15 9 (by decide) (by decide)
      · right
        exact rec1471 15 9 (by decide) (by decide)
      · right
        exact rec1495 15 9 (by decide) (by decide)
      · right
        exact rec1516 15 9 (by decide) (by decide)
      · right
        exact rec1540 15 9 (by decide) (by decide)
      · right
        exact rec1564 15 9 (by decide) (by decide)
      · right
        exact rec1588 15 9 (by decide) (by decide)
      · right
        exact rec1612 15 9 (by decide) (by decide)
      · right
        exact rec1633 15 9 (by decide) (by decide)
      · right
        exact rec1657 15 9 (by decide) (by decide)
      · right
        exact rec1681 15 9 (by decide) (by decide)
      · right
        exact rec1705 15 9 (by decide) (by decide)
      · right
        exact rec1729 15 9 (by decide) (by decide)
      · right
        exact rec1750 15 9 (by decide) (by decide)
      · right
        exact rec1774 15 9 (by decide) (by decide)
      · right
        exact rec1798 15 9 (by decide) (by decide)
      · right
        exact rec1822 15 9 (by decide) (by decide)
      · right
        exact rec1846 15 9 (by decide) (by decide)
      · right
        exact rec1867 15 9 (by decide) (by decide)
      · right
        exact rec1891 15 9 (by decide) (by decide)
      · right
        exact rec1915 15 9 (by decide) (by decide)
      · right
        exact rec1939 15 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 341)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 346)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 347)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14825 15 9 (by decide) (by decide)
      · right
        exact rec14828 15 9 (by decide) (by decide)
      · right
        exact rec14831 15 9 (by decide) (by decide)
      · right
        exact rec14834 15 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2906 15 9 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2916 15 9 (by decide) (by decide)
      · right
        exact rec2930 15 9 (by decide) (by decide)
      · right
        exact rec2945 15 9 (by decide) (by decide)
      · left
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
        exact rec2955 15 9 (by decide) (by decide)
      · right
        exact rec2967 15 9 (by decide) (by decide)
      · right
        exact rec2975 15 9 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2990 15 9 (by decide) (by decide)
  · left
    exact rec423 15 10 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(334,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(337,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(346,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 334)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 335)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14717 15 11 (by decide) (by decide)
      · right
        exact rec14721 15 11 (by decide) (by decide)
      · right
        exact rec14725 15 11 (by decide) (by decide)
      · right
        exact rec14729 15 11 (by decide) (by decide)
      · right
        exact rec14733 15 11 (by decide) (by decide)
      · right
        exact rec14737 15 11 (by decide) (by decide)
      · right
        exact rec14741 15 11 (by decide) (by decide)
      · right
        exact rec14745 15 11 (by decide) (by decide)
      · right
        exact rec14749 15 11 (by decide) (by decide)
      · right
        exact rec14753 15 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 336)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec926 15 11 (by decide) (by decide)
      · right
        exact rec937 15 11 (by decide) (by decide)
      · right
        exact rec948 15 11 (by decide) (by decide)
      · right
        exact rec959 15 11 (by decide) (by decide)
      · right
        exact rec970 15 11 (by decide) (by decide)
      · right
        exact rec981 15 11 (by decide) (by decide)
      · right
        exact rec992 15 11 (by decide) (by decide)
      · right
        exact rec1003 15 11 (by decide) (by decide)
      · right
        exact rec1014 15 11 (by decide) (by decide)
      · right
        exact rec1025 15 11 (by decide) (by decide)
      · right
        exact rec1036 15 11 (by decide) (by decide)
      · right
        exact rec1047 15 11 (by decide) (by decide)
      · right
        exact rec1058 15 11 (by decide) (by decide)
      · right
        exact rec1069 15 11 (by decide) (by decide)
      · right
        exact rec1080 15 11 (by decide) (by decide)
      · right
        exact rec1091 15 11 (by decide) (by decide)
      · right
        exact rec1102 15 11 (by decide) (by decide)
      · right
        exact rec1113 15 11 (by decide) (by decide)
      · right
        exact rec1124 15 11 (by decide) (by decide)
      · right
        exact rec1135 15 11 (by decide) (by decide)
      · right
        exact rec1146 15 11 (by decide) (by decide)
      · right
        exact rec1157 15 11 (by decide) (by decide)
      · right
        exact rec1168 15 11 (by decide) (by decide)
      · right
        exact rec1179 15 11 (by decide) (by decide)
      · right
        exact rec1190 15 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 337)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 338)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 339)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14756 15 11 (by decide) (by decide)
      · right
        exact rec14759 15 11 (by decide) (by decide)
      · right
        exact rec14762 15 11 (by decide) (by decide)
      · right
        exact rec14765 15 11 (by decide) (by decide)
      · right
        exact rec14768 15 11 (by decide) (by decide)
      · right
        exact rec14771 15 11 (by decide) (by decide)
      · right
        exact rec14774 15 11 (by decide) (by decide)
      · right
        exact rec14777 15 11 (by decide) (by decide)
      · right
        exact rec14780 15 11 (by decide) (by decide)
      · right
        exact rec14783 15 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 340)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1379 15 11 (by decide) (by decide)
      · right
        exact rec1400 15 11 (by decide) (by decide)
      · right
        exact rec1424 15 11 (by decide) (by decide)
      · right
        exact rec1448 15 11 (by decide) (by decide)
      · right
        exact rec1472 15 11 (by decide) (by decide)
      · right
        exact rec1496 15 11 (by decide) (by decide)
      · right
        exact rec1517 15 11 (by decide) (by decide)
      · right
        exact rec1541 15 11 (by decide) (by decide)
      · right
        exact rec1565 15 11 (by decide) (by decide)
      · right
        exact rec1589 15 11 (by decide) (by decide)
      · right
        exact rec1613 15 11 (by decide) (by decide)
      · right
        exact rec1634 15 11 (by decide) (by decide)
      · right
        exact rec1658 15 11 (by decide) (by decide)
      · right
        exact rec1682 15 11 (by decide) (by decide)
      · right
        exact rec1706 15 11 (by decide) (by decide)
      · right
        exact rec1730 15 11 (by decide) (by decide)
      · right
        exact rec1751 15 11 (by decide) (by decide)
      · right
        exact rec1775 15 11 (by decide) (by decide)
      · right
        exact rec1799 15 11 (by decide) (by decide)
      · right
        exact rec1823 15 11 (by decide) (by decide)
      · right
        exact rec1847 15 11 (by decide) (by decide)
      · right
        exact rec1868 15 11 (by decide) (by decide)
      · right
        exact rec1892 15 11 (by decide) (by decide)
      · right
        exact rec1916 15 11 (by decide) (by decide)
      · right
        exact rec1940 15 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 341)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 346)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 347)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14825 15 11 (by decide) (by decide)
      · right
        exact rec14829 15 11 (by decide) (by decide)
      · right
        exact rec14832 15 11 (by decide) (by decide)
      · right
        exact rec14835 15 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2907 15 11 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2917 15 11 (by decide) (by decide)
      · right
        exact rec2931 15 11 (by decide) (by decide)
      · right
        exact rec2947 15 11 (by decide) (by decide)
      · left
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
        exact rec2955 15 11 (by decide) (by decide)
      · right
        exact rec2968 15 11 (by decide) (by decide)
      · right
        exact rec2976 15 11 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2985 15 11 (by decide) (by decide)
  · left
    exact rec425 15 12 (by decide) (by decide)
  · left
    exact rec424 15 13 (by decide) (by decide)
  · left
    exact rec426 15 14 (by decide) (by decide)
  · left
    exact rec427 15 15 (by decide) (by decide)
end Section14Coverage_15_1_p0_16

#print axioms solution
