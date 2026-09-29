-- Prove2me | solution 1 for Freiman.section14_s0007_coverage0001_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T08:46:05.442131+00:00
-- url     : https://prove2.me/submissions/e172f4e1-e9f1-429b-8446-86e4f065b3b5

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
namespace Section14Coverage_7_1_p0_16
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
private theorem rec451 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[7],[11],1398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[451]? = some (⟨16,(-1),[7],[11],1398⟩) from rfl))
private theorem rec925 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[925]? = some (⟨20,(0),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec936 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[936]? = some (⟨20,(1),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec947 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[947]? = some (⟨20,(2),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec958 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[958]? = some (⟨20,(3),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec969 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[969]? = some (⟨20,(4),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec980 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[980]? = some (⟨20,(5),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec991 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[991]? = some (⟨20,(6),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1002 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1002]? = some (⟨20,(7),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1013 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1013]? = some (⟨20,(8),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1024 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1024]? = some (⟨20,(9),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1035 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1035]? = some (⟨20,(10),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1046 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1046]? = some (⟨20,(11),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1057 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1057]? = some (⟨20,(12),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1068 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1068]? = some (⟨20,(13),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1079 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1079]? = some (⟨20,(14),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1090 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1090]? = some (⟨20,(15),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1101 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1101]? = some (⟨20,(16),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1112 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1112]? = some (⟨20,(17),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1123 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1123]? = some (⟨20,(18),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1134 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1134]? = some (⟨20,(19),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1145 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1145]? = some (⟨20,(20),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1156 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1156]? = some (⟨20,(21),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1167 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1167]? = some (⟨20,(22),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1178 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[9]? = some (⟨20,(23),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1189 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[3,7,15],[8,9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[20]? = some (⟨20,(24),[3,7,15],[8,9],3⟩) from rfl))
private theorem rec1377 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[3,7,15],[8],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[208]? = some (⟨25,(0),[3,7,15],[8],145⟩) from rfl))
private theorem rec1378 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[3,7,15],[9],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[209]? = some (⟨25,(0),[3,7,15],[9],189⟩) from rfl))
private theorem rec1398 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[3,7,15],[8],146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[229]? = some (⟨25,(1),[3,7,15],[8],146⟩) from rfl))
private theorem rec1406 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[7],[9],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[237]? = some (⟨25,(1),[7],[9],216⟩) from rfl))
private theorem rec1422 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[3,7,15],[8],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[253]? = some (⟨25,(2),[3,7,15],[8],145⟩) from rfl))
private theorem rec1430 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[7],[9],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[261]? = some (⟨25,(2),[7],[9],217⟩) from rfl))
private theorem rec1446 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[3,7,15],[8],147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[277]? = some (⟨25,(3),[3,7,15],[8],147⟩) from rfl))
private theorem rec1454 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[7],[9],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[285]? = some (⟨25,(3),[7],[9],218⟩) from rfl))
private theorem rec1470 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[3,7,15],[8],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[301]? = some (⟨25,(4),[3,7,15],[8],148⟩) from rfl))
private theorem rec1478 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[7],[9],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[309]? = some (⟨25,(4),[7],[9],219⟩) from rfl))
private theorem rec1494 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[3,7,15],[8],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[325]? = some (⟨25,(5),[3,7,15],[8],145⟩) from rfl))
private theorem rec1495 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[3,7,15],[9],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[326]? = some (⟨25,(5),[3,7,15],[9],189⟩) from rfl))
private theorem rec1515 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[3,7,15],[8],146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[346]? = some (⟨25,(6),[3,7,15],[8],146⟩) from rfl))
private theorem rec1523 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[7],[9],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[354]? = some (⟨25,(6),[7],[9],216⟩) from rfl))
private theorem rec1539 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[3,7,15],[8],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[370]? = some (⟨25,(7),[3,7,15],[8],145⟩) from rfl))
private theorem rec1547 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[7],[9],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[378]? = some (⟨25,(7),[7],[9],217⟩) from rfl))
private theorem rec1563 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[3,7,15],[8],147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[394]? = some (⟨25,(8),[3,7,15],[8],147⟩) from rfl))
private theorem rec1571 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[7],[9],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[402]? = some (⟨25,(8),[7],[9],218⟩) from rfl))
private theorem rec1587 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[3,7,15],[8],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[418]? = some (⟨25,(9),[3,7,15],[8],148⟩) from rfl))
private theorem rec1595 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[7],[9],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[426]? = some (⟨25,(9),[7],[9],219⟩) from rfl))
private theorem rec1611 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[3,7,15],[8],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[442]? = some (⟨25,(10),[3,7,15],[8],149⟩) from rfl))
private theorem rec1612 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[3,7,15],[9],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[443]? = some (⟨25,(10),[3,7,15],[9],194⟩) from rfl))
private theorem rec1632 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[3,7,15],[8],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[463]? = some (⟨25,(11),[3,7,15],[8],149⟩) from rfl))
private theorem rec1640 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[7],[9],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[471]? = some (⟨25,(11),[7],[9],220⟩) from rfl))
private theorem rec1656 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[3,7,15],[8],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[487]? = some (⟨25,(12),[3,7,15],[8],149⟩) from rfl))
private theorem rec1664 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[7],[9],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[495]? = some (⟨25,(12),[7],[9],220⟩) from rfl))
private theorem rec1680 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[3,7,15],[8],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[511]? = some (⟨25,(13),[3,7,15],[8],149⟩) from rfl))
private theorem rec1688 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[7],[9],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[519]? = some (⟨25,(13),[7],[9],220⟩) from rfl))
private theorem rec1704 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[3,7,15],[8],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[535]? = some (⟨25,(14),[3,7,15],[8],148⟩) from rfl))
private theorem rec1712 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[7],[9],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[543]? = some (⟨25,(14),[7],[9],219⟩) from rfl))
private theorem rec1728 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[559]? = some (⟨25,(15),[3,7,15],[8],150⟩) from rfl))
private theorem rec1729 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[3,7,15],[9],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[560]? = some (⟨25,(15),[3,7,15],[9],196⟩) from rfl))
private theorem rec1749 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[580]? = some (⟨25,(16),[3,7,15],[8],150⟩) from rfl))
private theorem rec1757 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[7],[9],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[588]? = some (⟨25,(16),[7],[9],221⟩) from rfl))
private theorem rec1773 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[604]? = some (⟨25,(17),[3,7,15],[8],150⟩) from rfl))
private theorem rec1781 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[7],[9],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[612]? = some (⟨25,(17),[7],[9],221⟩) from rfl))
private theorem rec1797 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[628]? = some (⟨25,(18),[3,7,15],[8],150⟩) from rfl))
private theorem rec1805 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[7],[9],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[636]? = some (⟨25,(18),[7],[9],221⟩) from rfl))
private theorem rec1821 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[3,7,15],[8],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[652]? = some (⟨25,(19),[3,7,15],[8],150⟩) from rfl))
private theorem rec1829 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[7],[9],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[660]? = some (⟨25,(19),[7],[9],221⟩) from rfl))
private theorem rec1845 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[676]? = some (⟨25,(20),[3,7,15],[8],151⟩) from rfl))
private theorem rec1846 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[3,7,15],[9],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[677]? = some (⟨25,(20),[3,7,15],[9],198⟩) from rfl))
private theorem rec1866 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[697]? = some (⟨25,(21),[3,7,15],[8],151⟩) from rfl))
private theorem rec1874 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[7],[9],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[705]? = some (⟨25,(21),[7],[9],222⟩) from rfl))
private theorem rec1890 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[721]? = some (⟨25,(22),[3,7,15],[8],151⟩) from rfl))
private theorem rec1898 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[7],[9],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[729]? = some (⟨25,(22),[7],[9],222⟩) from rfl))
private theorem rec1914 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[745]? = some (⟨25,(23),[3,7,15],[8],151⟩) from rfl))
private theorem rec1922 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[7],[9],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[753]? = some (⟨25,(23),[7],[9],222⟩) from rfl))
private theorem rec1938 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[3,7,15],[8],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[769]? = some (⟨25,(24),[3,7,15],[8],151⟩) from rfl))
private theorem rec1946 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[7],[9],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[777]? = some (⟨25,(24),[7],[9],222⟩) from rfl))
private theorem rec2362 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[3,7],[8,9],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1193]? = some (⟨30,(0),[3,7],[8,9],152⟩) from rfl))
private theorem rec2376 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[3,7],[8,9],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1207]? = some (⟨30,(1),[3,7],[8,9],153⟩) from rfl))
private theorem rec2395 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[3,7],[8],154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1226]? = some (⟨30,(2),[3,7],[8],154⟩) from rfl))
private theorem rec2396 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[3,7],[9],200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1227]? = some (⟨30,(2),[3,7],[9],200⟩) from rfl))
private theorem rec2415 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[3,7],[8],155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1246]? = some (⟨30,(3),[3,7],[8],155⟩) from rfl))
private theorem rec2421 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[7],[9],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1252]? = some (⟨30,(3),[7],[9],230⟩) from rfl))
private theorem rec2439 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[3,7],[8],156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1270]? = some (⟨30,(4),[3,7],[8],156⟩) from rfl))
private theorem rec2445 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[7],[9],231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[2]? = some (⟨30,(4),[7],[9],231⟩) from rfl))
private theorem rec2463 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[3,7],[8],155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[20]? = some (⟨30,(5),[3,7],[8],155⟩) from rfl))
private theorem rec2469 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[7],[9],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[26]? = some (⟨30,(5),[7],[9],230⟩) from rfl))
private theorem rec2487 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[3,7],[8],157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[44]? = some (⟨30,(6),[3,7],[8],157⟩) from rfl))
private theorem rec2493 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[7],[9],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[50]? = some (⟨30,(6),[7],[9],232⟩) from rfl))
private theorem rec2511 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[3,7],[8],157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[68]? = some (⟨30,(7),[3,7],[8],157⟩) from rfl))
private theorem rec2517 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[7],[9],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[74]? = some (⟨30,(7),[7],[9],232⟩) from rfl))
private theorem rec2535 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[3,7],[8],158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[92]? = some (⟨30,(8),[3,7],[8],158⟩) from rfl))
private theorem rec2541 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[7],[9],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[98]? = some (⟨30,(8),[7],[9],233⟩) from rfl))
private theorem rec2559 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[3,7],[8],158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[116]? = some (⟨30,(9),[3,7],[8],158⟩) from rfl))
private theorem rec2565 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[7],[9],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[122]? = some (⟨30,(9),[7],[9],233⟩) from rfl))
private theorem rec2906 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[3,7,15],[8,9],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[463]? = some (⟨36,(5),[3,7,15],[8,9],105⟩) from rfl))
private theorem rec2916 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[3,7,15],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[473]? = some (⟨36,(7),[3,7,15],[9],3⟩) from rfl))
private theorem rec2918 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[7],[8],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[475]? = some (⟨36,(7),[7],[8],105⟩) from rfl))
private theorem rec2930 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[3,7,15],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[487]? = some (⟨36,(8),[3,7,15],[9],3⟩) from rfl))
private theorem rec2932 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[7],[8],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[489]? = some (⟨36,(8),[7],[8],105⟩) from rfl))
private theorem rec2944 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[3,7],[8],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[501]? = some (⟨36,(9),[3,7],[8],105⟩) from rfl))
private theorem rec2945 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[3,7,15],[9],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[502]? = some (⟨36,(9),[3,7,15],[9],143⟩) from rfl))
private theorem rec2954 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[3,7,15],[8],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[511]? = some (⟨36,(15),[3,7,15],[8],3⟩) from rfl))
private theorem rec2956 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[7],[9],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[513]? = some (⟨36,(15),[7],[9],105⟩) from rfl))
private theorem rec2967 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[3,7,15],[9],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[524]? = some (⟨36,(16),[3,7,15],[9],3⟩) from rfl))
private theorem rec2969 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[7],[8],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[526]? = some (⟨36,(16),[7],[8],105⟩) from rfl))
private theorem rec2979 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[7],[8,9],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[536]? = some (⟨36,(17),[7],[8,9],48⟩) from rfl))
private theorem rec2990 (si parent : ℕ) (hs : si ∈ ([7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[7,15],[8,9],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[547]? = some (⟨36,(19),[7,15],[8,9],143⟩) from rfl))
private theorem rec14715 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(0),[3,7,15],[8],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1112]? = some (⟨335,(0),[3,7,15],[8],106⟩) from rfl))
private theorem rec14716 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(0),[3,7,15],[9],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1113]? = some (⟨335,(0),[3,7,15],[9],125⟩) from rfl))
private theorem rec14719 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(1),[3,7,15],[8],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1116]? = some (⟨335,(1),[3,7,15],[8],106⟩) from rfl))
private theorem rec14720 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(1),[3,7,15],[9],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1117]? = some (⟨335,(1),[3,7,15],[9],125⟩) from rfl))
private theorem rec14723 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(2),[3,7,15],[8],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1120]? = some (⟨335,(2),[3,7,15],[8],107⟩) from rfl))
private theorem rec14724 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(2),[3,7,15],[9],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1121]? = some (⟨335,(2),[3,7,15],[9],126⟩) from rfl))
private theorem rec14727 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(3),[3,7,15],[8],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1124]? = some (⟨335,(3),[3,7,15],[8],107⟩) from rfl))
private theorem rec14728 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(3),[3,7,15],[9],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1125]? = some (⟨335,(3),[3,7,15],[9],126⟩) from rfl))
private theorem rec14731 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(4),[3,7,15],[8],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1128]? = some (⟨335,(4),[3,7,15],[8],108⟩) from rfl))
private theorem rec14732 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(4),[3,7,15],[9],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1129]? = some (⟨335,(4),[3,7,15],[9],127⟩) from rfl))
private theorem rec14735 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(5),[3,7,15],[8],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1132]? = some (⟨335,(5),[3,7,15],[8],110⟩) from rfl))
private theorem rec14736 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(5),[3,7,15],[9],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1133]? = some (⟨335,(5),[3,7,15],[9],129⟩) from rfl))
private theorem rec14739 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(6),[3,7,15],[8],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1136]? = some (⟨335,(6),[3,7,15],[8],108⟩) from rfl))
private theorem rec14740 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(6),[3,7,15],[9],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1137]? = some (⟨335,(6),[3,7,15],[9],127⟩) from rfl))
private theorem rec14743 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(7),[3,7,15],[8],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1140]? = some (⟨335,(7),[3,7,15],[8],112⟩) from rfl))
private theorem rec14744 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(7),[3,7,15],[9],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1141]? = some (⟨335,(7),[3,7,15],[9],131⟩) from rfl))
private theorem rec14747 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(8),[3,7,15],[8],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1144]? = some (⟨335,(8),[3,7,15],[8],108⟩) from rfl))
private theorem rec14748 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(8),[3,7,15],[9],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1145]? = some (⟨335,(8),[3,7,15],[9],127⟩) from rfl))
private theorem rec14751 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 335 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(9),[3,7,15],[8],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1148]? = some (⟨335,(9),[3,7,15],[8],110⟩) from rfl))
private theorem rec14752 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 335 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(9),[3,7,15],[9],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1149]? = some (⟨335,(9),[3,7,15],[9],129⟩) from rfl))
private theorem rec14755 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(0),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1152]? = some (⟨339,(0),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14758 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(1),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1155]? = some (⟨339,(1),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14761 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(2),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1158]? = some (⟨339,(2),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14764 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(3),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1161]? = some (⟨339,(3),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14767 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(4),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1164]? = some (⟨339,(4),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14770 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(5),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1167]? = some (⟨339,(5),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14773 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(6),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1170]? = some (⟨339,(6),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14776 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(7),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1173]? = some (⟨339,(7),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14779 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(8),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1176]? = some (⟨339,(8),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14782 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 339 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(9),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1179]? = some (⟨339,(9),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14786 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(0),[3,7],[8],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1183]? = some (⟨343,(0),[3,7],[8],113⟩) from rfl))
private theorem rec14787 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(0),[3,7],[9],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1184]? = some (⟨343,(0),[3,7],[9],132⟩) from rfl))
private theorem rec14790 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(1),[3,7],[8],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1187]? = some (⟨343,(1),[3,7],[8],113⟩) from rfl))
private theorem rec14791 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(1),[3,7],[9],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1188]? = some (⟨343,(1),[3,7],[9],132⟩) from rfl))
private theorem rec14794 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(2),[3,7],[8],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1191]? = some (⟨343,(2),[3,7],[8],114⟩) from rfl))
private theorem rec14795 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(2),[3,7],[9],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1192]? = some (⟨343,(2),[3,7],[9],133⟩) from rfl))
private theorem rec14798 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(3),[3,7],[8],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1195]? = some (⟨343,(3),[3,7],[8],114⟩) from rfl))
private theorem rec14799 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(3),[3,7],[9],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1196]? = some (⟨343,(3),[3,7],[9],133⟩) from rfl))
private theorem rec14802 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(4),[3,7],[8],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1199]? = some (⟨343,(4),[3,7],[8],115⟩) from rfl))
private theorem rec14803 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(4),[3,7],[9],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1200]? = some (⟨343,(4),[3,7],[9],134⟩) from rfl))
private theorem rec14806 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(5),[3,7],[8],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1203]? = some (⟨343,(5),[3,7],[8],117⟩) from rfl))
private theorem rec14807 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(5),[3,7],[9],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1204]? = some (⟨343,(5),[3,7],[9],136⟩) from rfl))
private theorem rec14810 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(6),[3,7],[8],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1207]? = some (⟨343,(6),[3,7],[8],115⟩) from rfl))
private theorem rec14811 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(6),[3,7],[9],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1208]? = some (⟨343,(6),[3,7],[9],134⟩) from rfl))
private theorem rec14814 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(7),[3,7],[8],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1211]? = some (⟨343,(7),[3,7],[8],119⟩) from rfl))
private theorem rec14815 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(7),[3,7],[9],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1212]? = some (⟨343,(7),[3,7],[9],138⟩) from rfl))
private theorem rec14818 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(8),[3,7],[8],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1215]? = some (⟨343,(8),[3,7],[8],115⟩) from rfl))
private theorem rec14819 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(8),[3,7],[9],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1216]? = some (⟨343,(8),[3,7],[9],134⟩) from rfl))
private theorem rec14822 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 343 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(9),[3,7],[8],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1219]? = some (⟨343,(9),[3,7],[8],117⟩) from rfl))
private theorem rec14823 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 343 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(9),[3,7],[9],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1220]? = some (⟨343,(9),[3,7],[9],136⟩) from rfl))
private theorem rec14826 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 347 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(0),[7],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1223]? = some (⟨347,(0),[7],[8,9],2⟩) from rfl))
private theorem rec14828 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 347 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(1),[3,7,15],[8,9],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1225]? = some (⟨347,(1),[3,7,15],[8,9],2⟩) from rfl))
private theorem rec14831 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 347 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(2),[3,7,15],[8,9],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1228]? = some (⟨347,(2),[3,7,15],[8,9],159⟩) from rfl))
private theorem rec14834 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8, 9] : List ℕ)) : section14Recorded section14Catalog si parent 347 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(3),[3,7,15],[8,9],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1231]? = some (⟨347,(3),[3,7,15],[8,9],99⟩) from rfl))
private theorem rec14838 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 349 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(0),[3,7],[8],121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1235]? = some (⟨349,(0),[3,7],[8],121⟩) from rfl))
private theorem rec14839 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 349 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(0),[3,7],[9],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1236]? = some (⟨349,(0),[3,7],[9],139⟩) from rfl))
private theorem rec14842 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 349 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(1),[3,7],[8],122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1239]? = some (⟨349,(1),[3,7],[8],122⟩) from rfl))
private theorem rec14843 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 349 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(1),[3,7],[9],140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1240]? = some (⟨349,(1),[3,7],[9],140⟩) from rfl))
private theorem rec14846 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 349 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(2),[3,7],[8],931⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1243]? = some (⟨349,(2),[3,7],[8],931⟩) from rfl))
private theorem rec14847 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 349 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(2),[3,7],[9],932⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1244]? = some (⟨349,(2),[3,7],[9],932⟩) from rfl))
private theorem rec14850 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 349 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(3),[3,7],[8],124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1247]? = some (⟨349,(3),[3,7],[8],124⟩) from rfl))
private theorem rec14851 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 349 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(3),[3,7],[9],142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1248]? = some (⟨349,(3),[3,7],[9],142⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 7).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 7)).drop 0).take 16, section14Recorded section14Catalog 7 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 7).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(334,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(337,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(342,⟨([3],[]),true,([3],[]),false,false,[]⟩),(343,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(344,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(345,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(346,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(348,⟨([2],[]),true,([3],[]),false,false,[]⟩),(349,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(350,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec416 7 0 (by decide) (by decide)
  · left
    exact rec417 7 1 (by decide) (by decide)
  · left
    exact rec418 7 2 (by decide) (by decide)
  · left
    exact rec419 7 3 (by decide) (by decide)
  · left
    exact rec420 7 4 (by decide) (by decide)
  · left
    exact rec415 7 5 (by decide) (by decide)
  · left
    exact rec421 7 6 (by decide) (by decide)
  · left
    exact rec422 7 7 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(334,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(337,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(342,⟨([3],[]),true,([3],[]),false,false,[]⟩),(343,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(344,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(345,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(346,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(348,⟨([2],[]),true,([3],[]),false,false,[]⟩),(349,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(350,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
        exact rec14715 7 8 (by decide) (by decide)
      · right
        exact rec14719 7 8 (by decide) (by decide)
      · right
        exact rec14723 7 8 (by decide) (by decide)
      · right
        exact rec14727 7 8 (by decide) (by decide)
      · right
        exact rec14731 7 8 (by decide) (by decide)
      · right
        exact rec14735 7 8 (by decide) (by decide)
      · right
        exact rec14739 7 8 (by decide) (by decide)
      · right
        exact rec14743 7 8 (by decide) (by decide)
      · right
        exact rec14747 7 8 (by decide) (by decide)
      · right
        exact rec14751 7 8 (by decide) (by decide)
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
        exact rec925 7 8 (by decide) (by decide)
      · right
        exact rec936 7 8 (by decide) (by decide)
      · right
        exact rec947 7 8 (by decide) (by decide)
      · right
        exact rec958 7 8 (by decide) (by decide)
      · right
        exact rec969 7 8 (by decide) (by decide)
      · right
        exact rec980 7 8 (by decide) (by decide)
      · right
        exact rec991 7 8 (by decide) (by decide)
      · right
        exact rec1002 7 8 (by decide) (by decide)
      · right
        exact rec1013 7 8 (by decide) (by decide)
      · right
        exact rec1024 7 8 (by decide) (by decide)
      · right
        exact rec1035 7 8 (by decide) (by decide)
      · right
        exact rec1046 7 8 (by decide) (by decide)
      · right
        exact rec1057 7 8 (by decide) (by decide)
      · right
        exact rec1068 7 8 (by decide) (by decide)
      · right
        exact rec1079 7 8 (by decide) (by decide)
      · right
        exact rec1090 7 8 (by decide) (by decide)
      · right
        exact rec1101 7 8 (by decide) (by decide)
      · right
        exact rec1112 7 8 (by decide) (by decide)
      · right
        exact rec1123 7 8 (by decide) (by decide)
      · right
        exact rec1134 7 8 (by decide) (by decide)
      · right
        exact rec1145 7 8 (by decide) (by decide)
      · right
        exact rec1156 7 8 (by decide) (by decide)
      · right
        exact rec1167 7 8 (by decide) (by decide)
      · right
        exact rec1178 7 8 (by decide) (by decide)
      · right
        exact rec1189 7 8 (by decide) (by decide)
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
        exact rec14755 7 8 (by decide) (by decide)
      · right
        exact rec14758 7 8 (by decide) (by decide)
      · right
        exact rec14761 7 8 (by decide) (by decide)
      · right
        exact rec14764 7 8 (by decide) (by decide)
      · right
        exact rec14767 7 8 (by decide) (by decide)
      · right
        exact rec14770 7 8 (by decide) (by decide)
      · right
        exact rec14773 7 8 (by decide) (by decide)
      · right
        exact rec14776 7 8 (by decide) (by decide)
      · right
        exact rec14779 7 8 (by decide) (by decide)
      · right
        exact rec14782 7 8 (by decide) (by decide)
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
        exact rec1377 7 8 (by decide) (by decide)
      · right
        exact rec1398 7 8 (by decide) (by decide)
      · right
        exact rec1422 7 8 (by decide) (by decide)
      · right
        exact rec1446 7 8 (by decide) (by decide)
      · right
        exact rec1470 7 8 (by decide) (by decide)
      · right
        exact rec1494 7 8 (by decide) (by decide)
      · right
        exact rec1515 7 8 (by decide) (by decide)
      · right
        exact rec1539 7 8 (by decide) (by decide)
      · right
        exact rec1563 7 8 (by decide) (by decide)
      · right
        exact rec1587 7 8 (by decide) (by decide)
      · right
        exact rec1611 7 8 (by decide) (by decide)
      · right
        exact rec1632 7 8 (by decide) (by decide)
      · right
        exact rec1656 7 8 (by decide) (by decide)
      · right
        exact rec1680 7 8 (by decide) (by decide)
      · right
        exact rec1704 7 8 (by decide) (by decide)
      · right
        exact rec1728 7 8 (by decide) (by decide)
      · right
        exact rec1749 7 8 (by decide) (by decide)
      · right
        exact rec1773 7 8 (by decide) (by decide)
      · right
        exact rec1797 7 8 (by decide) (by decide)
      · right
        exact rec1821 7 8 (by decide) (by decide)
      · right
        exact rec1845 7 8 (by decide) (by decide)
      · right
        exact rec1866 7 8 (by decide) (by decide)
      · right
        exact rec1890 7 8 (by decide) (by decide)
      · right
        exact rec1914 7 8 (by decide) (by decide)
      · right
        exact rec1938 7 8 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 342)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 343)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14786 7 8 (by decide) (by decide)
      · right
        exact rec14790 7 8 (by decide) (by decide)
      · right
        exact rec14794 7 8 (by decide) (by decide)
      · right
        exact rec14798 7 8 (by decide) (by decide)
      · right
        exact rec14802 7 8 (by decide) (by decide)
      · right
        exact rec14806 7 8 (by decide) (by decide)
      · right
        exact rec14810 7 8 (by decide) (by decide)
      · right
        exact rec14814 7 8 (by decide) (by decide)
      · right
        exact rec14818 7 8 (by decide) (by decide)
      · right
        exact rec14822 7 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 344)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 30)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2362 7 8 (by decide) (by decide)
      · right
        exact rec2376 7 8 (by decide) (by decide)
      · right
        exact rec2395 7 8 (by decide) (by decide)
      · right
        exact rec2415 7 8 (by decide) (by decide)
      · right
        exact rec2439 7 8 (by decide) (by decide)
      · right
        exact rec2463 7 8 (by decide) (by decide)
      · right
        exact rec2487 7 8 (by decide) (by decide)
      · right
        exact rec2511 7 8 (by decide) (by decide)
      · right
        exact rec2535 7 8 (by decide) (by decide)
      · right
        exact rec2559 7 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 345)).length = 10 := by decide +kernel
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
        exact rec14826 7 8 (by decide) (by decide)
      · right
        exact rec14828 7 8 (by decide) (by decide)
      · right
        exact rec14831 7 8 (by decide) (by decide)
      · right
        exact rec14834 7 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 348)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 349)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14838 7 8 (by decide) (by decide)
      · right
        exact rec14842 7 8 (by decide) (by decide)
      · right
        exact rec14846 7 8 (by decide) (by decide)
      · right
        exact rec14850 7 8 (by decide) (by decide)
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
        exact rec2906 7 8 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2918 7 8 (by decide) (by decide)
      · right
        exact rec2932 7 8 (by decide) (by decide)
      · right
        exact rec2944 7 8 (by decide) (by decide)
      · left
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
        exact rec2954 7 8 (by decide) (by decide)
      · right
        exact rec2969 7 8 (by decide) (by decide)
      · right
        exact rec2979 7 8 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2990 7 8 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 350)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · right
    intro gs hgs
    change gs ∈ [(334,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(337,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(342,⟨([3],[]),true,([3],[]),false,false,[]⟩),(343,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(344,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(345,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(346,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(348,⟨([2],[]),true,([3],[]),false,false,[]⟩),(349,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(350,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
        exact rec14716 7 9 (by decide) (by decide)
      · right
        exact rec14720 7 9 (by decide) (by decide)
      · right
        exact rec14724 7 9 (by decide) (by decide)
      · right
        exact rec14728 7 9 (by decide) (by decide)
      · right
        exact rec14732 7 9 (by decide) (by decide)
      · right
        exact rec14736 7 9 (by decide) (by decide)
      · right
        exact rec14740 7 9 (by decide) (by decide)
      · right
        exact rec14744 7 9 (by decide) (by decide)
      · right
        exact rec14748 7 9 (by decide) (by decide)
      · right
        exact rec14752 7 9 (by decide) (by decide)
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
        exact rec925 7 9 (by decide) (by decide)
      · right
        exact rec936 7 9 (by decide) (by decide)
      · right
        exact rec947 7 9 (by decide) (by decide)
      · right
        exact rec958 7 9 (by decide) (by decide)
      · right
        exact rec969 7 9 (by decide) (by decide)
      · right
        exact rec980 7 9 (by decide) (by decide)
      · right
        exact rec991 7 9 (by decide) (by decide)
      · right
        exact rec1002 7 9 (by decide) (by decide)
      · right
        exact rec1013 7 9 (by decide) (by decide)
      · right
        exact rec1024 7 9 (by decide) (by decide)
      · right
        exact rec1035 7 9 (by decide) (by decide)
      · right
        exact rec1046 7 9 (by decide) (by decide)
      · right
        exact rec1057 7 9 (by decide) (by decide)
      · right
        exact rec1068 7 9 (by decide) (by decide)
      · right
        exact rec1079 7 9 (by decide) (by decide)
      · right
        exact rec1090 7 9 (by decide) (by decide)
      · right
        exact rec1101 7 9 (by decide) (by decide)
      · right
        exact rec1112 7 9 (by decide) (by decide)
      · right
        exact rec1123 7 9 (by decide) (by decide)
      · right
        exact rec1134 7 9 (by decide) (by decide)
      · right
        exact rec1145 7 9 (by decide) (by decide)
      · right
        exact rec1156 7 9 (by decide) (by decide)
      · right
        exact rec1167 7 9 (by decide) (by decide)
      · right
        exact rec1178 7 9 (by decide) (by decide)
      · right
        exact rec1189 7 9 (by decide) (by decide)
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
        exact rec14755 7 9 (by decide) (by decide)
      · right
        exact rec14758 7 9 (by decide) (by decide)
      · right
        exact rec14761 7 9 (by decide) (by decide)
      · right
        exact rec14764 7 9 (by decide) (by decide)
      · right
        exact rec14767 7 9 (by decide) (by decide)
      · right
        exact rec14770 7 9 (by decide) (by decide)
      · right
        exact rec14773 7 9 (by decide) (by decide)
      · right
        exact rec14776 7 9 (by decide) (by decide)
      · right
        exact rec14779 7 9 (by decide) (by decide)
      · right
        exact rec14782 7 9 (by decide) (by decide)
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
        exact rec1378 7 9 (by decide) (by decide)
      · right
        exact rec1406 7 9 (by decide) (by decide)
      · right
        exact rec1430 7 9 (by decide) (by decide)
      · right
        exact rec1454 7 9 (by decide) (by decide)
      · right
        exact rec1478 7 9 (by decide) (by decide)
      · right
        exact rec1495 7 9 (by decide) (by decide)
      · right
        exact rec1523 7 9 (by decide) (by decide)
      · right
        exact rec1547 7 9 (by decide) (by decide)
      · right
        exact rec1571 7 9 (by decide) (by decide)
      · right
        exact rec1595 7 9 (by decide) (by decide)
      · right
        exact rec1612 7 9 (by decide) (by decide)
      · right
        exact rec1640 7 9 (by decide) (by decide)
      · right
        exact rec1664 7 9 (by decide) (by decide)
      · right
        exact rec1688 7 9 (by decide) (by decide)
      · right
        exact rec1712 7 9 (by decide) (by decide)
      · right
        exact rec1729 7 9 (by decide) (by decide)
      · right
        exact rec1757 7 9 (by decide) (by decide)
      · right
        exact rec1781 7 9 (by decide) (by decide)
      · right
        exact rec1805 7 9 (by decide) (by decide)
      · right
        exact rec1829 7 9 (by decide) (by decide)
      · right
        exact rec1846 7 9 (by decide) (by decide)
      · right
        exact rec1874 7 9 (by decide) (by decide)
      · right
        exact rec1898 7 9 (by decide) (by decide)
      · right
        exact rec1922 7 9 (by decide) (by decide)
      · right
        exact rec1946 7 9 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 342)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 343)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14787 7 9 (by decide) (by decide)
      · right
        exact rec14791 7 9 (by decide) (by decide)
      · right
        exact rec14795 7 9 (by decide) (by decide)
      · right
        exact rec14799 7 9 (by decide) (by decide)
      · right
        exact rec14803 7 9 (by decide) (by decide)
      · right
        exact rec14807 7 9 (by decide) (by decide)
      · right
        exact rec14811 7 9 (by decide) (by decide)
      · right
        exact rec14815 7 9 (by decide) (by decide)
      · right
        exact rec14819 7 9 (by decide) (by decide)
      · right
        exact rec14823 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 344)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 30)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2362 7 9 (by decide) (by decide)
      · right
        exact rec2376 7 9 (by decide) (by decide)
      · right
        exact rec2396 7 9 (by decide) (by decide)
      · right
        exact rec2421 7 9 (by decide) (by decide)
      · right
        exact rec2445 7 9 (by decide) (by decide)
      · right
        exact rec2469 7 9 (by decide) (by decide)
      · right
        exact rec2493 7 9 (by decide) (by decide)
      · right
        exact rec2517 7 9 (by decide) (by decide)
      · right
        exact rec2541 7 9 (by decide) (by decide)
      · right
        exact rec2565 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 345)).length = 10 := by decide +kernel
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
        exact rec14826 7 9 (by decide) (by decide)
      · right
        exact rec14828 7 9 (by decide) (by decide)
      · right
        exact rec14831 7 9 (by decide) (by decide)
      · right
        exact rec14834 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 348)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 349)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14839 7 9 (by decide) (by decide)
      · right
        exact rec14843 7 9 (by decide) (by decide)
      · right
        exact rec14847 7 9 (by decide) (by decide)
      · right
        exact rec14851 7 9 (by decide) (by decide)
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
        exact rec2906 7 9 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2916 7 9 (by decide) (by decide)
      · right
        exact rec2930 7 9 (by decide) (by decide)
      · right
        exact rec2945 7 9 (by decide) (by decide)
      · left
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
        exact rec2956 7 9 (by decide) (by decide)
      · right
        exact rec2967 7 9 (by decide) (by decide)
      · right
        exact rec2979 7 9 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2990 7 9 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 350)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec423 7 10 (by decide) (by decide)
  · left
    exact rec451 7 11 (by decide) (by decide)
  · left
    exact rec425 7 12 (by decide) (by decide)
  · left
    exact rec424 7 13 (by decide) (by decide)
  · left
    exact rec426 7 14 (by decide) (by decide)
  · left
    exact rec427 7 15 (by decide) (by decide)
end Section14Coverage_7_1_p0_16

#print axioms solution
