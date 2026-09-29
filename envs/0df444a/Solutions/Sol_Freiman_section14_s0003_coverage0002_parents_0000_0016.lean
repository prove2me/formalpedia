-- Prove2me | solution 1 for Freiman.section14_s0003_coverage0002_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T11:52:36.436963+00:00
-- url     : https://prove2.me/submissions/c9b703a1-7aca-4de8-8f9b-c83ccf28ef5c

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
namespace Section14Coverage_3_2_p0_16
private theorem rec2993 (si parent : ℕ) (hs : si ∈ ([1, 2, 3, 5, 6, 7, 9, 10, 13, 14, 15] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[550]? = some (⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩) from rfl))
private theorem rec3019 (si parent : ℕ) (hs : si ∈ ([1, 3, 5, 7, 9, 11, 13, 15] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,3,5,7,9,11,13,15],[0],246⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[576]? = some (⟨38,(-1),[1,3,5,7,9,11,13,15],[0],246⟩) from rfl))
private theorem rec3036 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,4,7,8,12,15,16],[5],248⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[593]? = some (⟨38,(-1),[3,4,7,8,12,15,16],[5],248⟩) from rfl))
private theorem rec3037 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,7,15],[2],60⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[594]? = some (⟨38,(-1),[3,7,15],[2],60⟩) from rfl))
private theorem rec3038 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,7,15],[6],68⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[595]? = some (⟨38,(-1),[3,7,15],[6],68⟩) from rfl))
private theorem rec3039 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,7,15],[14],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[596]? = some (⟨38,(-1),[3,7,15],[14],243⟩) from rfl))
private theorem rec3040 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,7,15],[3],246⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[597]? = some (⟨38,(-1),[3,7,15],[3],246⟩) from rfl))
private theorem rec3041 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([4, 7] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,7,15],[4,7],248⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[598]? = some (⟨38,(-1),[3,7,15],[4,7],248⟩) from rfl))
private theorem rec3042 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,7,15],[8],250⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[599]? = some (⟨38,(-1),[3,7,15],[8],250⟩) from rfl))
private theorem rec3043 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([12, 13, 15] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,7,15],[12,13,15],340⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[600]? = some (⟨38,(-1),[3,7,15],[12,13,15],340⟩) from rfl))
private theorem rec3044 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,15],[9],252⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[601]? = some (⟨38,(-1),[3,15],[9],252⟩) from rfl))
private theorem rec3215 (si parent : ℕ) (hs : si ∈ ([3, 7, 8, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[3,7,8,15],[10],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[772]? = some (⟨42,(0),[3,7,8,15],[10],253⟩) from rfl))
private theorem rec3216 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[3,15],[11],288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[773]? = some (⟨42,(0),[3,15],[11],288⟩) from rfl))
private theorem rec3226 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[3,4,7,8,15,16],[10],254⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[783]? = some (⟨42,(1),[3,4,7,8,15,16],[10],254⟩) from rfl))
private theorem rec3227 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[3,15],[11],289⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[784]? = some (⟨42,(1),[3,15],[11],289⟩) from rfl))
private theorem rec3236 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[3,4,7,8,15,16],[10],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[793]? = some (⟨42,(2),[3,4,7,8,15,16],[10],253⟩) from rfl))
private theorem rec3237 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[3,15],[11],288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[794]? = some (⟨42,(2),[3,15],[11],288⟩) from rfl))
private theorem rec3246 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[3,4,7,8,15,16],[10],255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[803]? = some (⟨42,(3),[3,4,7,8,15,16],[10],255⟩) from rfl))
private theorem rec3247 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[3,15],[11],290⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[804]? = some (⟨42,(3),[3,15],[11],290⟩) from rfl))
private theorem rec3256 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[3,4,7,8,15,16],[10],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[813]? = some (⟨42,(4),[3,4,7,8,15,16],[10],256⟩) from rfl))
private theorem rec3257 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[3,15],[11],291⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[814]? = some (⟨42,(4),[3,15],[11],291⟩) from rfl))
private theorem rec3266 (si parent : ℕ) (hs : si ∈ ([3, 7, 8, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[3,7,8,15],[10],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[823]? = some (⟨42,(5),[3,7,8,15],[10],253⟩) from rfl))
private theorem rec3267 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[3,15],[11],288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[824]? = some (⟨42,(5),[3,15],[11],288⟩) from rfl))
private theorem rec3277 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[3,4,7,8,15,16],[10],254⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[834]? = some (⟨42,(6),[3,4,7,8,15,16],[10],254⟩) from rfl))
private theorem rec3278 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[3,15],[11],289⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[835]? = some (⟨42,(6),[3,15],[11],289⟩) from rfl))
private theorem rec3287 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[3,4,7,8,15,16],[10],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[844]? = some (⟨42,(7),[3,4,7,8,15,16],[10],253⟩) from rfl))
private theorem rec3288 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[3,15],[11],288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[845]? = some (⟨42,(7),[3,15],[11],288⟩) from rfl))
private theorem rec3297 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[3,4,7,8,15,16],[10],255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[854]? = some (⟨42,(8),[3,4,7,8,15,16],[10],255⟩) from rfl))
private theorem rec3298 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[3,15],[11],290⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[855]? = some (⟨42,(8),[3,15],[11],290⟩) from rfl))
private theorem rec3307 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[3,4,7,8,15,16],[10],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[864]? = some (⟨42,(9),[3,4,7,8,15,16],[10],256⟩) from rfl))
private theorem rec3308 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[3,15],[11],291⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[865]? = some (⟨42,(9),[3,15],[11],291⟩) from rfl))
private theorem rec3317 (si parent : ℕ) (hs : si ∈ ([3, 7, 8, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[3,7,8,15],[10],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[874]? = some (⟨42,(10),[3,7,8,15],[10],257⟩) from rfl))
private theorem rec3318 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[3,15],[11],292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[875]? = some (⟨42,(10),[3,15],[11],292⟩) from rfl))
private theorem rec3328 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[3,4,7,8,15,16],[10],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[885]? = some (⟨42,(11),[3,4,7,8,15,16],[10],257⟩) from rfl))
private theorem rec3329 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[3,15],[11],292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[886]? = some (⟨42,(11),[3,15],[11],292⟩) from rfl))
private theorem rec3338 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[3,4,7,8,15,16],[10],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[895]? = some (⟨42,(12),[3,4,7,8,15,16],[10],257⟩) from rfl))
private theorem rec3339 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[3,15],[11],292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[896]? = some (⟨42,(12),[3,15],[11],292⟩) from rfl))
private theorem rec3348 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[3,4,7,8,15,16],[10],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[905]? = some (⟨42,(13),[3,4,7,8,15,16],[10],257⟩) from rfl))
private theorem rec3349 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[3,15],[11],292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[906]? = some (⟨42,(13),[3,15],[11],292⟩) from rfl))
private theorem rec3358 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[3,4,7,8,15,16],[10],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[915]? = some (⟨42,(14),[3,4,7,8,15,16],[10],256⟩) from rfl))
private theorem rec3359 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[3,15],[11],291⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[916]? = some (⟨42,(14),[3,15],[11],291⟩) from rfl))
private theorem rec3368 (si parent : ℕ) (hs : si ∈ ([3, 7, 8, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[3,7,8,15],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[925]? = some (⟨42,(15),[3,7,8,15],[10],258⟩) from rfl))
private theorem rec3369 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[3,15],[11],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[926]? = some (⟨42,(15),[3,15],[11],293⟩) from rfl))
private theorem rec3379 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[3,4,7,8,15,16],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[936]? = some (⟨42,(16),[3,4,7,8,15,16],[10],258⟩) from rfl))
private theorem rec3380 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[3,15],[11],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[937]? = some (⟨42,(16),[3,15],[11],293⟩) from rfl))
private theorem rec3389 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[3,4,7,8,15,16],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[946]? = some (⟨42,(17),[3,4,7,8,15,16],[10],258⟩) from rfl))
private theorem rec3390 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[3,15],[11],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[947]? = some (⟨42,(17),[3,15],[11],293⟩) from rfl))
private theorem rec3399 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[3,4,7,8,15,16],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[956]? = some (⟨42,(18),[3,4,7,8,15,16],[10],258⟩) from rfl))
private theorem rec3400 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[3,15],[11],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[957]? = some (⟨42,(18),[3,15],[11],293⟩) from rfl))
private theorem rec3409 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[3,4,7,8,15,16],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[966]? = some (⟨42,(19),[3,4,7,8,15,16],[10],258⟩) from rfl))
private theorem rec3410 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[3,15],[11],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[967]? = some (⟨42,(19),[3,15],[11],293⟩) from rfl))
private theorem rec3419 (si parent : ℕ) (hs : si ∈ ([3, 7, 8, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[3,7,8,15],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[976]? = some (⟨42,(20),[3,7,8,15],[10],259⟩) from rfl))
private theorem rec3420 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[3,15],[11],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[977]? = some (⟨42,(20),[3,15],[11],294⟩) from rfl))
private theorem rec3430 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[3,4,7,8,15,16],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[987]? = some (⟨42,(21),[3,4,7,8,15,16],[10],259⟩) from rfl))
private theorem rec3431 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[3,15],[11],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[988]? = some (⟨42,(21),[3,15],[11],294⟩) from rfl))
private theorem rec3440 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[3,4,7,8,15,16],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[997]? = some (⟨42,(22),[3,4,7,8,15,16],[10],259⟩) from rfl))
private theorem rec3441 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[3,15],[11],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[998]? = some (⟨42,(22),[3,15],[11],294⟩) from rfl))
private theorem rec3450 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[3,4,7,8,15,16],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1007]? = some (⟨42,(23),[3,4,7,8,15,16],[10],259⟩) from rfl))
private theorem rec3451 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[3,15],[11],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1008]? = some (⟨42,(23),[3,15],[11],294⟩) from rfl))
private theorem rec3460 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[3,4,7,8,15,16],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1017]? = some (⟨42,(24),[3,4,7,8,15,16],[10],259⟩) from rfl))
private theorem rec3461 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[3,15],[11],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1018]? = some (⟨42,(24),[3,15],[11],294⟩) from rfl))
private theorem rec3568 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[3,4,7,8,12,15,16],[10],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1125]? = some (⟨47,(0),[3,4,7,8,12,15,16],[10],189⟩) from rfl))
private theorem rec3569 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[3,7,15],[11],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1126]? = some (⟨47,(0),[3,7,15],[11],189⟩) from rfl))
private theorem rec3578 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[3,4,7,8,12,15,16],[10],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1135]? = some (⟨47,(1),[3,4,7,8,12,15,16],[10],260⟩) from rfl))
private theorem rec3579 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[3,7,15],[11],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1136]? = some (⟨47,(1),[3,7,15],[11],260⟩) from rfl))
private theorem rec3588 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[3,4,7,8,12,15,16],[10],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1145]? = some (⟨47,(2),[3,4,7,8,12,15,16],[10],261⟩) from rfl))
private theorem rec3589 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[3,7,15],[11],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1146]? = some (⟨47,(2),[3,7,15],[11],261⟩) from rfl))
private theorem rec3599 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[3,4,7,8,12,15,16],[10],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1156]? = some (⟨47,(3),[3,4,7,8,12,15,16],[10],262⟩) from rfl))
private theorem rec3600 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[3,7,15],[11],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1157]? = some (⟨47,(3),[3,7,15],[11],262⟩) from rfl))
private theorem rec3610 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[3,4,7,8,12,15,16],[10],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1167]? = some (⟨47,(4),[3,4,7,8,12,15,16],[10],263⟩) from rfl))
private theorem rec3611 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[3,7,15],[11],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1168]? = some (⟨47,(4),[3,7,15],[11],263⟩) from rfl))
private theorem rec3621 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[3,4,7,8,12,15,16],[10],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1178]? = some (⟨47,(5),[3,4,7,8,12,15,16],[10],189⟩) from rfl))
private theorem rec3622 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[3,7,15],[11],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1179]? = some (⟨47,(5),[3,7,15],[11],189⟩) from rfl))
private theorem rec3631 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[3,4,7,8,12,15,16],[10],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1188]? = some (⟨47,(6),[3,4,7,8,12,15,16],[10],260⟩) from rfl))
private theorem rec3632 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[3,7,15],[11],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1189]? = some (⟨47,(6),[3,7,15],[11],260⟩) from rfl))
private theorem rec3643 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[3,4,7,8,12,15,16],[10],264⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[4]? = some (⟨47,(7),[3,4,7,8,12,15,16],[10],264⟩) from rfl))
private theorem rec3644 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[3,15],[11],295⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[5]? = some (⟨47,(7),[3,15],[11],295⟩) from rfl))
private theorem rec3659 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[3,4,7,15,16],[10],265⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[20]? = some (⟨47,(8),[3,4,7,15,16],[10],265⟩) from rfl))
private theorem rec3660 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[3,7],[11],265⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[21]? = some (⟨47,(8),[3,7],[11],265⟩) from rfl))
private theorem rec3677 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[3,4,7,8,12,15,16],[10],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[38]? = some (⟨47,(9),[3,4,7,8,12,15,16],[10],266⟩) from rfl))
private theorem rec3678 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[3,15],[11],297⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[39]? = some (⟨47,(9),[3,15],[11],297⟩) from rfl))
private theorem rec3691 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[3,4,7,8,12,15,16],[10],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[52]? = some (⟨47,(10),[3,4,7,8,12,15,16],[10],194⟩) from rfl))
private theorem rec3692 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[3,7,15],[11],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[53]? = some (⟨47,(10),[3,7,15],[11],194⟩) from rfl))
private theorem rec3701 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[3,4,7,8,12,15,16],[10],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[62]? = some (⟨47,(11),[3,4,7,8,12,15,16],[10],267⟩) from rfl))
private theorem rec3702 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[3,7,15],[11],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[63]? = some (⟨47,(11),[3,7,15],[11],267⟩) from rfl))
private theorem rec3713 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[3,4,7,8,12,15,16],[10],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[74]? = some (⟨47,(12),[3,4,7,8,12,15,16],[10],268⟩) from rfl))
private theorem rec3714 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[3,15],[11],298⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[75]? = some (⟨47,(12),[3,15],[11],298⟩) from rfl))
private theorem rec3729 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[3,4,7,15,16],[10],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[90]? = some (⟨47,(13),[3,4,7,15,16],[10],268⟩) from rfl))
private theorem rec3730 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[3,15],[11],298⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[91]? = some (⟨47,(13),[3,15],[11],298⟩) from rfl))
private theorem rec3747 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[3,4,7,8,12,15,16],[10],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[108]? = some (⟨47,(14),[3,4,7,8,12,15,16],[10],266⟩) from rfl))
private theorem rec3748 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[3,15],[11],297⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[109]? = some (⟨47,(14),[3,15],[11],297⟩) from rfl))
private theorem rec3761 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[3,4,7,8,12,15,16],[10],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[122]? = some (⟨47,(15),[3,4,7,8,12,15,16],[10],196⟩) from rfl))
private theorem rec3762 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[3,7,15],[11],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[123]? = some (⟨47,(15),[3,7,15],[11],196⟩) from rfl))
private theorem rec3771 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[3,4,7,8,12,15,16],[10],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[132]? = some (⟨47,(16),[3,4,7,8,12,15,16],[10],269⟩) from rfl))
private theorem rec3772 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[3,7,15],[11],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[133]? = some (⟨47,(16),[3,7,15],[11],269⟩) from rfl))
private theorem rec3783 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[3,4,7,8,12,15,16],[10],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[144]? = some (⟨47,(17),[3,4,7,8,12,15,16],[10],270⟩) from rfl))
private theorem rec3784 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[3,15],[11],299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[145]? = some (⟨47,(17),[3,15],[11],299⟩) from rfl))
private theorem rec3798 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[3,4,7,15,16],[10],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[159]? = some (⟨47,(18),[3,4,7,15,16],[10],270⟩) from rfl))
private theorem rec3799 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[3,15],[11],299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[160]? = some (⟨47,(18),[3,15],[11],299⟩) from rfl))
private theorem rec3815 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[3,4,7,8,12,15,16],[10],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[176]? = some (⟨47,(19),[3,4,7,8,12,15,16],[10],270⟩) from rfl))
private theorem rec3816 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[3,15],[11],299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[177]? = some (⟨47,(19),[3,15],[11],299⟩) from rfl))
private theorem rec3828 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[3,4,7,8,12,15,16],[10],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[189]? = some (⟨47,(20),[3,4,7,8,12,15,16],[10],198⟩) from rfl))
private theorem rec3829 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[3,7,15],[11],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[190]? = some (⟨47,(20),[3,7,15],[11],198⟩) from rfl))
private theorem rec3838 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[3,4,7,8,12,15,16],[10],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[199]? = some (⟨47,(21),[3,4,7,8,12,15,16],[10],271⟩) from rfl))
private theorem rec3839 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[3,7,15],[11],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[200]? = some (⟨47,(21),[3,7,15],[11],271⟩) from rfl))
private theorem rec3850 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[3,4,7,8,12,15,16],[10],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[211]? = some (⟨47,(22),[3,4,7,8,12,15,16],[10],272⟩) from rfl))
private theorem rec3851 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[3,15],[11],300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[212]? = some (⟨47,(22),[3,15],[11],300⟩) from rfl))
private theorem rec3865 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[3,4,7,15,16],[10],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[226]? = some (⟨47,(23),[3,4,7,15,16],[10],272⟩) from rfl))
private theorem rec3866 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[3,15],[11],300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[227]? = some (⟨47,(23),[3,15],[11],300⟩) from rfl))
private theorem rec3882 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[3,4,7,8,12,15,16],[10],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[243]? = some (⟨47,(24),[3,4,7,8,12,15,16],[10],272⟩) from rfl))
private theorem rec3883 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[3,15],[11],300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[244]? = some (⟨47,(24),[3,15],[11],300⟩) from rfl))
private theorem rec4089 (si parent : ℕ) (hs : si ∈ ([3] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[3],[11],307⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[450]? = some (⟨53,(0),[3],[11],307⟩) from rfl))
private theorem rec4090 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[3,4,7,8,12],[10],279⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[451]? = some (⟨53,(0),[3,4,7,8,12],[10],279⟩) from rfl))
private theorem rec4105 (si parent : ℕ) (hs : si ∈ ([3] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[3],[11],308⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[466]? = some (⟨53,(1),[3],[11],308⟩) from rfl))
private theorem rec4106 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[3,4,7,8,12],[10],280⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[467]? = some (⟨53,(1),[3,4,7,8,12],[10],280⟩) from rfl))
private theorem rec4121 (si parent : ℕ) (hs : si ∈ ([3] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[3],[11],309⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[482]? = some (⟨53,(2),[3],[11],309⟩) from rfl))
private theorem rec4122 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[3,4,7,8,12],[10],281⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[483]? = some (⟨53,(2),[3,4,7,8,12],[10],281⟩) from rfl))
private theorem rec4136 (si parent : ℕ) (hs : si ∈ ([3] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[3],[11],310⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[497]? = some (⟨53,(3),[3],[11],310⟩) from rfl))
private theorem rec4137 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[3,4,7,8,12],[10],282⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[498]? = some (⟨53,(3),[3,4,7,8,12],[10],282⟩) from rfl))
private theorem rec4420 (si parent : ℕ) (hs : si ∈ ([3] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 58 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(5),[3],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[271]? = some (⟨58,(5),[3],[10],3⟩) from rfl))
private theorem rec4421 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 58 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(5),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[272]? = some (⟨58,(5),[3,15],[11],3⟩) from rfl))
private theorem rec4429 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 58 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(7),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[280]? = some (⟨58,(7),[3,7,15],[10],3⟩) from rfl))
private theorem rec4430 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 58 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(7),[3,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[281]? = some (⟨58,(7),[3,15],[11],3⟩) from rfl))
private theorem rec4438 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 58 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(8),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[289]? = some (⟨58,(8),[3,7,15],[11],3⟩) from rfl))
private theorem rec4439 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 58 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(8),[3,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[290]? = some (⟨58,(8),[3,15],[10],3⟩) from rfl))
private theorem rec4446 (si parent : ℕ) (hs : si ∈ ([3] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 58 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(9),[3],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[297]? = some (⟨58,(9),[3],[10,11],3⟩) from rfl))
private theorem rec4455 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 58 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(15),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[306]? = some (⟨58,(15),[3,7,15],[11],3⟩) from rfl))
private theorem rec4456 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 58 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(15),[3,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[307]? = some (⟨58,(15),[3,15],[10],3⟩) from rfl))
private theorem rec4464 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 58 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(16),[3,7,15],[11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[315]? = some (⟨58,(16),[3,7,15],[11],3⟩) from rfl))
private theorem rec4465 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 58 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(16),[3,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[316]? = some (⟨58,(16),[3,15],[10],3⟩) from rfl))
private theorem rec4472 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 58 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(17),[3,7,15],[10,11],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[323]? = some (⟨58,(17),[3,7,15],[10,11],48⟩) from rfl))
private theorem rec4478 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 58 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(19),[3,7],[10],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[329]? = some (⟨58,(19),[3,7],[10],48⟩) from rfl))
private theorem rec4479 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 58 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(19),[3,7,15],[11],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[330]? = some (⟨58,(19),[3,7,15],[11],143⟩) from rfl))
private theorem rec14853 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(0),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1250]? = some (⟨352,(0),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14856 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(1),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1253]? = some (⟨352,(1),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14859 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(2),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1256]? = some (⟨352,(2),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14862 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(3),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1259]? = some (⟨352,(3),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14865 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(4),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1262]? = some (⟨352,(4),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14868 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(5),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1265]? = some (⟨352,(5),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14871 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(6),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1268]? = some (⟨352,(6),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14874 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(7),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1271]? = some (⟨352,(7),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14877 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(8),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1274]? = some (⟨352,(8),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14880 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 352 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨352,(9),[3,7,15],[10,11],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1277]? = some (⟨352,(9),[3,7,15],[10,11],3⟩) from rfl))
private theorem rec14883 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(0),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1280]? = some (⟨356,(0),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14886 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(1),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1283]? = some (⟨356,(1),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14889 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(2),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1286]? = some (⟨356,(2),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14892 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(3),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1289]? = some (⟨356,(3),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14895 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(4),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1292]? = some (⟨356,(4),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14898 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(5),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1295]? = some (⟨356,(5),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14901 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(6),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1298]? = some (⟨356,(6),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14904 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(7),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1301]? = some (⟨356,(7),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14907 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(8),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1304]? = some (⟨356,(8),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14910 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 356 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨356,(9),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1307]? = some (⟨356,(9),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14913 (si parent : ℕ) (hs : si ∈ ([3] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 360 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨360,(0),[3],[10],934⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1310]? = some (⟨360,(0),[3],[10],934⟩) from rfl))
private theorem rec14914 (si parent : ℕ) (hs : si ∈ ([3] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 360 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨360,(0),[3],[11],941⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1311]? = some (⟨360,(0),[3],[11],941⟩) from rfl))
private theorem rec14918 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 360 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨360,(1),[3,7],[10],935⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1315]? = some (⟨360,(1),[3,7],[10],935⟩) from rfl))
private theorem rec14919 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 360 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨360,(1),[3,7],[11],942⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1316]? = some (⟨360,(1),[3,7],[11],942⟩) from rfl))
private theorem rec14922 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 360 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨360,(2),[3,7],[10],934⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1]? = some (⟨360,(2),[3,7],[10],934⟩) from rfl))
private theorem rec14923 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 360 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨360,(2),[3,7],[11],941⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[2]? = some (⟨360,(2),[3,7],[11],941⟩) from rfl))
private theorem rec14926 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 360 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨360,(3),[3,7],[10],936⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[5]? = some (⟨360,(3),[3,7],[10],936⟩) from rfl))
private theorem rec14927 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 360 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨360,(3),[3,7],[11],943⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[6]? = some (⟨360,(3),[3,7],[11],943⟩) from rfl))
private theorem rec14930 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 363 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨363,(0),[3,15],[10,11],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[9]? = some (⟨363,(0),[3,15],[10,11],159⟩) from rfl))
private theorem rec14933 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 363 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨363,(1),[3,7,15],[10,11],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[12]? = some (⟨363,(1),[3,7,15],[10,11],2⟩) from rfl))
private theorem rec14936 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 363 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨363,(2),[3,7,15],[10,11],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[15]? = some (⟨363,(2),[3,7,15],[10,11],159⟩) from rfl))
private theorem rec14939 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 363 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨363,(3),[3,7,15],[10,11],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[18]? = some (⟨363,(3),[3,7,15],[10,11],99⟩) from rfl))
private theorem rec14942 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 365 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨365,(0),[3,7],[10],283⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[21]? = some (⟨365,(0),[3,7],[10],283⟩) from rfl))
private theorem rec14943 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 365 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨365,(0),[3,7],[11],337⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[22]? = some (⟨365,(0),[3,7],[11],337⟩) from rfl))
private theorem rec14946 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 365 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨365,(1),[3,7],[10],937⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[25]? = some (⟨365,(1),[3,7],[10],937⟩) from rfl))
private theorem rec14947 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 365 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨365,(1),[3,7],[11],944⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[26]? = some (⟨365,(1),[3,7],[11],944⟩) from rfl))
private theorem rec14950 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 365 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨365,(2),[3,7],[10],938⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[29]? = some (⟨365,(2),[3,7],[10],938⟩) from rfl))
private theorem rec14951 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 365 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨365,(2),[3,7],[11],945⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[30]? = some (⟨365,(2),[3,7],[11],945⟩) from rfl))
private theorem rec14954 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 365 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨365,(3),[3,7],[10,11],939⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[33]? = some (⟨365,(3),[3,7],[10,11],939⟩) from rfl))
private theorem rec14957 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10, 11] : List ℕ)) : section14Recorded section14Catalog si parent 365 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨365,(4),[3,7],[10,11],940⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[36]? = some (⟨365,(4),[3,7],[10,11],940⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 3).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 3)).drop 0).take 16, section14Recorded section14Catalog 3 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 3).plans.drop 2).take 1 = [⟨3,38,[([1],[]),([2],[]),([3],[1])],false,[(351,⟨([1],[]),true,([1],[]),false,false,[]⟩),(352,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(353,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(354,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(355,⟨([2],[]),true,([2],[]),false,false,[]⟩),(356,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(357,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(358,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(359,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(360,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(361,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(362,⟨([1],[]),true,([2],[]),false,false,[]⟩),(363,⟨([2],[]),true,([1],[]),false,false,[]⟩),(364,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(365,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩),(366,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 3)).drop 0).take 16 = [⟨2,0,[⟨true,false,12⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨2,1,[⟨true,false,12⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨2,2,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,3,[⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,4,[⟨true,false,16⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,5,[⟨true,false,16⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,6,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨2,7,[⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,8,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,9,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,10,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨2,11,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,12,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,13,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,14,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨2,15,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec3019 3 0 (by decide) (by decide)
  · left
    exact rec2993 3 1 (by decide) (by decide)
  · left
    exact rec3037 3 2 (by decide) (by decide)
  · left
    exact rec3040 3 3 (by decide) (by decide)
  · left
    exact rec3041 3 4 (by decide) (by decide)
  · left
    exact rec3036 3 5 (by decide) (by decide)
  · left
    exact rec3038 3 6 (by decide) (by decide)
  · left
    exact rec3041 3 7 (by decide) (by decide)
  · left
    exact rec3042 3 8 (by decide) (by decide)
  · left
    exact rec3044 3 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(351,⟨([1],[]),true,([1],[]),false,false,[]⟩),(352,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(353,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(354,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(355,⟨([2],[]),true,([2],[]),false,false,[]⟩),(356,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(357,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(358,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(359,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(360,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(361,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(362,⟨([1],[]),true,([2],[]),false,false,[]⟩),(363,⟨([2],[]),true,([1],[]),false,false,[]⟩),(364,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(365,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩),(366,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 351)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 352)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14853 3 10 (by decide) (by decide)
      · right
        exact rec14856 3 10 (by decide) (by decide)
      · right
        exact rec14859 3 10 (by decide) (by decide)
      · right
        exact rec14862 3 10 (by decide) (by decide)
      · right
        exact rec14865 3 10 (by decide) (by decide)
      · right
        exact rec14868 3 10 (by decide) (by decide)
      · right
        exact rec14871 3 10 (by decide) (by decide)
      · right
        exact rec14874 3 10 (by decide) (by decide)
      · right
        exact rec14877 3 10 (by decide) (by decide)
      · right
        exact rec14880 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 353)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 42)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3215 3 10 (by decide) (by decide)
      · right
        exact rec3226 3 10 (by decide) (by decide)
      · right
        exact rec3236 3 10 (by decide) (by decide)
      · right
        exact rec3246 3 10 (by decide) (by decide)
      · right
        exact rec3256 3 10 (by decide) (by decide)
      · right
        exact rec3266 3 10 (by decide) (by decide)
      · right
        exact rec3277 3 10 (by decide) (by decide)
      · right
        exact rec3287 3 10 (by decide) (by decide)
      · right
        exact rec3297 3 10 (by decide) (by decide)
      · right
        exact rec3307 3 10 (by decide) (by decide)
      · right
        exact rec3317 3 10 (by decide) (by decide)
      · right
        exact rec3328 3 10 (by decide) (by decide)
      · right
        exact rec3338 3 10 (by decide) (by decide)
      · right
        exact rec3348 3 10 (by decide) (by decide)
      · right
        exact rec3358 3 10 (by decide) (by decide)
      · right
        exact rec3368 3 10 (by decide) (by decide)
      · right
        exact rec3379 3 10 (by decide) (by decide)
      · right
        exact rec3389 3 10 (by decide) (by decide)
      · right
        exact rec3399 3 10 (by decide) (by decide)
      · right
        exact rec3409 3 10 (by decide) (by decide)
      · right
        exact rec3419 3 10 (by decide) (by decide)
      · right
        exact rec3430 3 10 (by decide) (by decide)
      · right
        exact rec3440 3 10 (by decide) (by decide)
      · right
        exact rec3450 3 10 (by decide) (by decide)
      · right
        exact rec3460 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 354)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 355)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 356)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14883 3 10 (by decide) (by decide)
      · right
        exact rec14886 3 10 (by decide) (by decide)
      · right
        exact rec14889 3 10 (by decide) (by decide)
      · right
        exact rec14892 3 10 (by decide) (by decide)
      · right
        exact rec14895 3 10 (by decide) (by decide)
      · right
        exact rec14898 3 10 (by decide) (by decide)
      · right
        exact rec14901 3 10 (by decide) (by decide)
      · right
        exact rec14904 3 10 (by decide) (by decide)
      · right
        exact rec14907 3 10 (by decide) (by decide)
      · right
        exact rec14910 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 357)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 47)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3568 3 10 (by decide) (by decide)
      · right
        exact rec3578 3 10 (by decide) (by decide)
      · right
        exact rec3588 3 10 (by decide) (by decide)
      · right
        exact rec3599 3 10 (by decide) (by decide)
      · right
        exact rec3610 3 10 (by decide) (by decide)
      · right
        exact rec3621 3 10 (by decide) (by decide)
      · right
        exact rec3631 3 10 (by decide) (by decide)
      · right
        exact rec3643 3 10 (by decide) (by decide)
      · right
        exact rec3659 3 10 (by decide) (by decide)
      · right
        exact rec3677 3 10 (by decide) (by decide)
      · right
        exact rec3691 3 10 (by decide) (by decide)
      · right
        exact rec3701 3 10 (by decide) (by decide)
      · right
        exact rec3713 3 10 (by decide) (by decide)
      · right
        exact rec3729 3 10 (by decide) (by decide)
      · right
        exact rec3747 3 10 (by decide) (by decide)
      · right
        exact rec3761 3 10 (by decide) (by decide)
      · right
        exact rec3771 3 10 (by decide) (by decide)
      · right
        exact rec3783 3 10 (by decide) (by decide)
      · right
        exact rec3798 3 10 (by decide) (by decide)
      · right
        exact rec3815 3 10 (by decide) (by decide)
      · right
        exact rec3828 3 10 (by decide) (by decide)
      · right
        exact rec3838 3 10 (by decide) (by decide)
      · right
        exact rec3850 3 10 (by decide) (by decide)
      · right
        exact rec3865 3 10 (by decide) (by decide)
      · right
        exact rec3882 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 358)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 359)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 360)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14913 3 10 (by decide) (by decide)
      · right
        exact rec14918 3 10 (by decide) (by decide)
      · right
        exact rec14922 3 10 (by decide) (by decide)
      · right
        exact rec14926 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 361)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 52)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 53)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4090 3 10 (by decide) (by decide)
      · right
        exact rec4106 3 10 (by decide) (by decide)
      · right
        exact rec4122 3 10 (by decide) (by decide)
      · right
        exact rec4137 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 362)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 363)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14930 3 10 (by decide) (by decide)
      · right
        exact rec14933 3 10 (by decide) (by decide)
      · right
        exact rec14936 3 10 (by decide) (by decide)
      · right
        exact rec14939 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 364)).length = 8 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 365)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14942 3 10 (by decide) (by decide)
      · right
        exact rec14946 3 10 (by decide) (by decide)
      · right
        exact rec14950 3 10 (by decide) (by decide)
      · right
        exact rec14954 3 10 (by decide) (by decide)
      · right
        exact rec14957 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 58)).length = 20 := by decide +kernel
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
        exact rec4420 3 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4429 3 10 (by decide) (by decide)
      · right
        exact rec4439 3 10 (by decide) (by decide)
      · right
        exact rec4446 3 10 (by decide) (by decide)
      · left
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
        exact rec4456 3 10 (by decide) (by decide)
      · right
        exact rec4465 3 10 (by decide) (by decide)
      · right
        exact rec4472 3 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4478 3 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 366)).length = 4 := by decide +kernel
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
  · right
    intro gs hgs
    change gs ∈ [(351,⟨([1],[]),true,([1],[]),false,false,[]⟩),(352,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(353,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(354,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(355,⟨([2],[]),true,([2],[]),false,false,[]⟩),(356,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(357,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(358,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(359,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(360,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(361,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(362,⟨([1],[]),true,([2],[]),false,false,[]⟩),(363,⟨([2],[]),true,([1],[]),false,false,[]⟩),(364,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(365,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩),(366,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 351)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 352)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14853 3 11 (by decide) (by decide)
      · right
        exact rec14856 3 11 (by decide) (by decide)
      · right
        exact rec14859 3 11 (by decide) (by decide)
      · right
        exact rec14862 3 11 (by decide) (by decide)
      · right
        exact rec14865 3 11 (by decide) (by decide)
      · right
        exact rec14868 3 11 (by decide) (by decide)
      · right
        exact rec14871 3 11 (by decide) (by decide)
      · right
        exact rec14874 3 11 (by decide) (by decide)
      · right
        exact rec14877 3 11 (by decide) (by decide)
      · right
        exact rec14880 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 353)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 42)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3216 3 11 (by decide) (by decide)
      · right
        exact rec3227 3 11 (by decide) (by decide)
      · right
        exact rec3237 3 11 (by decide) (by decide)
      · right
        exact rec3247 3 11 (by decide) (by decide)
      · right
        exact rec3257 3 11 (by decide) (by decide)
      · right
        exact rec3267 3 11 (by decide) (by decide)
      · right
        exact rec3278 3 11 (by decide) (by decide)
      · right
        exact rec3288 3 11 (by decide) (by decide)
      · right
        exact rec3298 3 11 (by decide) (by decide)
      · right
        exact rec3308 3 11 (by decide) (by decide)
      · right
        exact rec3318 3 11 (by decide) (by decide)
      · right
        exact rec3329 3 11 (by decide) (by decide)
      · right
        exact rec3339 3 11 (by decide) (by decide)
      · right
        exact rec3349 3 11 (by decide) (by decide)
      · right
        exact rec3359 3 11 (by decide) (by decide)
      · right
        exact rec3369 3 11 (by decide) (by decide)
      · right
        exact rec3380 3 11 (by decide) (by decide)
      · right
        exact rec3390 3 11 (by decide) (by decide)
      · right
        exact rec3400 3 11 (by decide) (by decide)
      · right
        exact rec3410 3 11 (by decide) (by decide)
      · right
        exact rec3420 3 11 (by decide) (by decide)
      · right
        exact rec3431 3 11 (by decide) (by decide)
      · right
        exact rec3441 3 11 (by decide) (by decide)
      · right
        exact rec3451 3 11 (by decide) (by decide)
      · right
        exact rec3461 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 354)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 355)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 356)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14883 3 11 (by decide) (by decide)
      · right
        exact rec14886 3 11 (by decide) (by decide)
      · right
        exact rec14889 3 11 (by decide) (by decide)
      · right
        exact rec14892 3 11 (by decide) (by decide)
      · right
        exact rec14895 3 11 (by decide) (by decide)
      · right
        exact rec14898 3 11 (by decide) (by decide)
      · right
        exact rec14901 3 11 (by decide) (by decide)
      · right
        exact rec14904 3 11 (by decide) (by decide)
      · right
        exact rec14907 3 11 (by decide) (by decide)
      · right
        exact rec14910 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 357)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 47)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3569 3 11 (by decide) (by decide)
      · right
        exact rec3579 3 11 (by decide) (by decide)
      · right
        exact rec3589 3 11 (by decide) (by decide)
      · right
        exact rec3600 3 11 (by decide) (by decide)
      · right
        exact rec3611 3 11 (by decide) (by decide)
      · right
        exact rec3622 3 11 (by decide) (by decide)
      · right
        exact rec3632 3 11 (by decide) (by decide)
      · right
        exact rec3644 3 11 (by decide) (by decide)
      · right
        exact rec3660 3 11 (by decide) (by decide)
      · right
        exact rec3678 3 11 (by decide) (by decide)
      · right
        exact rec3692 3 11 (by decide) (by decide)
      · right
        exact rec3702 3 11 (by decide) (by decide)
      · right
        exact rec3714 3 11 (by decide) (by decide)
      · right
        exact rec3730 3 11 (by decide) (by decide)
      · right
        exact rec3748 3 11 (by decide) (by decide)
      · right
        exact rec3762 3 11 (by decide) (by decide)
      · right
        exact rec3772 3 11 (by decide) (by decide)
      · right
        exact rec3784 3 11 (by decide) (by decide)
      · right
        exact rec3799 3 11 (by decide) (by decide)
      · right
        exact rec3816 3 11 (by decide) (by decide)
      · right
        exact rec3829 3 11 (by decide) (by decide)
      · right
        exact rec3839 3 11 (by decide) (by decide)
      · right
        exact rec3851 3 11 (by decide) (by decide)
      · right
        exact rec3866 3 11 (by decide) (by decide)
      · right
        exact rec3883 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 358)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 359)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 360)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14914 3 11 (by decide) (by decide)
      · right
        exact rec14919 3 11 (by decide) (by decide)
      · right
        exact rec14923 3 11 (by decide) (by decide)
      · right
        exact rec14927 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 361)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 52)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 53)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4089 3 11 (by decide) (by decide)
      · right
        exact rec4105 3 11 (by decide) (by decide)
      · right
        exact rec4121 3 11 (by decide) (by decide)
      · right
        exact rec4136 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 362)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 363)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14930 3 11 (by decide) (by decide)
      · right
        exact rec14933 3 11 (by decide) (by decide)
      · right
        exact rec14936 3 11 (by decide) (by decide)
      · right
        exact rec14939 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 364)).length = 8 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 365)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14943 3 11 (by decide) (by decide)
      · right
        exact rec14947 3 11 (by decide) (by decide)
      · right
        exact rec14951 3 11 (by decide) (by decide)
      · right
        exact rec14954 3 11 (by decide) (by decide)
      · right
        exact rec14957 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 58)).length = 20 := by decide +kernel
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
        exact rec4421 3 11 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4430 3 11 (by decide) (by decide)
      · right
        exact rec4438 3 11 (by decide) (by decide)
      · right
        exact rec4446 3 11 (by decide) (by decide)
      · left
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
        exact rec4455 3 11 (by decide) (by decide)
      · right
        exact rec4464 3 11 (by decide) (by decide)
      · right
        exact rec4472 3 11 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4479 3 11 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 366)).length = 4 := by decide +kernel
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
    exact rec3043 3 12 (by decide) (by decide)
  · left
    exact rec3043 3 13 (by decide) (by decide)
  · left
    exact rec3039 3 14 (by decide) (by decide)
  · left
    exact rec3043 3 15 (by decide) (by decide)
end Section14Coverage_3_2_p0_16

#print axioms solution
