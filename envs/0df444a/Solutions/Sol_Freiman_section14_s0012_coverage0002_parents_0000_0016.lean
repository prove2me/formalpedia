-- Prove2me | solution 1 for Freiman.section14_s0012_coverage0002_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T03:43:43.710796+00:00
-- url     : https://prove2.me/submissions/54db0140-e7ae-442a-a7be-5ed8883f4585

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
namespace Section14Coverage_12_2_p0_16
private theorem rec3027 (si parent : ℕ) (hs : si ∈ ([2, 4, 6, 8, 10, 12, 14, 16] : List ℕ)) (hp : parent ∈ ([0, 4] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[2,4,6,8,10,12,14,16],[0,4],247⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[584]? = some (⟨38,(-1),[2,4,6,8,10,12,14,16],[0,4],247⟩) from rfl))
private theorem rec3036 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[3,4,7,8,12,15,16],[5],248⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[593]? = some (⟨38,(-1),[3,4,7,8,12,15,16],[5],248⟩) from rfl))
private theorem rec3045 (si parent : ℕ) (hs : si ∈ ([4, 8, 10, 12, 16] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,10,12,16],[8],69⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[602]? = some (⟨38,(-1),[4,8,10,12,16],[8],69⟩) from rfl))
private theorem rec3046 (si parent : ℕ) (hs : si ∈ ([4, 8, 11, 12, 16] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,11,12,16],[1],248⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[603]? = some (⟨38,(-1),[4,8,11,12,16],[1],248⟩) from rfl))
private theorem rec3047 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,12,16],[9],70⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[604]? = some (⟨38,(-1),[4,8,12,16],[9],70⟩) from rfl))
private theorem rec3048 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,12,16],[11],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[605]? = some (⟨38,(-1),[4,8,12,16],[11],207⟩) from rfl))
private theorem rec3049 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([12] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,12,16],[12],247⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[606]? = some (⟨38,(-1),[4,8,12,16],[12],247⟩) from rfl))
private theorem rec3050 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([13] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,12,16],[13],248⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[607]? = some (⟨38,(-1),[4,8,12,16],[13],248⟩) from rfl))
private theorem rec3051 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,12,16],[2],249⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[608]? = some (⟨38,(-1),[4,8,12,16],[2],249⟩) from rfl))
private theorem rec3052 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([7, 15] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,12,16],[7,15],251⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[609]? = some (⟨38,(-1),[4,8,12,16],[7,15],251⟩) from rfl))
private theorem rec3058 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[8,12],[3],251⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[615]? = some (⟨38,(-1),[8,12],[3],251⟩) from rfl))
private theorem rec3568 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[3,4,7,8,12,15,16],[10],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1125]? = some (⟨47,(0),[3,4,7,8,12,15,16],[10],189⟩) from rfl))
private theorem rec3570 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[4,8,12,16],[14],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1127]? = some (⟨47,(0),[4,8,12,16],[14],189⟩) from rfl))
private theorem rec3575 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[12],[6],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1132]? = some (⟨47,(0),[12],[6],189⟩) from rfl))
private theorem rec3578 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[3,4,7,8,12,15,16],[10],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1135]? = some (⟨47,(1),[3,4,7,8,12,15,16],[10],260⟩) from rfl))
private theorem rec3580 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[4,8,12,16],[14],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1137]? = some (⟨47,(1),[4,8,12,16],[14],260⟩) from rfl))
private theorem rec3585 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[12],[6],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1142]? = some (⟨47,(1),[12],[6],260⟩) from rfl))
private theorem rec3588 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[3,4,7,8,12,15,16],[10],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1145]? = some (⟨47,(2),[3,4,7,8,12,15,16],[10],261⟩) from rfl))
private theorem rec3590 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[4,8,12,16],[14],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1147]? = some (⟨47,(2),[4,8,12,16],[14],261⟩) from rfl))
private theorem rec3596 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[12],[6],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1153]? = some (⟨47,(2),[12],[6],191⟩) from rfl))
private theorem rec3599 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[3,4,7,8,12,15,16],[10],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1156]? = some (⟨47,(3),[3,4,7,8,12,15,16],[10],262⟩) from rfl))
private theorem rec3601 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[4,8,12,16],[14],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1158]? = some (⟨47,(3),[4,8,12,16],[14],262⟩) from rfl))
private theorem rec3607 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[12],[6],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1164]? = some (⟨47,(3),[12],[6],192⟩) from rfl))
private theorem rec3610 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[3,4,7,8,12,15,16],[10],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1167]? = some (⟨47,(4),[3,4,7,8,12,15,16],[10],263⟩) from rfl))
private theorem rec3612 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[4,8,12,16],[14],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1169]? = some (⟨47,(4),[4,8,12,16],[14],263⟩) from rfl))
private theorem rec3618 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[12],[6],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1175]? = some (⟨47,(4),[12],[6],193⟩) from rfl))
private theorem rec3621 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[3,4,7,8,12,15,16],[10],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1178]? = some (⟨47,(5),[3,4,7,8,12,15,16],[10],189⟩) from rfl))
private theorem rec3623 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[4,8,12,16],[14],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1180]? = some (⟨47,(5),[4,8,12,16],[14],189⟩) from rfl))
private theorem rec3628 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[12],[6],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1185]? = some (⟨47,(5),[12],[6],189⟩) from rfl))
private theorem rec3631 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[3,4,7,8,12,15,16],[10],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1188]? = some (⟨47,(6),[3,4,7,8,12,15,16],[10],260⟩) from rfl))
private theorem rec3633 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[4,8,12,16],[14],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1190]? = some (⟨47,(6),[4,8,12,16],[14],260⟩) from rfl))
private theorem rec3638 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[12],[6],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1195]? = some (⟨47,(6),[12],[6],260⟩) from rfl))
private theorem rec3643 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[3,4,7,8,12,15,16],[10],264⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[4]? = some (⟨47,(7),[3,4,7,8,12,15,16],[10],264⟩) from rfl))
private theorem rec3645 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[4,8,12,16],[14],319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[6]? = some (⟨47,(7),[4,8,12,16],[14],319⟩) from rfl))
private theorem rec3654 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[12],[6],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[15]? = some (⟨47,(7),[12],[6],191⟩) from rfl))
private theorem rec3661 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[4,8,12,16],[14],320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[22]? = some (⟨47,(8),[4,8,12,16],[14],320⟩) from rfl))
private theorem rec3665 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[8,12],[10],1631⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[26]? = some (⟨47,(8),[8,12],[10],1631⟩) from rfl))
private theorem rec3671 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[12],[6],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[32]? = some (⟨47,(8),[12],[6],192⟩) from rfl))
private theorem rec3677 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[3,4,7,8,12,15,16],[10],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[38]? = some (⟨47,(9),[3,4,7,8,12,15,16],[10],266⟩) from rfl))
private theorem rec3679 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[4,8,12,16],[14],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[40]? = some (⟨47,(9),[4,8,12,16],[14],321⟩) from rfl))
private theorem rec3688 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[12],[6],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[49]? = some (⟨47,(9),[12],[6],193⟩) from rfl))
private theorem rec3691 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[3,4,7,8,12,15,16],[10],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[52]? = some (⟨47,(10),[3,4,7,8,12,15,16],[10],194⟩) from rfl))
private theorem rec3693 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[4,8,12,16],[14],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[54]? = some (⟨47,(10),[4,8,12,16],[14],194⟩) from rfl))
private theorem rec3698 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[12],[6],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[59]? = some (⟨47,(10),[12],[6],194⟩) from rfl))
private theorem rec3701 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[3,4,7,8,12,15,16],[10],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[62]? = some (⟨47,(11),[3,4,7,8,12,15,16],[10],267⟩) from rfl))
private theorem rec3703 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[4,8,12,16],[14],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[64]? = some (⟨47,(11),[4,8,12,16],[14],267⟩) from rfl))
private theorem rec3708 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[12],[6],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[69]? = some (⟨47,(11),[12],[6],267⟩) from rfl))
private theorem rec3713 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[3,4,7,8,12,15,16],[10],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[74]? = some (⟨47,(12),[3,4,7,8,12,15,16],[10],268⟩) from rfl))
private theorem rec3715 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[4,8,12,16],[14],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[76]? = some (⟨47,(12),[4,8,12,16],[14],322⟩) from rfl))
private theorem rec3724 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[12],[6],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[85]? = some (⟨47,(12),[12],[6],195⟩) from rfl))
private theorem rec3731 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[4,8,12,16],[14],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[92]? = some (⟨47,(13),[4,8,12,16],[14],322⟩) from rfl))
private theorem rec3736 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[8,12],[10],1632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[97]? = some (⟨47,(13),[8,12],[10],1632⟩) from rfl))
private theorem rec3742 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[12],[6],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[103]? = some (⟨47,(13),[12],[6],195⟩) from rfl))
private theorem rec3747 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[3,4,7,8,12,15,16],[10],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[108]? = some (⟨47,(14),[3,4,7,8,12,15,16],[10],266⟩) from rfl))
private theorem rec3749 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[4,8,12,16],[14],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[110]? = some (⟨47,(14),[4,8,12,16],[14],321⟩) from rfl))
private theorem rec3758 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[12],[6],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[119]? = some (⟨47,(14),[12],[6],193⟩) from rfl))
private theorem rec3761 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[3,4,7,8,12,15,16],[10],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[122]? = some (⟨47,(15),[3,4,7,8,12,15,16],[10],196⟩) from rfl))
private theorem rec3763 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[4,8,12,16],[14],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[124]? = some (⟨47,(15),[4,8,12,16],[14],196⟩) from rfl))
private theorem rec3768 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[12],[6],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[129]? = some (⟨47,(15),[12],[6],196⟩) from rfl))
private theorem rec3771 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[3,4,7,8,12,15,16],[10],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[132]? = some (⟨47,(16),[3,4,7,8,12,15,16],[10],269⟩) from rfl))
private theorem rec3773 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[4,8,12,16],[14],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[134]? = some (⟨47,(16),[4,8,12,16],[14],269⟩) from rfl))
private theorem rec3778 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[12],[6],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[139]? = some (⟨47,(16),[12],[6],269⟩) from rfl))
private theorem rec3783 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[3,4,7,8,12,15,16],[10],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[144]? = some (⟨47,(17),[3,4,7,8,12,15,16],[10],270⟩) from rfl))
private theorem rec3785 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[4,8,12,16],[14],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[146]? = some (⟨47,(17),[4,8,12,16],[14],323⟩) from rfl))
private theorem rec3793 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[12],[6],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[154]? = some (⟨47,(17),[12],[6],197⟩) from rfl))
private theorem rec3800 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[4,8,12,16],[14],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[161]? = some (⟨47,(18),[4,8,12,16],[14],323⟩) from rfl))
private theorem rec3804 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[8,12],[10],1633⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[165]? = some (⟨47,(18),[8,12],[10],1633⟩) from rfl))
private theorem rec3810 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[12],[6],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[171]? = some (⟨47,(18),[12],[6],197⟩) from rfl))
private theorem rec3815 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[3,4,7,8,12,15,16],[10],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[176]? = some (⟨47,(19),[3,4,7,8,12,15,16],[10],270⟩) from rfl))
private theorem rec3817 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[4,8,12,16],[14],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[178]? = some (⟨47,(19),[4,8,12,16],[14],323⟩) from rfl))
private theorem rec3825 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[12],[6],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[186]? = some (⟨47,(19),[12],[6],197⟩) from rfl))
private theorem rec3828 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[3,4,7,8,12,15,16],[10],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[189]? = some (⟨47,(20),[3,4,7,8,12,15,16],[10],198⟩) from rfl))
private theorem rec3830 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[4,8,12,16],[14],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[191]? = some (⟨47,(20),[4,8,12,16],[14],198⟩) from rfl))
private theorem rec3835 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[12],[6],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[196]? = some (⟨47,(20),[12],[6],198⟩) from rfl))
private theorem rec3838 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[3,4,7,8,12,15,16],[10],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[199]? = some (⟨47,(21),[3,4,7,8,12,15,16],[10],271⟩) from rfl))
private theorem rec3840 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[4,8,12,16],[14],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[201]? = some (⟨47,(21),[4,8,12,16],[14],271⟩) from rfl))
private theorem rec3845 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[12],[6],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[206]? = some (⟨47,(21),[12],[6],271⟩) from rfl))
private theorem rec3850 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[3,4,7,8,12,15,16],[10],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[211]? = some (⟨47,(22),[3,4,7,8,12,15,16],[10],272⟩) from rfl))
private theorem rec3852 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[4,8,12,16],[14],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[213]? = some (⟨47,(22),[4,8,12,16],[14],324⟩) from rfl))
private theorem rec3860 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[12],[6],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[221]? = some (⟨47,(22),[12],[6],199⟩) from rfl))
private theorem rec3867 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[4,8,12,16],[14],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[228]? = some (⟨47,(23),[4,8,12,16],[14],324⟩) from rfl))
private theorem rec3871 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[8,12],[10],1634⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[232]? = some (⟨47,(23),[8,12],[10],1634⟩) from rfl))
private theorem rec3877 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[12],[6],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[238]? = some (⟨47,(23),[12],[6],199⟩) from rfl))
private theorem rec3882 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[3,4,7,8,12,15,16],[10],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[243]? = some (⟨47,(24),[3,4,7,8,12,15,16],[10],272⟩) from rfl))
private theorem rec3884 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[4,8,12,16],[14],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[245]? = some (⟨47,(24),[4,8,12,16],[14],324⟩) from rfl))
private theorem rec3892 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[12],[6],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[253]? = some (⟨47,(24),[12],[6],199⟩) from rfl))
private theorem rec3897 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[4,8,12],[10],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[258]? = some (⟨50,(0),[4,8,12],[10],301⟩) from rfl))
private theorem rec3898 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[4,8,12],[14],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[259]? = some (⟨50,(0),[4,8,12],[14],331⟩) from rfl))
private theorem rec3904 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[12],[6],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[265]? = some (⟨50,(0),[12],[6],331⟩) from rfl))
private theorem rec3909 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[4,8,12],[10],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[270]? = some (⟨50,(1),[4,8,12],[10],302⟩) from rfl))
private theorem rec3910 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[4,8,12],[14],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[271]? = some (⟨50,(1),[4,8,12],[14],332⟩) from rfl))
private theorem rec3916 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[12],[6],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[277]? = some (⟨50,(1),[12],[6],332⟩) from rfl))
private theorem rec3921 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[4,8,12],[10],303⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[282]? = some (⟨50,(2),[4,8,12],[10],303⟩) from rfl))
private theorem rec3922 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[4,8,12],[14],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[283]? = some (⟨50,(2),[4,8,12],[14],333⟩) from rfl))
private theorem rec3928 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[12],[6],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[289]? = some (⟨50,(2),[12],[6],333⟩) from rfl))
private theorem rec3933 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[4,8,12],[10],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[294]? = some (⟨50,(3),[4,8,12],[10],304⟩) from rfl))
private theorem rec3934 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[4,8,12],[14],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[295]? = some (⟨50,(3),[4,8,12],[14],334⟩) from rfl))
private theorem rec3940 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[12],[6],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[301]? = some (⟨50,(3),[12],[6],334⟩) from rfl))
private theorem rec3945 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[4,8,12],[10],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[306]? = some (⟨50,(4),[4,8,12],[10],301⟩) from rfl))
private theorem rec3946 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[4,8,12],[14],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[307]? = some (⟨50,(4),[4,8,12],[14],331⟩) from rfl))
private theorem rec3952 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[12],[6],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[313]? = some (⟨50,(4),[12],[6],331⟩) from rfl))
private theorem rec3957 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[4,8,12],[10],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[318]? = some (⟨50,(5),[4,8,12],[10],302⟩) from rfl))
private theorem rec3958 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[4,8,12],[14],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[319]? = some (⟨50,(5),[4,8,12],[14],332⟩) from rfl))
private theorem rec3964 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[12],[6],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[325]? = some (⟨50,(5),[12],[6],332⟩) from rfl))
private theorem rec3969 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[4,8,12],[10],305⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[330]? = some (⟨50,(6),[4,8,12],[10],305⟩) from rfl))
private theorem rec3970 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[4,8,12],[14],335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[331]? = some (⟨50,(6),[4,8,12],[14],335⟩) from rfl))
private theorem rec3976 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[12],[6],335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[337]? = some (⟨50,(6),[12],[6],335⟩) from rfl))
private theorem rec3981 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[4,8,12],[10],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[342]? = some (⟨50,(7),[4,8,12],[10],304⟩) from rfl))
private theorem rec3982 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[4,8,12],[14],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[343]? = some (⟨50,(7),[4,8,12],[14],334⟩) from rfl))
private theorem rec3988 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[12],[6],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[349]? = some (⟨50,(7),[12],[6],334⟩) from rfl))
private theorem rec3993 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[4,8,12],[10],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[354]? = some (⟨50,(8),[4,8,12],[10],301⟩) from rfl))
private theorem rec3994 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[4,8,12],[14],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[355]? = some (⟨50,(8),[4,8,12],[14],331⟩) from rfl))
private theorem rec4000 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[12],[6],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[361]? = some (⟨50,(8),[12],[6],331⟩) from rfl))
private theorem rec4005 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[4,8,12],[10],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[366]? = some (⟨50,(9),[4,8,12],[10],302⟩) from rfl))
private theorem rec4006 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[4,8,12],[14],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[367]? = some (⟨50,(9),[4,8,12],[14],332⟩) from rfl))
private theorem rec4012 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[12],[6],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[373]? = some (⟨50,(9),[12],[6],332⟩) from rfl))
private theorem rec4017 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[4,8,12],[10],303⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[378]? = some (⟨50,(10),[4,8,12],[10],303⟩) from rfl))
private theorem rec4018 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[4,8,12],[14],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[379]? = some (⟨50,(10),[4,8,12],[14],333⟩) from rfl))
private theorem rec4024 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[12],[6],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[385]? = some (⟨50,(10),[12],[6],333⟩) from rfl))
private theorem rec4029 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[4,8,12],[10],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[390]? = some (⟨50,(11),[4,8,12],[10],304⟩) from rfl))
private theorem rec4030 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[4,8,12],[14],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[391]? = some (⟨50,(11),[4,8,12],[14],334⟩) from rfl))
private theorem rec4036 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[12],[6],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[397]? = some (⟨50,(11),[12],[6],334⟩) from rfl))
private theorem rec4041 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[4,8,12],[10],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[402]? = some (⟨50,(12),[4,8,12],[10],301⟩) from rfl))
private theorem rec4042 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[4,8,12],[14],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[403]? = some (⟨50,(12),[4,8,12],[14],331⟩) from rfl))
private theorem rec4048 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[12],[6],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[409]? = some (⟨50,(12),[12],[6],331⟩) from rfl))
private theorem rec4053 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[4,8,12],[10],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[414]? = some (⟨50,(13),[4,8,12],[10],302⟩) from rfl))
private theorem rec4054 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[4,8,12],[14],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[415]? = some (⟨50,(13),[4,8,12],[14],332⟩) from rfl))
private theorem rec4060 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[12],[6],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[421]? = some (⟨50,(13),[12],[6],332⟩) from rfl))
private theorem rec4065 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[4,8,12],[10],306⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[426]? = some (⟨50,(14),[4,8,12],[10],306⟩) from rfl))
private theorem rec4066 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[4,8,12],[14],336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[427]? = some (⟨50,(14),[4,8,12],[14],336⟩) from rfl))
private theorem rec4072 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[12],[6],336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[433]? = some (⟨50,(14),[12],[6],336⟩) from rfl))
private theorem rec4077 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[4,8,12],[10],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[438]? = some (⟨50,(15),[4,8,12],[10],304⟩) from rfl))
private theorem rec4078 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[4,8,12],[14],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[439]? = some (⟨50,(15),[4,8,12],[14],334⟩) from rfl))
private theorem rec4084 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[12],[6],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[445]? = some (⟨50,(15),[12],[6],334⟩) from rfl))
private theorem rec4090 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[3,4,7,8,12],[10],279⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[451]? = some (⟨53,(0),[3,4,7,8,12],[10],279⟩) from rfl))
private theorem rec4091 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[4,8,12],[14],325⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[452]? = some (⟨53,(0),[4,8,12],[14],325⟩) from rfl))
private theorem rec4100 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[12],[6],360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[461]? = some (⟨53,(0),[12],[6],360⟩) from rfl))
private theorem rec4106 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[3,4,7,8,12],[10],280⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[467]? = some (⟨53,(1),[3,4,7,8,12],[10],280⟩) from rfl))
private theorem rec4107 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[4,8,12],[14],326⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[468]? = some (⟨53,(1),[4,8,12],[14],326⟩) from rfl))
private theorem rec4116 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[12],[6],361⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[477]? = some (⟨53,(1),[12],[6],361⟩) from rfl))
private theorem rec4122 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[3,4,7,8,12],[10],281⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[483]? = some (⟨53,(2),[3,4,7,8,12],[10],281⟩) from rfl))
private theorem rec4123 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[4,8,12],[14],327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[484]? = some (⟨53,(2),[4,8,12],[14],327⟩) from rfl))
private theorem rec4131 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[12],[6],362⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[492]? = some (⟨53,(2),[12],[6],362⟩) from rfl))
private theorem rec4137 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[3,4,7,8,12],[10],282⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[498]? = some (⟨53,(3),[3,4,7,8,12],[10],282⟩) from rfl))
private theorem rec4138 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[4,8,12],[14],328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[499]? = some (⟨53,(3),[4,8,12],[14],328⟩) from rfl))
private theorem rec4147 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[12],[6],363⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[508]? = some (⟨53,(3),[12],[6],363⟩) from rfl))
private theorem rec4280 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(0),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[131]? = some (⟨57,(0),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4283 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(0),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[134]? = some (⟨57,(0),[12],[6],2⟩) from rfl))
private theorem rec4286 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(1),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[137]? = some (⟨57,(1),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4289 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(1),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[140]? = some (⟨57,(1),[12],[6],2⟩) from rfl))
private theorem rec4294 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[4,8,12],[10],311⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[145]? = some (⟨57,(2),[4,8,12],[10],311⟩) from rfl))
private theorem rec4295 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[4,8,12],[14],337⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[146]? = some (⟨57,(2),[4,8,12],[14],337⟩) from rfl))
private theorem rec4301 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[12],[6],337⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[152]? = some (⟨57,(2),[12],[6],337⟩) from rfl))
private theorem rec4304 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(3),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[155]? = some (⟨57,(3),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4307 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(3),[12],[6],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[158]? = some (⟨57,(3),[12],[6],101⟩) from rfl))
private theorem rec4310 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(4),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[161]? = some (⟨57,(4),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4313 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(4),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[164]? = some (⟨57,(4),[12],[6],2⟩) from rfl))
private theorem rec4316 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(5),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[167]? = some (⟨57,(5),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4319 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(5),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[170]? = some (⟨57,(5),[12],[6],2⟩) from rfl))
private theorem rec4325 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[4,8,12],[10],284⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[176]? = some (⟨57,(6),[4,8,12],[10],284⟩) from rfl))
private theorem rec4326 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[4,8,12],[14],338⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[177]? = some (⟨57,(6),[4,8,12],[14],338⟩) from rfl))
private theorem rec4332 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[12],[6],338⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[183]? = some (⟨57,(6),[12],[6],338⟩) from rfl))
private theorem rec4335 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(7),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[186]? = some (⟨57,(7),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4338 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(7),[12],[6],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[189]? = some (⟨57,(7),[12],[6],101⟩) from rfl))
private theorem rec4341 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(8),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[192]? = some (⟨57,(8),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4344 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(8),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[195]? = some (⟨57,(8),[12],[6],2⟩) from rfl))
private theorem rec4347 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(9),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[198]? = some (⟨57,(9),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4350 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(9),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[201]? = some (⟨57,(9),[12],[6],2⟩) from rfl))
private theorem rec4356 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[4,8,12],[10],285⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[207]? = some (⟨57,(10),[4,8,12],[10],285⟩) from rfl))
private theorem rec4357 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[4,8,12],[14],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[208]? = some (⟨57,(10),[4,8,12],[14],339⟩) from rfl))
private theorem rec4363 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[12],[6],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[214]? = some (⟨57,(10),[12],[6],339⟩) from rfl))
private theorem rec4366 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(11),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[217]? = some (⟨57,(11),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4369 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(11),[12],[6],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[220]? = some (⟨57,(11),[12],[6],101⟩) from rfl))
private theorem rec4372 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(12),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[223]? = some (⟨57,(12),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4375 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(12),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[226]? = some (⟨57,(12),[12],[6],2⟩) from rfl))
private theorem rec4378 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(13),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[229]? = some (⟨57,(13),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4381 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(13),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[232]? = some (⟨57,(13),[12],[6],2⟩) from rfl))
private theorem rec4384 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(14),[4,8,12],[10,14],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[235]? = some (⟨57,(14),[4,8,12],[10,14],286⟩) from rfl))
private theorem rec4387 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(14),[12],[6],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[238]? = some (⟨57,(14),[12],[6],286⟩) from rfl))
private theorem rec4390 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(15),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[241]? = some (⟨57,(15),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4393 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(15),[12],[6],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[244]? = some (⟨57,(15),[12],[6],101⟩) from rfl))
private theorem rec4396 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(16),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[247]? = some (⟨57,(16),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4399 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(16),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[250]? = some (⟨57,(16),[12],[6],2⟩) from rfl))
private theorem rec4402 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(17),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[253]? = some (⟨57,(17),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4405 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(17),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[256]? = some (⟨57,(17),[12],[6],2⟩) from rfl))
private theorem rec4408 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(18),[4,8,12],[10,14],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[259]? = some (⟨57,(18),[4,8,12],[10,14],287⟩) from rfl))
private theorem rec4411 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(18),[12],[6],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[262]? = some (⟨57,(18),[12],[6],287⟩) from rfl))
private theorem rec4414 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(19),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[265]? = some (⟨57,(19),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4417 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 57 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(19),[12],[6],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[268]? = some (⟨57,(19),[12],[6],101⟩) from rfl))
private theorem rec16064 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(0),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1143]? = some (⟨497,(0),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16065 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(0),[12],[6],1534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1144]? = some (⟨497,(0),[12],[6],1534⟩) from rfl))
private theorem rec16066 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(1),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1145]? = some (⟨497,(1),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16067 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(1),[12],[6],1711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1146]? = some (⟨497,(1),[12],[6],1711⟩) from rfl))
private theorem rec16068 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(2),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1147]? = some (⟨497,(2),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16069 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(2),[12],[6],1712⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1148]? = some (⟨497,(2),[12],[6],1712⟩) from rfl))
private theorem rec16070 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(3),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1149]? = some (⟨497,(3),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16071 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(3),[12],[6],1711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1150]? = some (⟨497,(3),[12],[6],1711⟩) from rfl))
private theorem rec16072 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(4),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1151]? = some (⟨497,(4),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16073 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(4),[12],[6],1713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1152]? = some (⟨497,(4),[12],[6],1713⟩) from rfl))
private theorem rec16074 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(5),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1153]? = some (⟨497,(5),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16075 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(5),[12],[6],1534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1154]? = some (⟨497,(5),[12],[6],1534⟩) from rfl))
private theorem rec16076 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(6),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1155]? = some (⟨497,(6),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16077 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(6),[12],[6],1711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1156]? = some (⟨497,(6),[12],[6],1711⟩) from rfl))
private theorem rec16078 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(7),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1157]? = some (⟨497,(7),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16079 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(7),[12],[6],1712⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1158]? = some (⟨497,(7),[12],[6],1712⟩) from rfl))
private theorem rec16080 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(8),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1159]? = some (⟨497,(8),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16081 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(8),[12],[6],1711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1160]? = some (⟨497,(8),[12],[6],1711⟩) from rfl))
private theorem rec16082 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(9),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1161]? = some (⟨497,(9),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16083 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 497 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(9),[12],[6],1713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1162]? = some (⟨497,(9),[12],[6],1713⟩) from rfl))
private theorem rec16084 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(0),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1163]? = some (⟨500,(0),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16085 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(0),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1164]? = some (⟨500,(0),[12],[6],2⟩) from rfl))
private theorem rec16086 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(1),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1165]? = some (⟨500,(1),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16087 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(1),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1166]? = some (⟨500,(1),[12],[6],2⟩) from rfl))
private theorem rec16088 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(2),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1167]? = some (⟨500,(2),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16089 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(2),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1168]? = some (⟨500,(2),[12],[6],2⟩) from rfl))
private theorem rec16090 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(3),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1169]? = some (⟨500,(3),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16091 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(3),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1170]? = some (⟨500,(3),[12],[6],2⟩) from rfl))
private theorem rec16092 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(4),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1171]? = some (⟨500,(4),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16093 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(4),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1172]? = some (⟨500,(4),[12],[6],2⟩) from rfl))
private theorem rec16094 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(5),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1173]? = some (⟨500,(5),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16095 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(5),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1174]? = some (⟨500,(5),[12],[6],2⟩) from rfl))
private theorem rec16096 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(6),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1175]? = some (⟨500,(6),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16097 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(6),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1176]? = some (⟨500,(6),[12],[6],2⟩) from rfl))
private theorem rec16098 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(7),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1177]? = some (⟨500,(7),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16099 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(7),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1178]? = some (⟨500,(7),[12],[6],2⟩) from rfl))
private theorem rec16100 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(8),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1179]? = some (⟨500,(8),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16101 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(8),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1180]? = some (⟨500,(8),[12],[6],2⟩) from rfl))
private theorem rec16102 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(9),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1181]? = some (⟨500,(9),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16103 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 500 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(9),[12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1182]? = some (⟨500,(9),[12],[6],2⟩) from rfl))
private theorem rec16104 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 503 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(0),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1183]? = some (⟨503,(0),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16106 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 503 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(0),[8,12],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1185]? = some (⟨503,(0),[8,12],[10],1266⟩) from rfl))
private theorem rec16107 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 503 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(0),[12],[6],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1186]? = some (⟨503,(0),[12],[6],98⟩) from rfl))
private theorem rec16108 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 503 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(1),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1187]? = some (⟨503,(1),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16109 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 503 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(1),[12],[6],1258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1188]? = some (⟨503,(1),[12],[6],1258⟩) from rfl))
private theorem rec16110 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 503 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(2),[4,8,12,16],[14],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1189]? = some (⟨503,(2),[4,8,12,16],[14],29⟩) from rfl))
private theorem rec16111 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 503 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(2),[4,8,12,16],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1190]? = some (⟨503,(2),[4,8,12,16],[10],1266⟩) from rfl))
private theorem rec16112 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 503 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(2),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1191]? = some (⟨503,(2),[12],[6],3⟩) from rfl))
private theorem rec16113 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 503 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(3),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1192]? = some (⟨503,(3),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec16114 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 503 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(3),[4,8,12,16],[14],1264⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1193]? = some (⟨503,(3),[4,8,12,16],[14],1264⟩) from rfl))
private theorem rec16115 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 503 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(3),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1194]? = some (⟨503,(3),[12],[6],3⟩) from rfl))
private theorem rec16298 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(0),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[90]? = some (⟨552,(0),[12],[6],3⟩) from rfl))
private theorem rec16299 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(0),[12],[10],1657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[91]? = some (⟨552,(0),[12],[10],1657⟩) from rfl))
private theorem rec16300 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(0),[12],[14],1660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[92]? = some (⟨552,(0),[12],[14],1660⟩) from rfl))
private theorem rec16305 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(1),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[97]? = some (⟨552,(1),[12],[6],3⟩) from rfl))
private theorem rec16306 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(1),[12],[10],1658⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[98]? = some (⟨552,(1),[12],[10],1658⟩) from rfl))
private theorem rec16307 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(1),[12],[14],1661⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[99]? = some (⟨552,(1),[12],[14],1661⟩) from rfl))
private theorem rec16312 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(2),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[104]? = some (⟨552,(2),[12],[6],3⟩) from rfl))
private theorem rec16313 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(2),[12],[10],1657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[105]? = some (⟨552,(2),[12],[10],1657⟩) from rfl))
private theorem rec16314 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(2),[12],[14],1660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[106]? = some (⟨552,(2),[12],[14],1660⟩) from rfl))
private theorem rec16319 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(3),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[111]? = some (⟨552,(3),[12],[6],3⟩) from rfl))
private theorem rec16320 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(3),[12],[10],1659⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[112]? = some (⟨552,(3),[12],[10],1659⟩) from rfl))
private theorem rec16321 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(3),[12],[14],1662⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[113]? = some (⟨552,(3),[12],[14],1662⟩) from rfl))
private theorem rec16326 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(4),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[118]? = some (⟨552,(4),[12],[6],3⟩) from rfl))
private theorem rec16327 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(4),[12],[10],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[119]? = some (⟨552,(4),[12],[10],256⟩) from rfl))
private theorem rec16328 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(4),[12],[14],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[120]? = some (⟨552,(4),[12],[14],315⟩) from rfl))
private theorem rec16333 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(5),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[125]? = some (⟨552,(5),[12],[6],3⟩) from rfl))
private theorem rec16334 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(5),[12],[10],1657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[126]? = some (⟨552,(5),[12],[10],1657⟩) from rfl))
private theorem rec16335 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(5),[12],[14],1660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[127]? = some (⟨552,(5),[12],[14],1660⟩) from rfl))
private theorem rec16340 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(6),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[132]? = some (⟨552,(6),[12],[6],3⟩) from rfl))
private theorem rec16341 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(6),[12],[10],1658⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[133]? = some (⟨552,(6),[12],[10],1658⟩) from rfl))
private theorem rec16342 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(6),[12],[14],1661⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[134]? = some (⟨552,(6),[12],[14],1661⟩) from rfl))
private theorem rec16347 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(7),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[139]? = some (⟨552,(7),[12],[6],3⟩) from rfl))
private theorem rec16348 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(7),[12],[10],1657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[140]? = some (⟨552,(7),[12],[10],1657⟩) from rfl))
private theorem rec16349 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(7),[12],[14],1660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[141]? = some (⟨552,(7),[12],[14],1660⟩) from rfl))
private theorem rec16354 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(8),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[146]? = some (⟨552,(8),[12],[6],3⟩) from rfl))
private theorem rec16355 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(8),[12],[10],1659⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[147]? = some (⟨552,(8),[12],[10],1659⟩) from rfl))
private theorem rec16356 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(8),[12],[14],1662⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[148]? = some (⟨552,(8),[12],[14],1662⟩) from rfl))
private theorem rec16361 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 552 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(9),[12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[153]? = some (⟨552,(9),[12],[6],3⟩) from rfl))
private theorem rec16362 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 552 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(9),[12],[10],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[154]? = some (⟨552,(9),[12],[10],256⟩) from rfl))
private theorem rec16363 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 552 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(9),[12],[14],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[155]? = some (⟨552,(9),[12],[14],315⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 12).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 12)).drop 0).take 16, section14Recorded section14Catalog 12 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 12 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 12).plans.drop 2).take 1 = [⟨3,38,[([1],[]),([2],[]),([3],[1])],false,[(616,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(552,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(553,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(617,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(618,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 12)).drop 0).take 16 = [⟨3,0,[⟨true,false,15⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨3,1,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,2,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,3,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,4,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨3,5,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,6,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,7,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,8,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨3,9,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨3,10,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨3,11,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨3,12,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨3,13,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨3,14,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨3,15,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec3027 12 0 (by decide) (by decide)
  · left
    exact rec3046 12 1 (by decide) (by decide)
  · left
    exact rec3051 12 2 (by decide) (by decide)
  · left
    exact rec3058 12 3 (by decide) (by decide)
  · left
    exact rec3027 12 4 (by decide) (by decide)
  · left
    exact rec3036 12 5 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(616,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(552,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(553,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(617,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(618,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 616)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 497)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16065 12 6 (by decide) (by decide)
      · right
        exact rec16067 12 6 (by decide) (by decide)
      · right
        exact rec16069 12 6 (by decide) (by decide)
      · right
        exact rec16071 12 6 (by decide) (by decide)
      · right
        exact rec16073 12 6 (by decide) (by decide)
      · right
        exact rec16075 12 6 (by decide) (by decide)
      · right
        exact rec16077 12 6 (by decide) (by decide)
      · right
        exact rec16079 12 6 (by decide) (by decide)
      · right
        exact rec16081 12 6 (by decide) (by decide)
      · right
        exact rec16083 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 498)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 552)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16298 12 6 (by decide) (by decide)
      · right
        exact rec16305 12 6 (by decide) (by decide)
      · right
        exact rec16312 12 6 (by decide) (by decide)
      · right
        exact rec16319 12 6 (by decide) (by decide)
      · right
        exact rec16326 12 6 (by decide) (by decide)
      · right
        exact rec16333 12 6 (by decide) (by decide)
      · right
        exact rec16340 12 6 (by decide) (by decide)
      · right
        exact rec16347 12 6 (by decide) (by decide)
      · right
        exact rec16354 12 6 (by decide) (by decide)
      · right
        exact rec16361 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 553)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 499)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 500)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16085 12 6 (by decide) (by decide)
      · right
        exact rec16087 12 6 (by decide) (by decide)
      · right
        exact rec16089 12 6 (by decide) (by decide)
      · right
        exact rec16091 12 6 (by decide) (by decide)
      · right
        exact rec16093 12 6 (by decide) (by decide)
      · right
        exact rec16095 12 6 (by decide) (by decide)
      · right
        exact rec16097 12 6 (by decide) (by decide)
      · right
        exact rec16099 12 6 (by decide) (by decide)
      · right
        exact rec16101 12 6 (by decide) (by decide)
      · right
        exact rec16103 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 501)).length = 10 := by decide +kernel
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
        exact rec3575 12 6 (by decide) (by decide)
      · right
        exact rec3585 12 6 (by decide) (by decide)
      · right
        exact rec3596 12 6 (by decide) (by decide)
      · right
        exact rec3607 12 6 (by decide) (by decide)
      · right
        exact rec3618 12 6 (by decide) (by decide)
      · right
        exact rec3628 12 6 (by decide) (by decide)
      · right
        exact rec3638 12 6 (by decide) (by decide)
      · right
        exact rec3654 12 6 (by decide) (by decide)
      · right
        exact rec3671 12 6 (by decide) (by decide)
      · right
        exact rec3688 12 6 (by decide) (by decide)
      · right
        exact rec3698 12 6 (by decide) (by decide)
      · right
        exact rec3708 12 6 (by decide) (by decide)
      · right
        exact rec3724 12 6 (by decide) (by decide)
      · right
        exact rec3742 12 6 (by decide) (by decide)
      · right
        exact rec3758 12 6 (by decide) (by decide)
      · right
        exact rec3768 12 6 (by decide) (by decide)
      · right
        exact rec3778 12 6 (by decide) (by decide)
      · right
        exact rec3793 12 6 (by decide) (by decide)
      · right
        exact rec3810 12 6 (by decide) (by decide)
      · right
        exact rec3825 12 6 (by decide) (by decide)
      · right
        exact rec3835 12 6 (by decide) (by decide)
      · right
        exact rec3845 12 6 (by decide) (by decide)
      · right
        exact rec3860 12 6 (by decide) (by decide)
      · right
        exact rec3877 12 6 (by decide) (by decide)
      · right
        exact rec3892 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 48)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 49)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 50)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3904 12 6 (by decide) (by decide)
      · right
        exact rec3916 12 6 (by decide) (by decide)
      · right
        exact rec3928 12 6 (by decide) (by decide)
      · right
        exact rec3940 12 6 (by decide) (by decide)
      · right
        exact rec3952 12 6 (by decide) (by decide)
      · right
        exact rec3964 12 6 (by decide) (by decide)
      · right
        exact rec3976 12 6 (by decide) (by decide)
      · right
        exact rec3988 12 6 (by decide) (by decide)
      · right
        exact rec4000 12 6 (by decide) (by decide)
      · right
        exact rec4012 12 6 (by decide) (by decide)
      · right
        exact rec4024 12 6 (by decide) (by decide)
      · right
        exact rec4036 12 6 (by decide) (by decide)
      · right
        exact rec4048 12 6 (by decide) (by decide)
      · right
        exact rec4060 12 6 (by decide) (by decide)
      · right
        exact rec4072 12 6 (by decide) (by decide)
      · right
        exact rec4084 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 51)).length = 4 := by decide +kernel
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
        exact rec4100 12 6 (by decide) (by decide)
      · right
        exact rec4116 12 6 (by decide) (by decide)
      · right
        exact rec4131 12 6 (by decide) (by decide)
      · right
        exact rec4147 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 617)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 503)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16107 12 6 (by decide) (by decide)
      · right
        exact rec16109 12 6 (by decide) (by decide)
      · right
        exact rec16112 12 6 (by decide) (by decide)
      · right
        exact rec16115 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 504)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 57)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4283 12 6 (by decide) (by decide)
      · right
        exact rec4289 12 6 (by decide) (by decide)
      · right
        exact rec4301 12 6 (by decide) (by decide)
      · right
        exact rec4307 12 6 (by decide) (by decide)
      · right
        exact rec4313 12 6 (by decide) (by decide)
      · right
        exact rec4319 12 6 (by decide) (by decide)
      · right
        exact rec4332 12 6 (by decide) (by decide)
      · right
        exact rec4338 12 6 (by decide) (by decide)
      · right
        exact rec4344 12 6 (by decide) (by decide)
      · right
        exact rec4350 12 6 (by decide) (by decide)
      · right
        exact rec4363 12 6 (by decide) (by decide)
      · right
        exact rec4369 12 6 (by decide) (by decide)
      · right
        exact rec4375 12 6 (by decide) (by decide)
      · right
        exact rec4381 12 6 (by decide) (by decide)
      · right
        exact rec4387 12 6 (by decide) (by decide)
      · right
        exact rec4393 12 6 (by decide) (by decide)
      · right
        exact rec4399 12 6 (by decide) (by decide)
      · right
        exact rec4405 12 6 (by decide) (by decide)
      · right
        exact rec4411 12 6 (by decide) (by decide)
      · right
        exact rec4417 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 618)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 59)).length = 10 := by decide +kernel
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
    exact rec3052 12 7 (by decide) (by decide)
  · left
    exact rec3045 12 8 (by decide) (by decide)
  · left
    exact rec3047 12 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(616,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(552,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(553,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(617,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(618,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 616)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 497)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16064 12 10 (by decide) (by decide)
      · right
        exact rec16066 12 10 (by decide) (by decide)
      · right
        exact rec16068 12 10 (by decide) (by decide)
      · right
        exact rec16070 12 10 (by decide) (by decide)
      · right
        exact rec16072 12 10 (by decide) (by decide)
      · right
        exact rec16074 12 10 (by decide) (by decide)
      · right
        exact rec16076 12 10 (by decide) (by decide)
      · right
        exact rec16078 12 10 (by decide) (by decide)
      · right
        exact rec16080 12 10 (by decide) (by decide)
      · right
        exact rec16082 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 498)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 552)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16299 12 10 (by decide) (by decide)
      · right
        exact rec16306 12 10 (by decide) (by decide)
      · right
        exact rec16313 12 10 (by decide) (by decide)
      · right
        exact rec16320 12 10 (by decide) (by decide)
      · right
        exact rec16327 12 10 (by decide) (by decide)
      · right
        exact rec16334 12 10 (by decide) (by decide)
      · right
        exact rec16341 12 10 (by decide) (by decide)
      · right
        exact rec16348 12 10 (by decide) (by decide)
      · right
        exact rec16355 12 10 (by decide) (by decide)
      · right
        exact rec16362 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 553)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 499)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 500)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16084 12 10 (by decide) (by decide)
      · right
        exact rec16086 12 10 (by decide) (by decide)
      · right
        exact rec16088 12 10 (by decide) (by decide)
      · right
        exact rec16090 12 10 (by decide) (by decide)
      · right
        exact rec16092 12 10 (by decide) (by decide)
      · right
        exact rec16094 12 10 (by decide) (by decide)
      · right
        exact rec16096 12 10 (by decide) (by decide)
      · right
        exact rec16098 12 10 (by decide) (by decide)
      · right
        exact rec16100 12 10 (by decide) (by decide)
      · right
        exact rec16102 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 501)).length = 10 := by decide +kernel
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
        exact rec3568 12 10 (by decide) (by decide)
      · right
        exact rec3578 12 10 (by decide) (by decide)
      · right
        exact rec3588 12 10 (by decide) (by decide)
      · right
        exact rec3599 12 10 (by decide) (by decide)
      · right
        exact rec3610 12 10 (by decide) (by decide)
      · right
        exact rec3621 12 10 (by decide) (by decide)
      · right
        exact rec3631 12 10 (by decide) (by decide)
      · right
        exact rec3643 12 10 (by decide) (by decide)
      · right
        exact rec3665 12 10 (by decide) (by decide)
      · right
        exact rec3677 12 10 (by decide) (by decide)
      · right
        exact rec3691 12 10 (by decide) (by decide)
      · right
        exact rec3701 12 10 (by decide) (by decide)
      · right
        exact rec3713 12 10 (by decide) (by decide)
      · right
        exact rec3736 12 10 (by decide) (by decide)
      · right
        exact rec3747 12 10 (by decide) (by decide)
      · right
        exact rec3761 12 10 (by decide) (by decide)
      · right
        exact rec3771 12 10 (by decide) (by decide)
      · right
        exact rec3783 12 10 (by decide) (by decide)
      · right
        exact rec3804 12 10 (by decide) (by decide)
      · right
        exact rec3815 12 10 (by decide) (by decide)
      · right
        exact rec3828 12 10 (by decide) (by decide)
      · right
        exact rec3838 12 10 (by decide) (by decide)
      · right
        exact rec3850 12 10 (by decide) (by decide)
      · right
        exact rec3871 12 10 (by decide) (by decide)
      · right
        exact rec3882 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 48)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 49)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 50)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3897 12 10 (by decide) (by decide)
      · right
        exact rec3909 12 10 (by decide) (by decide)
      · right
        exact rec3921 12 10 (by decide) (by decide)
      · right
        exact rec3933 12 10 (by decide) (by decide)
      · right
        exact rec3945 12 10 (by decide) (by decide)
      · right
        exact rec3957 12 10 (by decide) (by decide)
      · right
        exact rec3969 12 10 (by decide) (by decide)
      · right
        exact rec3981 12 10 (by decide) (by decide)
      · right
        exact rec3993 12 10 (by decide) (by decide)
      · right
        exact rec4005 12 10 (by decide) (by decide)
      · right
        exact rec4017 12 10 (by decide) (by decide)
      · right
        exact rec4029 12 10 (by decide) (by decide)
      · right
        exact rec4041 12 10 (by decide) (by decide)
      · right
        exact rec4053 12 10 (by decide) (by decide)
      · right
        exact rec4065 12 10 (by decide) (by decide)
      · right
        exact rec4077 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 51)).length = 4 := by decide +kernel
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
        exact rec4090 12 10 (by decide) (by decide)
      · right
        exact rec4106 12 10 (by decide) (by decide)
      · right
        exact rec4122 12 10 (by decide) (by decide)
      · right
        exact rec4137 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 617)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 503)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16106 12 10 (by decide) (by decide)
      · right
        exact rec16108 12 10 (by decide) (by decide)
      · right
        exact rec16111 12 10 (by decide) (by decide)
      · right
        exact rec16113 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 504)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 57)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4280 12 10 (by decide) (by decide)
      · right
        exact rec4286 12 10 (by decide) (by decide)
      · right
        exact rec4294 12 10 (by decide) (by decide)
      · right
        exact rec4304 12 10 (by decide) (by decide)
      · right
        exact rec4310 12 10 (by decide) (by decide)
      · right
        exact rec4316 12 10 (by decide) (by decide)
      · right
        exact rec4325 12 10 (by decide) (by decide)
      · right
        exact rec4335 12 10 (by decide) (by decide)
      · right
        exact rec4341 12 10 (by decide) (by decide)
      · right
        exact rec4347 12 10 (by decide) (by decide)
      · right
        exact rec4356 12 10 (by decide) (by decide)
      · right
        exact rec4366 12 10 (by decide) (by decide)
      · right
        exact rec4372 12 10 (by decide) (by decide)
      · right
        exact rec4378 12 10 (by decide) (by decide)
      · right
        exact rec4384 12 10 (by decide) (by decide)
      · right
        exact rec4390 12 10 (by decide) (by decide)
      · right
        exact rec4396 12 10 (by decide) (by decide)
      · right
        exact rec4402 12 10 (by decide) (by decide)
      · right
        exact rec4408 12 10 (by decide) (by decide)
      · right
        exact rec4414 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 618)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 59)).length = 10 := by decide +kernel
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
    exact rec3048 12 11 (by decide) (by decide)
  · left
    exact rec3049 12 12 (by decide) (by decide)
  · left
    exact rec3050 12 13 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(616,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(552,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(553,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(617,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(618,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 616)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 497)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16064 12 14 (by decide) (by decide)
      · right
        exact rec16066 12 14 (by decide) (by decide)
      · right
        exact rec16068 12 14 (by decide) (by decide)
      · right
        exact rec16070 12 14 (by decide) (by decide)
      · right
        exact rec16072 12 14 (by decide) (by decide)
      · right
        exact rec16074 12 14 (by decide) (by decide)
      · right
        exact rec16076 12 14 (by decide) (by decide)
      · right
        exact rec16078 12 14 (by decide) (by decide)
      · right
        exact rec16080 12 14 (by decide) (by decide)
      · right
        exact rec16082 12 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 498)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 552)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16300 12 14 (by decide) (by decide)
      · right
        exact rec16307 12 14 (by decide) (by decide)
      · right
        exact rec16314 12 14 (by decide) (by decide)
      · right
        exact rec16321 12 14 (by decide) (by decide)
      · right
        exact rec16328 12 14 (by decide) (by decide)
      · right
        exact rec16335 12 14 (by decide) (by decide)
      · right
        exact rec16342 12 14 (by decide) (by decide)
      · right
        exact rec16349 12 14 (by decide) (by decide)
      · right
        exact rec16356 12 14 (by decide) (by decide)
      · right
        exact rec16363 12 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 553)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 499)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 500)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16084 12 14 (by decide) (by decide)
      · right
        exact rec16086 12 14 (by decide) (by decide)
      · right
        exact rec16088 12 14 (by decide) (by decide)
      · right
        exact rec16090 12 14 (by decide) (by decide)
      · right
        exact rec16092 12 14 (by decide) (by decide)
      · right
        exact rec16094 12 14 (by decide) (by decide)
      · right
        exact rec16096 12 14 (by decide) (by decide)
      · right
        exact rec16098 12 14 (by decide) (by decide)
      · right
        exact rec16100 12 14 (by decide) (by decide)
      · right
        exact rec16102 12 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 501)).length = 10 := by decide +kernel
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
        exact rec3570 12 14 (by decide) (by decide)
      · right
        exact rec3580 12 14 (by decide) (by decide)
      · right
        exact rec3590 12 14 (by decide) (by decide)
      · right
        exact rec3601 12 14 (by decide) (by decide)
      · right
        exact rec3612 12 14 (by decide) (by decide)
      · right
        exact rec3623 12 14 (by decide) (by decide)
      · right
        exact rec3633 12 14 (by decide) (by decide)
      · right
        exact rec3645 12 14 (by decide) (by decide)
      · right
        exact rec3661 12 14 (by decide) (by decide)
      · right
        exact rec3679 12 14 (by decide) (by decide)
      · right
        exact rec3693 12 14 (by decide) (by decide)
      · right
        exact rec3703 12 14 (by decide) (by decide)
      · right
        exact rec3715 12 14 (by decide) (by decide)
      · right
        exact rec3731 12 14 (by decide) (by decide)
      · right
        exact rec3749 12 14 (by decide) (by decide)
      · right
        exact rec3763 12 14 (by decide) (by decide)
      · right
        exact rec3773 12 14 (by decide) (by decide)
      · right
        exact rec3785 12 14 (by decide) (by decide)
      · right
        exact rec3800 12 14 (by decide) (by decide)
      · right
        exact rec3817 12 14 (by decide) (by decide)
      · right
        exact rec3830 12 14 (by decide) (by decide)
      · right
        exact rec3840 12 14 (by decide) (by decide)
      · right
        exact rec3852 12 14 (by decide) (by decide)
      · right
        exact rec3867 12 14 (by decide) (by decide)
      · right
        exact rec3884 12 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 48)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 49)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 50)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3898 12 14 (by decide) (by decide)
      · right
        exact rec3910 12 14 (by decide) (by decide)
      · right
        exact rec3922 12 14 (by decide) (by decide)
      · right
        exact rec3934 12 14 (by decide) (by decide)
      · right
        exact rec3946 12 14 (by decide) (by decide)
      · right
        exact rec3958 12 14 (by decide) (by decide)
      · right
        exact rec3970 12 14 (by decide) (by decide)
      · right
        exact rec3982 12 14 (by decide) (by decide)
      · right
        exact rec3994 12 14 (by decide) (by decide)
      · right
        exact rec4006 12 14 (by decide) (by decide)
      · right
        exact rec4018 12 14 (by decide) (by decide)
      · right
        exact rec4030 12 14 (by decide) (by decide)
      · right
        exact rec4042 12 14 (by decide) (by decide)
      · right
        exact rec4054 12 14 (by decide) (by decide)
      · right
        exact rec4066 12 14 (by decide) (by decide)
      · right
        exact rec4078 12 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 51)).length = 4 := by decide +kernel
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
        exact rec4091 12 14 (by decide) (by decide)
      · right
        exact rec4107 12 14 (by decide) (by decide)
      · right
        exact rec4123 12 14 (by decide) (by decide)
      · right
        exact rec4138 12 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 617)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 503)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16104 12 14 (by decide) (by decide)
      · right
        exact rec16108 12 14 (by decide) (by decide)
      · right
        exact rec16110 12 14 (by decide) (by decide)
      · right
        exact rec16114 12 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 504)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 57)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4280 12 14 (by decide) (by decide)
      · right
        exact rec4286 12 14 (by decide) (by decide)
      · right
        exact rec4295 12 14 (by decide) (by decide)
      · right
        exact rec4304 12 14 (by decide) (by decide)
      · right
        exact rec4310 12 14 (by decide) (by decide)
      · right
        exact rec4316 12 14 (by decide) (by decide)
      · right
        exact rec4326 12 14 (by decide) (by decide)
      · right
        exact rec4335 12 14 (by decide) (by decide)
      · right
        exact rec4341 12 14 (by decide) (by decide)
      · right
        exact rec4347 12 14 (by decide) (by decide)
      · right
        exact rec4357 12 14 (by decide) (by decide)
      · right
        exact rec4366 12 14 (by decide) (by decide)
      · right
        exact rec4372 12 14 (by decide) (by decide)
      · right
        exact rec4378 12 14 (by decide) (by decide)
      · right
        exact rec4384 12 14 (by decide) (by decide)
      · right
        exact rec4390 12 14 (by decide) (by decide)
      · right
        exact rec4396 12 14 (by decide) (by decide)
      · right
        exact rec4402 12 14 (by decide) (by decide)
      · right
        exact rec4408 12 14 (by decide) (by decide)
      · right
        exact rec4414 12 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 618)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 59)).length = 10 := by decide +kernel
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
    exact rec3052 12 15 (by decide) (by decide)
end Section14Coverage_12_2_p0_16

#print axioms solution
