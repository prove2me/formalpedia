-- Prove2me | solution 1 for Freiman.section14_s0016_coverage0002_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T22:03:23.741505+00:00
-- url     : https://prove2.me/submissions/5547917d-eaa5-449c-ab65-04ad3d277459

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
namespace Section14Coverage_16_2_p0_16
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
private theorem rec3053 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,8,16],[6],252⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[610]? = some (⟨38,(-1),[4,8,16],[6],252⟩) from rfl))
private theorem rec3054 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[4,16],[3],249⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[611]? = some (⟨38,(-1),[4,16],[3],249⟩) from rfl))
private theorem rec3217 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[4,8,16],[14],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[774]? = some (⟨42,(0),[4,8,16],[14],312⟩) from rfl))
private theorem rec3218 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[4,16],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[775]? = some (⟨42,(0),[4,16],[10],10⟩) from rfl))
private theorem rec3226 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[3,4,7,8,15,16],[10],254⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[783]? = some (⟨42,(1),[3,4,7,8,15,16],[10],254⟩) from rfl))
private theorem rec3228 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[4,8,16],[14],313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[785]? = some (⟨42,(1),[4,8,16],[14],313⟩) from rfl))
private theorem rec3236 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[3,4,7,8,15,16],[10],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[793]? = some (⟨42,(2),[3,4,7,8,15,16],[10],253⟩) from rfl))
private theorem rec3238 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[4,8,16],[14],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[795]? = some (⟨42,(2),[4,8,16],[14],312⟩) from rfl))
private theorem rec3246 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[3,4,7,8,15,16],[10],255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[803]? = some (⟨42,(3),[3,4,7,8,15,16],[10],255⟩) from rfl))
private theorem rec3248 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[4,8,16],[14],314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[805]? = some (⟨42,(3),[4,8,16],[14],314⟩) from rfl))
private theorem rec3256 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[3,4,7,8,15,16],[10],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[813]? = some (⟨42,(4),[3,4,7,8,15,16],[10],256⟩) from rfl))
private theorem rec3258 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[4,8,16],[14],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[815]? = some (⟨42,(4),[4,8,16],[14],315⟩) from rfl))
private theorem rec3268 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[4,8,16],[14],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[825]? = some (⟨42,(5),[4,8,16],[14],312⟩) from rfl))
private theorem rec3269 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[4,16],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[826]? = some (⟨42,(5),[4,16],[10],10⟩) from rfl))
private theorem rec3277 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[3,4,7,8,15,16],[10],254⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[834]? = some (⟨42,(6),[3,4,7,8,15,16],[10],254⟩) from rfl))
private theorem rec3279 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[4,8,16],[14],313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[836]? = some (⟨42,(6),[4,8,16],[14],313⟩) from rfl))
private theorem rec3287 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[3,4,7,8,15,16],[10],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[844]? = some (⟨42,(7),[3,4,7,8,15,16],[10],253⟩) from rfl))
private theorem rec3289 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[4,8,16],[14],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[846]? = some (⟨42,(7),[4,8,16],[14],312⟩) from rfl))
private theorem rec3297 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[3,4,7,8,15,16],[10],255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[854]? = some (⟨42,(8),[3,4,7,8,15,16],[10],255⟩) from rfl))
private theorem rec3299 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[4,8,16],[14],314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[856]? = some (⟨42,(8),[4,8,16],[14],314⟩) from rfl))
private theorem rec3307 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[3,4,7,8,15,16],[10],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[864]? = some (⟨42,(9),[3,4,7,8,15,16],[10],256⟩) from rfl))
private theorem rec3309 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[4,8,16],[14],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[866]? = some (⟨42,(9),[4,8,16],[14],315⟩) from rfl))
private theorem rec3319 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[4,8,16],[14],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[876]? = some (⟨42,(10),[4,8,16],[14],316⟩) from rfl))
private theorem rec3320 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[4,16],[10],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[877]? = some (⟨42,(10),[4,16],[10],18⟩) from rfl))
private theorem rec3328 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[3,4,7,8,15,16],[10],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[885]? = some (⟨42,(11),[3,4,7,8,15,16],[10],257⟩) from rfl))
private theorem rec3330 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[4,8,16],[14],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[887]? = some (⟨42,(11),[4,8,16],[14],316⟩) from rfl))
private theorem rec3338 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[3,4,7,8,15,16],[10],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[895]? = some (⟨42,(12),[3,4,7,8,15,16],[10],257⟩) from rfl))
private theorem rec3340 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[4,8,16],[14],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[897]? = some (⟨42,(12),[4,8,16],[14],316⟩) from rfl))
private theorem rec3348 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[3,4,7,8,15,16],[10],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[905]? = some (⟨42,(13),[3,4,7,8,15,16],[10],257⟩) from rfl))
private theorem rec3350 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[4,8,16],[14],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[907]? = some (⟨42,(13),[4,8,16],[14],316⟩) from rfl))
private theorem rec3358 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[3,4,7,8,15,16],[10],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[915]? = some (⟨42,(14),[3,4,7,8,15,16],[10],256⟩) from rfl))
private theorem rec3360 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[4,8,16],[14],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[917]? = some (⟨42,(14),[4,8,16],[14],315⟩) from rfl))
private theorem rec3370 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[4,8,16],[14],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[927]? = some (⟨42,(15),[4,8,16],[14],317⟩) from rfl))
private theorem rec3371 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[4,16],[10],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[928]? = some (⟨42,(15),[4,16],[10],21⟩) from rfl))
private theorem rec3379 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[3,4,7,8,15,16],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[936]? = some (⟨42,(16),[3,4,7,8,15,16],[10],258⟩) from rfl))
private theorem rec3381 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[4,8,16],[14],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[938]? = some (⟨42,(16),[4,8,16],[14],317⟩) from rfl))
private theorem rec3389 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[3,4,7,8,15,16],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[946]? = some (⟨42,(17),[3,4,7,8,15,16],[10],258⟩) from rfl))
private theorem rec3391 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[4,8,16],[14],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[948]? = some (⟨42,(17),[4,8,16],[14],317⟩) from rfl))
private theorem rec3399 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[3,4,7,8,15,16],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[956]? = some (⟨42,(18),[3,4,7,8,15,16],[10],258⟩) from rfl))
private theorem rec3401 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[4,8,16],[14],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[958]? = some (⟨42,(18),[4,8,16],[14],317⟩) from rfl))
private theorem rec3409 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[3,4,7,8,15,16],[10],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[966]? = some (⟨42,(19),[3,4,7,8,15,16],[10],258⟩) from rfl))
private theorem rec3411 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[4,8,16],[14],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[968]? = some (⟨42,(19),[4,8,16],[14],317⟩) from rfl))
private theorem rec3421 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[4,8,16],[14],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[978]? = some (⟨42,(20),[4,8,16],[14],318⟩) from rfl))
private theorem rec3422 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[4,16],[10],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[979]? = some (⟨42,(20),[4,16],[10],24⟩) from rfl))
private theorem rec3430 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[3,4,7,8,15,16],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[987]? = some (⟨42,(21),[3,4,7,8,15,16],[10],259⟩) from rfl))
private theorem rec3432 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[4,8,16],[14],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[989]? = some (⟨42,(21),[4,8,16],[14],318⟩) from rfl))
private theorem rec3440 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[3,4,7,8,15,16],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[997]? = some (⟨42,(22),[3,4,7,8,15,16],[10],259⟩) from rfl))
private theorem rec3442 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[4,8,16],[14],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[999]? = some (⟨42,(22),[4,8,16],[14],318⟩) from rfl))
private theorem rec3450 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[3,4,7,8,15,16],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1007]? = some (⟨42,(23),[3,4,7,8,15,16],[10],259⟩) from rfl))
private theorem rec3452 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[4,8,16],[14],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1009]? = some (⟨42,(23),[4,8,16],[14],318⟩) from rfl))
private theorem rec3460 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[3,4,7,8,15,16],[10],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1017]? = some (⟨42,(24),[3,4,7,8,15,16],[10],259⟩) from rfl))
private theorem rec3462 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[4,8,16],[14],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1019]? = some (⟨42,(24),[4,8,16],[14],318⟩) from rfl))
private theorem rec3568 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[3,4,7,8,12,15,16],[10],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1125]? = some (⟨47,(0),[3,4,7,8,12,15,16],[10],189⟩) from rfl))
private theorem rec3570 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[4,8,12,16],[14],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1127]? = some (⟨47,(0),[4,8,12,16],[14],189⟩) from rfl))
private theorem rec3578 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[3,4,7,8,12,15,16],[10],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1135]? = some (⟨47,(1),[3,4,7,8,12,15,16],[10],260⟩) from rfl))
private theorem rec3580 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[4,8,12,16],[14],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1137]? = some (⟨47,(1),[4,8,12,16],[14],260⟩) from rfl))
private theorem rec3588 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[3,4,7,8,12,15,16],[10],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1145]? = some (⟨47,(2),[3,4,7,8,12,15,16],[10],261⟩) from rfl))
private theorem rec3590 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[4,8,12,16],[14],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1147]? = some (⟨47,(2),[4,8,12,16],[14],261⟩) from rfl))
private theorem rec3599 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[3,4,7,8,12,15,16],[10],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1156]? = some (⟨47,(3),[3,4,7,8,12,15,16],[10],262⟩) from rfl))
private theorem rec3601 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[4,8,12,16],[14],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1158]? = some (⟨47,(3),[4,8,12,16],[14],262⟩) from rfl))
private theorem rec3610 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[3,4,7,8,12,15,16],[10],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1167]? = some (⟨47,(4),[3,4,7,8,12,15,16],[10],263⟩) from rfl))
private theorem rec3612 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[4,8,12,16],[14],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1169]? = some (⟨47,(4),[4,8,12,16],[14],263⟩) from rfl))
private theorem rec3621 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[3,4,7,8,12,15,16],[10],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1178]? = some (⟨47,(5),[3,4,7,8,12,15,16],[10],189⟩) from rfl))
private theorem rec3623 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[4,8,12,16],[14],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1180]? = some (⟨47,(5),[4,8,12,16],[14],189⟩) from rfl))
private theorem rec3631 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[3,4,7,8,12,15,16],[10],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1188]? = some (⟨47,(6),[3,4,7,8,12,15,16],[10],260⟩) from rfl))
private theorem rec3633 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[4,8,12,16],[14],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1190]? = some (⟨47,(6),[4,8,12,16],[14],260⟩) from rfl))
private theorem rec3643 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[3,4,7,8,12,15,16],[10],264⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[4]? = some (⟨47,(7),[3,4,7,8,12,15,16],[10],264⟩) from rfl))
private theorem rec3645 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[4,8,12,16],[14],319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[6]? = some (⟨47,(7),[4,8,12,16],[14],319⟩) from rfl))
private theorem rec3659 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[3,4,7,15,16],[10],265⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[20]? = some (⟨47,(8),[3,4,7,15,16],[10],265⟩) from rfl))
private theorem rec3661 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[4,8,12,16],[14],320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[22]? = some (⟨47,(8),[4,8,12,16],[14],320⟩) from rfl))
private theorem rec3677 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[3,4,7,8,12,15,16],[10],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[38]? = some (⟨47,(9),[3,4,7,8,12,15,16],[10],266⟩) from rfl))
private theorem rec3679 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[4,8,12,16],[14],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[40]? = some (⟨47,(9),[4,8,12,16],[14],321⟩) from rfl))
private theorem rec3691 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[3,4,7,8,12,15,16],[10],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[52]? = some (⟨47,(10),[3,4,7,8,12,15,16],[10],194⟩) from rfl))
private theorem rec3693 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[4,8,12,16],[14],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[54]? = some (⟨47,(10),[4,8,12,16],[14],194⟩) from rfl))
private theorem rec3701 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[3,4,7,8,12,15,16],[10],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[62]? = some (⟨47,(11),[3,4,7,8,12,15,16],[10],267⟩) from rfl))
private theorem rec3703 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[4,8,12,16],[14],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[64]? = some (⟨47,(11),[4,8,12,16],[14],267⟩) from rfl))
private theorem rec3713 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[3,4,7,8,12,15,16],[10],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[74]? = some (⟨47,(12),[3,4,7,8,12,15,16],[10],268⟩) from rfl))
private theorem rec3715 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[4,8,12,16],[14],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[76]? = some (⟨47,(12),[4,8,12,16],[14],322⟩) from rfl))
private theorem rec3729 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[3,4,7,15,16],[10],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[90]? = some (⟨47,(13),[3,4,7,15,16],[10],268⟩) from rfl))
private theorem rec3731 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[4,8,12,16],[14],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[92]? = some (⟨47,(13),[4,8,12,16],[14],322⟩) from rfl))
private theorem rec3747 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[3,4,7,8,12,15,16],[10],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[108]? = some (⟨47,(14),[3,4,7,8,12,15,16],[10],266⟩) from rfl))
private theorem rec3749 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[4,8,12,16],[14],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[110]? = some (⟨47,(14),[4,8,12,16],[14],321⟩) from rfl))
private theorem rec3761 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[3,4,7,8,12,15,16],[10],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[122]? = some (⟨47,(15),[3,4,7,8,12,15,16],[10],196⟩) from rfl))
private theorem rec3763 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[4,8,12,16],[14],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[124]? = some (⟨47,(15),[4,8,12,16],[14],196⟩) from rfl))
private theorem rec3771 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[3,4,7,8,12,15,16],[10],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[132]? = some (⟨47,(16),[3,4,7,8,12,15,16],[10],269⟩) from rfl))
private theorem rec3773 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[4,8,12,16],[14],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[134]? = some (⟨47,(16),[4,8,12,16],[14],269⟩) from rfl))
private theorem rec3783 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[3,4,7,8,12,15,16],[10],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[144]? = some (⟨47,(17),[3,4,7,8,12,15,16],[10],270⟩) from rfl))
private theorem rec3785 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[4,8,12,16],[14],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[146]? = some (⟨47,(17),[4,8,12,16],[14],323⟩) from rfl))
private theorem rec3798 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[3,4,7,15,16],[10],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[159]? = some (⟨47,(18),[3,4,7,15,16],[10],270⟩) from rfl))
private theorem rec3800 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[4,8,12,16],[14],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[161]? = some (⟨47,(18),[4,8,12,16],[14],323⟩) from rfl))
private theorem rec3815 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[3,4,7,8,12,15,16],[10],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[176]? = some (⟨47,(19),[3,4,7,8,12,15,16],[10],270⟩) from rfl))
private theorem rec3817 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[4,8,12,16],[14],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[178]? = some (⟨47,(19),[4,8,12,16],[14],323⟩) from rfl))
private theorem rec3828 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[3,4,7,8,12,15,16],[10],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[189]? = some (⟨47,(20),[3,4,7,8,12,15,16],[10],198⟩) from rfl))
private theorem rec3830 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[4,8,12,16],[14],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[191]? = some (⟨47,(20),[4,8,12,16],[14],198⟩) from rfl))
private theorem rec3838 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[3,4,7,8,12,15,16],[10],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[199]? = some (⟨47,(21),[3,4,7,8,12,15,16],[10],271⟩) from rfl))
private theorem rec3840 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[4,8,12,16],[14],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[201]? = some (⟨47,(21),[4,8,12,16],[14],271⟩) from rfl))
private theorem rec3850 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[3,4,7,8,12,15,16],[10],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[211]? = some (⟨47,(22),[3,4,7,8,12,15,16],[10],272⟩) from rfl))
private theorem rec3852 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[4,8,12,16],[14],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[213]? = some (⟨47,(22),[4,8,12,16],[14],324⟩) from rfl))
private theorem rec3865 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[3,4,7,15,16],[10],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[226]? = some (⟨47,(23),[3,4,7,15,16],[10],272⟩) from rfl))
private theorem rec3867 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[4,8,12,16],[14],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[228]? = some (⟨47,(23),[4,8,12,16],[14],324⟩) from rfl))
private theorem rec3882 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[3,4,7,8,12,15,16],[10],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[243]? = some (⟨47,(24),[3,4,7,8,12,15,16],[10],272⟩) from rfl))
private theorem rec3884 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[4,8,12,16],[14],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[245]? = some (⟨47,(24),[4,8,12,16],[14],324⟩) from rfl))
private theorem rec16064 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(0),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1143]? = some (⟨497,(0),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16066 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(1),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1145]? = some (⟨497,(1),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16068 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(2),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1147]? = some (⟨497,(2),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16070 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(3),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1149]? = some (⟨497,(3),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16072 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(4),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1151]? = some (⟨497,(4),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16074 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(5),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1153]? = some (⟨497,(5),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16076 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(6),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1155]? = some (⟨497,(6),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16078 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(7),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1157]? = some (⟨497,(7),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16080 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(8),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1159]? = some (⟨497,(8),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16082 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 497 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨497,(9),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1161]? = some (⟨497,(9),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16084 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(0),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1163]? = some (⟨500,(0),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16086 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(1),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1165]? = some (⟨500,(1),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16088 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(2),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1167]? = some (⟨500,(2),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16090 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(3),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1169]? = some (⟨500,(3),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16092 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(4),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1171]? = some (⟨500,(4),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16094 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(5),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1173]? = some (⟨500,(5),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16096 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(6),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1175]? = some (⟨500,(6),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16098 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(7),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1177]? = some (⟨500,(7),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16100 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(8),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1179]? = some (⟨500,(8),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16102 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 500 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨500,(9),[4,8,12,16],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1181]? = some (⟨500,(9),[4,8,12,16],[10,14],2⟩) from rfl))
private theorem rec16104 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 503 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(0),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1183]? = some (⟨503,(0),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16105 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 503 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(0),[4,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1184]? = some (⟨503,(0),[4,16],[10],3⟩) from rfl))
private theorem rec16108 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 503 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(1),[4,8,12,16],[10,14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1187]? = some (⟨503,(1),[4,8,12,16],[10,14],3⟩) from rfl))
private theorem rec16110 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 503 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(2),[4,8,12,16],[14],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1189]? = some (⟨503,(2),[4,8,12,16],[14],29⟩) from rfl))
private theorem rec16111 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 503 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(2),[4,8,12,16],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1190]? = some (⟨503,(2),[4,8,12,16],[10],1266⟩) from rfl))
private theorem rec16113 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 503 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(3),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1192]? = some (⟨503,(3),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec16114 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 503 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨503,(3),[4,8,12,16],[14],1264⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1193]? = some (⟨503,(3),[4,8,12,16],[14],1264⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 16).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 16)).drop 0).take 16, section14Recorded section14Catalog 16 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 16 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 16).plans.drop 2).take 1 = [⟨3,38,[([1],[]),([2],[])],true,[(496,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(502,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(505,⟨([1],[]),true,([],[]),true,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 16)).drop 0).take 16 = [⟨3,0,[⟨true,false,15⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨3,1,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,2,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,3,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,4,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨3,5,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,6,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,7,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,8,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨3,9,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨3,10,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨3,11,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨3,12,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨3,13,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨3,14,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨3,15,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec3027 16 0 (by decide) (by decide)
  · left
    exact rec3046 16 1 (by decide) (by decide)
  · left
    exact rec3051 16 2 (by decide) (by decide)
  · left
    exact rec3054 16 3 (by decide) (by decide)
  · left
    exact rec3027 16 4 (by decide) (by decide)
  · left
    exact rec3036 16 5 (by decide) (by decide)
  · left
    exact rec3053 16 6 (by decide) (by decide)
  · left
    exact rec3052 16 7 (by decide) (by decide)
  · left
    exact rec3045 16 8 (by decide) (by decide)
  · left
    exact rec3047 16 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(496,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(502,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(505,⟨([1],[]),true,([],[]),true,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 496)).length = 4 := by decide +kernel
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
        exact rec16064 16 10 (by decide) (by decide)
      · right
        exact rec16066 16 10 (by decide) (by decide)
      · right
        exact rec16068 16 10 (by decide) (by decide)
      · right
        exact rec16070 16 10 (by decide) (by decide)
      · right
        exact rec16072 16 10 (by decide) (by decide)
      · right
        exact rec16074 16 10 (by decide) (by decide)
      · right
        exact rec16076 16 10 (by decide) (by decide)
      · right
        exact rec16078 16 10 (by decide) (by decide)
      · right
        exact rec16080 16 10 (by decide) (by decide)
      · right
        exact rec16082 16 10 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 42)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3218 16 10 (by decide) (by decide)
      · right
        exact rec3226 16 10 (by decide) (by decide)
      · right
        exact rec3236 16 10 (by decide) (by decide)
      · right
        exact rec3246 16 10 (by decide) (by decide)
      · right
        exact rec3256 16 10 (by decide) (by decide)
      · right
        exact rec3269 16 10 (by decide) (by decide)
      · right
        exact rec3277 16 10 (by decide) (by decide)
      · right
        exact rec3287 16 10 (by decide) (by decide)
      · right
        exact rec3297 16 10 (by decide) (by decide)
      · right
        exact rec3307 16 10 (by decide) (by decide)
      · right
        exact rec3320 16 10 (by decide) (by decide)
      · right
        exact rec3328 16 10 (by decide) (by decide)
      · right
        exact rec3338 16 10 (by decide) (by decide)
      · right
        exact rec3348 16 10 (by decide) (by decide)
      · right
        exact rec3358 16 10 (by decide) (by decide)
      · right
        exact rec3371 16 10 (by decide) (by decide)
      · right
        exact rec3379 16 10 (by decide) (by decide)
      · right
        exact rec3389 16 10 (by decide) (by decide)
      · right
        exact rec3399 16 10 (by decide) (by decide)
      · right
        exact rec3409 16 10 (by decide) (by decide)
      · right
        exact rec3422 16 10 (by decide) (by decide)
      · right
        exact rec3430 16 10 (by decide) (by decide)
      · right
        exact rec3440 16 10 (by decide) (by decide)
      · right
        exact rec3450 16 10 (by decide) (by decide)
      · right
        exact rec3460 16 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 43)).length = 25 := by decide +kernel
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
        exact rec16084 16 10 (by decide) (by decide)
      · right
        exact rec16086 16 10 (by decide) (by decide)
      · right
        exact rec16088 16 10 (by decide) (by decide)
      · right
        exact rec16090 16 10 (by decide) (by decide)
      · right
        exact rec16092 16 10 (by decide) (by decide)
      · right
        exact rec16094 16 10 (by decide) (by decide)
      · right
        exact rec16096 16 10 (by decide) (by decide)
      · right
        exact rec16098 16 10 (by decide) (by decide)
      · right
        exact rec16100 16 10 (by decide) (by decide)
      · right
        exact rec16102 16 10 (by decide) (by decide)
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
        exact rec3568 16 10 (by decide) (by decide)
      · right
        exact rec3578 16 10 (by decide) (by decide)
      · right
        exact rec3588 16 10 (by decide) (by decide)
      · right
        exact rec3599 16 10 (by decide) (by decide)
      · right
        exact rec3610 16 10 (by decide) (by decide)
      · right
        exact rec3621 16 10 (by decide) (by decide)
      · right
        exact rec3631 16 10 (by decide) (by decide)
      · right
        exact rec3643 16 10 (by decide) (by decide)
      · right
        exact rec3659 16 10 (by decide) (by decide)
      · right
        exact rec3677 16 10 (by decide) (by decide)
      · right
        exact rec3691 16 10 (by decide) (by decide)
      · right
        exact rec3701 16 10 (by decide) (by decide)
      · right
        exact rec3713 16 10 (by decide) (by decide)
      · right
        exact rec3729 16 10 (by decide) (by decide)
      · right
        exact rec3747 16 10 (by decide) (by decide)
      · right
        exact rec3761 16 10 (by decide) (by decide)
      · right
        exact rec3771 16 10 (by decide) (by decide)
      · right
        exact rec3783 16 10 (by decide) (by decide)
      · right
        exact rec3798 16 10 (by decide) (by decide)
      · right
        exact rec3815 16 10 (by decide) (by decide)
      · right
        exact rec3828 16 10 (by decide) (by decide)
      · right
        exact rec3838 16 10 (by decide) (by decide)
      · right
        exact rec3850 16 10 (by decide) (by decide)
      · right
        exact rec3865 16 10 (by decide) (by decide)
      · right
        exact rec3882 16 10 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 502)).length = 4 := by decide +kernel
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
        exact rec16105 16 10 (by decide) (by decide)
      · right
        exact rec16108 16 10 (by decide) (by decide)
      · right
        exact rec16111 16 10 (by decide) (by decide)
      · right
        exact rec16113 16 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 505)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec3048 16 11 (by decide) (by decide)
  · left
    exact rec3049 16 12 (by decide) (by decide)
  · left
    exact rec3050 16 13 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(496,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(502,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(505,⟨([1],[]),true,([],[]),true,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 496)).length = 4 := by decide +kernel
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
        exact rec16064 16 14 (by decide) (by decide)
      · right
        exact rec16066 16 14 (by decide) (by decide)
      · right
        exact rec16068 16 14 (by decide) (by decide)
      · right
        exact rec16070 16 14 (by decide) (by decide)
      · right
        exact rec16072 16 14 (by decide) (by decide)
      · right
        exact rec16074 16 14 (by decide) (by decide)
      · right
        exact rec16076 16 14 (by decide) (by decide)
      · right
        exact rec16078 16 14 (by decide) (by decide)
      · right
        exact rec16080 16 14 (by decide) (by decide)
      · right
        exact rec16082 16 14 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 42)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3217 16 14 (by decide) (by decide)
      · right
        exact rec3228 16 14 (by decide) (by decide)
      · right
        exact rec3238 16 14 (by decide) (by decide)
      · right
        exact rec3248 16 14 (by decide) (by decide)
      · right
        exact rec3258 16 14 (by decide) (by decide)
      · right
        exact rec3268 16 14 (by decide) (by decide)
      · right
        exact rec3279 16 14 (by decide) (by decide)
      · right
        exact rec3289 16 14 (by decide) (by decide)
      · right
        exact rec3299 16 14 (by decide) (by decide)
      · right
        exact rec3309 16 14 (by decide) (by decide)
      · right
        exact rec3319 16 14 (by decide) (by decide)
      · right
        exact rec3330 16 14 (by decide) (by decide)
      · right
        exact rec3340 16 14 (by decide) (by decide)
      · right
        exact rec3350 16 14 (by decide) (by decide)
      · right
        exact rec3360 16 14 (by decide) (by decide)
      · right
        exact rec3370 16 14 (by decide) (by decide)
      · right
        exact rec3381 16 14 (by decide) (by decide)
      · right
        exact rec3391 16 14 (by decide) (by decide)
      · right
        exact rec3401 16 14 (by decide) (by decide)
      · right
        exact rec3411 16 14 (by decide) (by decide)
      · right
        exact rec3421 16 14 (by decide) (by decide)
      · right
        exact rec3432 16 14 (by decide) (by decide)
      · right
        exact rec3442 16 14 (by decide) (by decide)
      · right
        exact rec3452 16 14 (by decide) (by decide)
      · right
        exact rec3462 16 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 43)).length = 25 := by decide +kernel
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
        exact rec16084 16 14 (by decide) (by decide)
      · right
        exact rec16086 16 14 (by decide) (by decide)
      · right
        exact rec16088 16 14 (by decide) (by decide)
      · right
        exact rec16090 16 14 (by decide) (by decide)
      · right
        exact rec16092 16 14 (by decide) (by decide)
      · right
        exact rec16094 16 14 (by decide) (by decide)
      · right
        exact rec16096 16 14 (by decide) (by decide)
      · right
        exact rec16098 16 14 (by decide) (by decide)
      · right
        exact rec16100 16 14 (by decide) (by decide)
      · right
        exact rec16102 16 14 (by decide) (by decide)
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
        exact rec3570 16 14 (by decide) (by decide)
      · right
        exact rec3580 16 14 (by decide) (by decide)
      · right
        exact rec3590 16 14 (by decide) (by decide)
      · right
        exact rec3601 16 14 (by decide) (by decide)
      · right
        exact rec3612 16 14 (by decide) (by decide)
      · right
        exact rec3623 16 14 (by decide) (by decide)
      · right
        exact rec3633 16 14 (by decide) (by decide)
      · right
        exact rec3645 16 14 (by decide) (by decide)
      · right
        exact rec3661 16 14 (by decide) (by decide)
      · right
        exact rec3679 16 14 (by decide) (by decide)
      · right
        exact rec3693 16 14 (by decide) (by decide)
      · right
        exact rec3703 16 14 (by decide) (by decide)
      · right
        exact rec3715 16 14 (by decide) (by decide)
      · right
        exact rec3731 16 14 (by decide) (by decide)
      · right
        exact rec3749 16 14 (by decide) (by decide)
      · right
        exact rec3763 16 14 (by decide) (by decide)
      · right
        exact rec3773 16 14 (by decide) (by decide)
      · right
        exact rec3785 16 14 (by decide) (by decide)
      · right
        exact rec3800 16 14 (by decide) (by decide)
      · right
        exact rec3817 16 14 (by decide) (by decide)
      · right
        exact rec3830 16 14 (by decide) (by decide)
      · right
        exact rec3840 16 14 (by decide) (by decide)
      · right
        exact rec3852 16 14 (by decide) (by decide)
      · right
        exact rec3867 16 14 (by decide) (by decide)
      · right
        exact rec3884 16 14 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 502)).length = 4 := by decide +kernel
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
        exact rec16104 16 14 (by decide) (by decide)
      · right
        exact rec16108 16 14 (by decide) (by decide)
      · right
        exact rec16110 16 14 (by decide) (by decide)
      · right
        exact rec16114 16 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 505)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec3052 16 15 (by decide) (by decide)
end Section14Coverage_16_2_p0_16

#print axioms solution
