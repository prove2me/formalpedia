-- Prove2me | solution 1 for Freiman.section14_s0004_coverage0002_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T01:33:40.538425+00:00
-- url     : https://prove2.me/submissions/ae698c1e-1b2e-479b-85a1-1b25c831b29f

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
namespace Section14Coverage_4_2_p0_16
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
private theorem rec3897 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[4,8,12],[10],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[258]? = some (⟨50,(0),[4,8,12],[10],301⟩) from rfl))
private theorem rec3898 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[4,8,12],[14],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[259]? = some (⟨50,(0),[4,8,12],[14],331⟩) from rfl))
private theorem rec3909 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[4,8,12],[10],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[270]? = some (⟨50,(1),[4,8,12],[10],302⟩) from rfl))
private theorem rec3910 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[4,8,12],[14],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[271]? = some (⟨50,(1),[4,8,12],[14],332⟩) from rfl))
private theorem rec3921 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[4,8,12],[10],303⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[282]? = some (⟨50,(2),[4,8,12],[10],303⟩) from rfl))
private theorem rec3922 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[4,8,12],[14],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[283]? = some (⟨50,(2),[4,8,12],[14],333⟩) from rfl))
private theorem rec3933 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[4,8,12],[10],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[294]? = some (⟨50,(3),[4,8,12],[10],304⟩) from rfl))
private theorem rec3934 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[4,8,12],[14],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[295]? = some (⟨50,(3),[4,8,12],[14],334⟩) from rfl))
private theorem rec3945 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[4,8,12],[10],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[306]? = some (⟨50,(4),[4,8,12],[10],301⟩) from rfl))
private theorem rec3946 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[4,8,12],[14],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[307]? = some (⟨50,(4),[4,8,12],[14],331⟩) from rfl))
private theorem rec3957 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[4,8,12],[10],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[318]? = some (⟨50,(5),[4,8,12],[10],302⟩) from rfl))
private theorem rec3958 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[4,8,12],[14],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[319]? = some (⟨50,(5),[4,8,12],[14],332⟩) from rfl))
private theorem rec3969 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[4,8,12],[10],305⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[330]? = some (⟨50,(6),[4,8,12],[10],305⟩) from rfl))
private theorem rec3970 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[4,8,12],[14],335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[331]? = some (⟨50,(6),[4,8,12],[14],335⟩) from rfl))
private theorem rec3981 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[4,8,12],[10],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[342]? = some (⟨50,(7),[4,8,12],[10],304⟩) from rfl))
private theorem rec3982 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[4,8,12],[14],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[343]? = some (⟨50,(7),[4,8,12],[14],334⟩) from rfl))
private theorem rec3993 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[4,8,12],[10],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[354]? = some (⟨50,(8),[4,8,12],[10],301⟩) from rfl))
private theorem rec3994 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[4,8,12],[14],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[355]? = some (⟨50,(8),[4,8,12],[14],331⟩) from rfl))
private theorem rec4005 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[4,8,12],[10],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[366]? = some (⟨50,(9),[4,8,12],[10],302⟩) from rfl))
private theorem rec4006 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[4,8,12],[14],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[367]? = some (⟨50,(9),[4,8,12],[14],332⟩) from rfl))
private theorem rec4017 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[4,8,12],[10],303⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[378]? = some (⟨50,(10),[4,8,12],[10],303⟩) from rfl))
private theorem rec4018 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[4,8,12],[14],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[379]? = some (⟨50,(10),[4,8,12],[14],333⟩) from rfl))
private theorem rec4029 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[4,8,12],[10],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[390]? = some (⟨50,(11),[4,8,12],[10],304⟩) from rfl))
private theorem rec4030 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[4,8,12],[14],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[391]? = some (⟨50,(11),[4,8,12],[14],334⟩) from rfl))
private theorem rec4041 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[4,8,12],[10],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[402]? = some (⟨50,(12),[4,8,12],[10],301⟩) from rfl))
private theorem rec4042 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[4,8,12],[14],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[403]? = some (⟨50,(12),[4,8,12],[14],331⟩) from rfl))
private theorem rec4053 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[4,8,12],[10],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[414]? = some (⟨50,(13),[4,8,12],[10],302⟩) from rfl))
private theorem rec4054 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[4,8,12],[14],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[415]? = some (⟨50,(13),[4,8,12],[14],332⟩) from rfl))
private theorem rec4065 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[4,8,12],[10],306⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[426]? = some (⟨50,(14),[4,8,12],[10],306⟩) from rfl))
private theorem rec4066 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[4,8,12],[14],336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[427]? = some (⟨50,(14),[4,8,12],[14],336⟩) from rfl))
private theorem rec4077 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[4,8,12],[10],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[438]? = some (⟨50,(15),[4,8,12],[10],304⟩) from rfl))
private theorem rec4078 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[4,8,12],[14],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[439]? = some (⟨50,(15),[4,8,12],[14],334⟩) from rfl))
private theorem rec4090 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[3,4,7,8,12],[10],279⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[451]? = some (⟨53,(0),[3,4,7,8,12],[10],279⟩) from rfl))
private theorem rec4091 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[4,8,12],[14],325⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[452]? = some (⟨53,(0),[4,8,12],[14],325⟩) from rfl))
private theorem rec4106 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[3,4,7,8,12],[10],280⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[467]? = some (⟨53,(1),[3,4,7,8,12],[10],280⟩) from rfl))
private theorem rec4107 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[4,8,12],[14],326⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[468]? = some (⟨53,(1),[4,8,12],[14],326⟩) from rfl))
private theorem rec4122 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[3,4,7,8,12],[10],281⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[483]? = some (⟨53,(2),[3,4,7,8,12],[10],281⟩) from rfl))
private theorem rec4123 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[4,8,12],[14],327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[484]? = some (⟨53,(2),[4,8,12],[14],327⟩) from rfl))
private theorem rec4137 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[3,4,7,8,12],[10],282⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[498]? = some (⟨53,(3),[3,4,7,8,12],[10],282⟩) from rfl))
private theorem rec4138 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[4,8,12],[14],328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[499]? = some (⟨53,(3),[4,8,12],[14],328⟩) from rfl))
private theorem rec4280 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(0),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[131]? = some (⟨57,(0),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4286 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(1),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[137]? = some (⟨57,(1),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4294 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[4,8,12],[10],311⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[145]? = some (⟨57,(2),[4,8,12],[10],311⟩) from rfl))
private theorem rec4295 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[4,8,12],[14],337⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[146]? = some (⟨57,(2),[4,8,12],[14],337⟩) from rfl))
private theorem rec4304 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(3),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[155]? = some (⟨57,(3),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4310 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(4),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[161]? = some (⟨57,(4),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4316 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(5),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[167]? = some (⟨57,(5),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4325 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[4,8,12],[10],284⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[176]? = some (⟨57,(6),[4,8,12],[10],284⟩) from rfl))
private theorem rec4326 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[4,8,12],[14],338⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[177]? = some (⟨57,(6),[4,8,12],[14],338⟩) from rfl))
private theorem rec4335 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(7),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[186]? = some (⟨57,(7),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4341 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(8),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[192]? = some (⟨57,(8),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4347 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(9),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[198]? = some (⟨57,(9),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4356 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[4,8,12],[10],285⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[207]? = some (⟨57,(10),[4,8,12],[10],285⟩) from rfl))
private theorem rec4357 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[4,8,12],[14],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[208]? = some (⟨57,(10),[4,8,12],[14],339⟩) from rfl))
private theorem rec4366 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(11),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[217]? = some (⟨57,(11),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4372 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(12),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[223]? = some (⟨57,(12),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4378 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(13),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[229]? = some (⟨57,(13),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4384 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(14),[4,8,12],[10,14],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[235]? = some (⟨57,(14),[4,8,12],[10,14],286⟩) from rfl))
private theorem rec4390 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(15),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[241]? = some (⟨57,(15),[4,8,12],[10,14],101⟩) from rfl))
private theorem rec4396 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(16),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[247]? = some (⟨57,(16),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4402 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(17),[4,8,12],[10,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[253]? = some (⟨57,(17),[4,8,12],[10,14],2⟩) from rfl))
private theorem rec4408 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(18),[4,8,12],[10,14],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[259]? = some (⟨57,(18),[4,8,12],[10,14],287⟩) from rfl))
private theorem rec4414 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10, 14] : List ℕ)) : section14Recorded section14Catalog si parent 57 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(19),[4,8,12],[10,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[265]? = some (⟨57,(19),[4,8,12],[10,14],101⟩) from rfl))
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
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 4).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 4)).drop 0).take 16, section14Recorded section14Catalog 4 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 4 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 4).plans.drop 2).take 1 = [⟨3,38,[([1],[]),([2],[]),([3],[1])],false,[(496,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(502,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(505,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 4)).drop 0).take 16 = [⟨3,0,[⟨true,false,15⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨3,1,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,2,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,3,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,4,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨3,5,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,6,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,7,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨3,8,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨3,9,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨3,10,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨3,11,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨3,12,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨3,13,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨3,14,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨3,15,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec3027 4 0 (by decide) (by decide)
  · left
    exact rec3046 4 1 (by decide) (by decide)
  · left
    exact rec3051 4 2 (by decide) (by decide)
  · left
    exact rec3054 4 3 (by decide) (by decide)
  · left
    exact rec3027 4 4 (by decide) (by decide)
  · left
    exact rec3036 4 5 (by decide) (by decide)
  · left
    exact rec3053 4 6 (by decide) (by decide)
  · left
    exact rec3052 4 7 (by decide) (by decide)
  · left
    exact rec3045 4 8 (by decide) (by decide)
  · left
    exact rec3047 4 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(496,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(502,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(505,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
        exact rec16064 4 10 (by decide) (by decide)
      · right
        exact rec16066 4 10 (by decide) (by decide)
      · right
        exact rec16068 4 10 (by decide) (by decide)
      · right
        exact rec16070 4 10 (by decide) (by decide)
      · right
        exact rec16072 4 10 (by decide) (by decide)
      · right
        exact rec16074 4 10 (by decide) (by decide)
      · right
        exact rec16076 4 10 (by decide) (by decide)
      · right
        exact rec16078 4 10 (by decide) (by decide)
      · right
        exact rec16080 4 10 (by decide) (by decide)
      · right
        exact rec16082 4 10 (by decide) (by decide)
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
        exact rec3218 4 10 (by decide) (by decide)
      · right
        exact rec3226 4 10 (by decide) (by decide)
      · right
        exact rec3236 4 10 (by decide) (by decide)
      · right
        exact rec3246 4 10 (by decide) (by decide)
      · right
        exact rec3256 4 10 (by decide) (by decide)
      · right
        exact rec3269 4 10 (by decide) (by decide)
      · right
        exact rec3277 4 10 (by decide) (by decide)
      · right
        exact rec3287 4 10 (by decide) (by decide)
      · right
        exact rec3297 4 10 (by decide) (by decide)
      · right
        exact rec3307 4 10 (by decide) (by decide)
      · right
        exact rec3320 4 10 (by decide) (by decide)
      · right
        exact rec3328 4 10 (by decide) (by decide)
      · right
        exact rec3338 4 10 (by decide) (by decide)
      · right
        exact rec3348 4 10 (by decide) (by decide)
      · right
        exact rec3358 4 10 (by decide) (by decide)
      · right
        exact rec3371 4 10 (by decide) (by decide)
      · right
        exact rec3379 4 10 (by decide) (by decide)
      · right
        exact rec3389 4 10 (by decide) (by decide)
      · right
        exact rec3399 4 10 (by decide) (by decide)
      · right
        exact rec3409 4 10 (by decide) (by decide)
      · right
        exact rec3422 4 10 (by decide) (by decide)
      · right
        exact rec3430 4 10 (by decide) (by decide)
      · right
        exact rec3440 4 10 (by decide) (by decide)
      · right
        exact rec3450 4 10 (by decide) (by decide)
      · right
        exact rec3460 4 10 (by decide) (by decide)
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
        exact rec16084 4 10 (by decide) (by decide)
      · right
        exact rec16086 4 10 (by decide) (by decide)
      · right
        exact rec16088 4 10 (by decide) (by decide)
      · right
        exact rec16090 4 10 (by decide) (by decide)
      · right
        exact rec16092 4 10 (by decide) (by decide)
      · right
        exact rec16094 4 10 (by decide) (by decide)
      · right
        exact rec16096 4 10 (by decide) (by decide)
      · right
        exact rec16098 4 10 (by decide) (by decide)
      · right
        exact rec16100 4 10 (by decide) (by decide)
      · right
        exact rec16102 4 10 (by decide) (by decide)
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
        exact rec3568 4 10 (by decide) (by decide)
      · right
        exact rec3578 4 10 (by decide) (by decide)
      · right
        exact rec3588 4 10 (by decide) (by decide)
      · right
        exact rec3599 4 10 (by decide) (by decide)
      · right
        exact rec3610 4 10 (by decide) (by decide)
      · right
        exact rec3621 4 10 (by decide) (by decide)
      · right
        exact rec3631 4 10 (by decide) (by decide)
      · right
        exact rec3643 4 10 (by decide) (by decide)
      · right
        exact rec3659 4 10 (by decide) (by decide)
      · right
        exact rec3677 4 10 (by decide) (by decide)
      · right
        exact rec3691 4 10 (by decide) (by decide)
      · right
        exact rec3701 4 10 (by decide) (by decide)
      · right
        exact rec3713 4 10 (by decide) (by decide)
      · right
        exact rec3729 4 10 (by decide) (by decide)
      · right
        exact rec3747 4 10 (by decide) (by decide)
      · right
        exact rec3761 4 10 (by decide) (by decide)
      · right
        exact rec3771 4 10 (by decide) (by decide)
      · right
        exact rec3783 4 10 (by decide) (by decide)
      · right
        exact rec3798 4 10 (by decide) (by decide)
      · right
        exact rec3815 4 10 (by decide) (by decide)
      · right
        exact rec3828 4 10 (by decide) (by decide)
      · right
        exact rec3838 4 10 (by decide) (by decide)
      · right
        exact rec3850 4 10 (by decide) (by decide)
      · right
        exact rec3865 4 10 (by decide) (by decide)
      · right
        exact rec3882 4 10 (by decide) (by decide)
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
        exact rec3897 4 10 (by decide) (by decide)
      · right
        exact rec3909 4 10 (by decide) (by decide)
      · right
        exact rec3921 4 10 (by decide) (by decide)
      · right
        exact rec3933 4 10 (by decide) (by decide)
      · right
        exact rec3945 4 10 (by decide) (by decide)
      · right
        exact rec3957 4 10 (by decide) (by decide)
      · right
        exact rec3969 4 10 (by decide) (by decide)
      · right
        exact rec3981 4 10 (by decide) (by decide)
      · right
        exact rec3993 4 10 (by decide) (by decide)
      · right
        exact rec4005 4 10 (by decide) (by decide)
      · right
        exact rec4017 4 10 (by decide) (by decide)
      · right
        exact rec4029 4 10 (by decide) (by decide)
      · right
        exact rec4041 4 10 (by decide) (by decide)
      · right
        exact rec4053 4 10 (by decide) (by decide)
      · right
        exact rec4065 4 10 (by decide) (by decide)
      · right
        exact rec4077 4 10 (by decide) (by decide)
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
        exact rec4090 4 10 (by decide) (by decide)
      · right
        exact rec4106 4 10 (by decide) (by decide)
      · right
        exact rec4122 4 10 (by decide) (by decide)
      · right
        exact rec4137 4 10 (by decide) (by decide)
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
        exact rec16105 4 10 (by decide) (by decide)
      · right
        exact rec16108 4 10 (by decide) (by decide)
      · right
        exact rec16111 4 10 (by decide) (by decide)
      · right
        exact rec16113 4 10 (by decide) (by decide)
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
        exact rec4280 4 10 (by decide) (by decide)
      · right
        exact rec4286 4 10 (by decide) (by decide)
      · right
        exact rec4294 4 10 (by decide) (by decide)
      · right
        exact rec4304 4 10 (by decide) (by decide)
      · right
        exact rec4310 4 10 (by decide) (by decide)
      · right
        exact rec4316 4 10 (by decide) (by decide)
      · right
        exact rec4325 4 10 (by decide) (by decide)
      · right
        exact rec4335 4 10 (by decide) (by decide)
      · right
        exact rec4341 4 10 (by decide) (by decide)
      · right
        exact rec4347 4 10 (by decide) (by decide)
      · right
        exact rec4356 4 10 (by decide) (by decide)
      · right
        exact rec4366 4 10 (by decide) (by decide)
      · right
        exact rec4372 4 10 (by decide) (by decide)
      · right
        exact rec4378 4 10 (by decide) (by decide)
      · right
        exact rec4384 4 10 (by decide) (by decide)
      · right
        exact rec4390 4 10 (by decide) (by decide)
      · right
        exact rec4396 4 10 (by decide) (by decide)
      · right
        exact rec4402 4 10 (by decide) (by decide)
      · right
        exact rec4408 4 10 (by decide) (by decide)
      · right
        exact rec4414 4 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 505)).length = 2 := by decide +kernel
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
    exact rec3048 4 11 (by decide) (by decide)
  · left
    exact rec3049 4 12 (by decide) (by decide)
  · left
    exact rec3050 4 13 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(496,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(502,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(505,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
        exact rec16064 4 14 (by decide) (by decide)
      · right
        exact rec16066 4 14 (by decide) (by decide)
      · right
        exact rec16068 4 14 (by decide) (by decide)
      · right
        exact rec16070 4 14 (by decide) (by decide)
      · right
        exact rec16072 4 14 (by decide) (by decide)
      · right
        exact rec16074 4 14 (by decide) (by decide)
      · right
        exact rec16076 4 14 (by decide) (by decide)
      · right
        exact rec16078 4 14 (by decide) (by decide)
      · right
        exact rec16080 4 14 (by decide) (by decide)
      · right
        exact rec16082 4 14 (by decide) (by decide)
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
        exact rec3217 4 14 (by decide) (by decide)
      · right
        exact rec3228 4 14 (by decide) (by decide)
      · right
        exact rec3238 4 14 (by decide) (by decide)
      · right
        exact rec3248 4 14 (by decide) (by decide)
      · right
        exact rec3258 4 14 (by decide) (by decide)
      · right
        exact rec3268 4 14 (by decide) (by decide)
      · right
        exact rec3279 4 14 (by decide) (by decide)
      · right
        exact rec3289 4 14 (by decide) (by decide)
      · right
        exact rec3299 4 14 (by decide) (by decide)
      · right
        exact rec3309 4 14 (by decide) (by decide)
      · right
        exact rec3319 4 14 (by decide) (by decide)
      · right
        exact rec3330 4 14 (by decide) (by decide)
      · right
        exact rec3340 4 14 (by decide) (by decide)
      · right
        exact rec3350 4 14 (by decide) (by decide)
      · right
        exact rec3360 4 14 (by decide) (by decide)
      · right
        exact rec3370 4 14 (by decide) (by decide)
      · right
        exact rec3381 4 14 (by decide) (by decide)
      · right
        exact rec3391 4 14 (by decide) (by decide)
      · right
        exact rec3401 4 14 (by decide) (by decide)
      · right
        exact rec3411 4 14 (by decide) (by decide)
      · right
        exact rec3421 4 14 (by decide) (by decide)
      · right
        exact rec3432 4 14 (by decide) (by decide)
      · right
        exact rec3442 4 14 (by decide) (by decide)
      · right
        exact rec3452 4 14 (by decide) (by decide)
      · right
        exact rec3462 4 14 (by decide) (by decide)
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
        exact rec16084 4 14 (by decide) (by decide)
      · right
        exact rec16086 4 14 (by decide) (by decide)
      · right
        exact rec16088 4 14 (by decide) (by decide)
      · right
        exact rec16090 4 14 (by decide) (by decide)
      · right
        exact rec16092 4 14 (by decide) (by decide)
      · right
        exact rec16094 4 14 (by decide) (by decide)
      · right
        exact rec16096 4 14 (by decide) (by decide)
      · right
        exact rec16098 4 14 (by decide) (by decide)
      · right
        exact rec16100 4 14 (by decide) (by decide)
      · right
        exact rec16102 4 14 (by decide) (by decide)
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
        exact rec3570 4 14 (by decide) (by decide)
      · right
        exact rec3580 4 14 (by decide) (by decide)
      · right
        exact rec3590 4 14 (by decide) (by decide)
      · right
        exact rec3601 4 14 (by decide) (by decide)
      · right
        exact rec3612 4 14 (by decide) (by decide)
      · right
        exact rec3623 4 14 (by decide) (by decide)
      · right
        exact rec3633 4 14 (by decide) (by decide)
      · right
        exact rec3645 4 14 (by decide) (by decide)
      · right
        exact rec3661 4 14 (by decide) (by decide)
      · right
        exact rec3679 4 14 (by decide) (by decide)
      · right
        exact rec3693 4 14 (by decide) (by decide)
      · right
        exact rec3703 4 14 (by decide) (by decide)
      · right
        exact rec3715 4 14 (by decide) (by decide)
      · right
        exact rec3731 4 14 (by decide) (by decide)
      · right
        exact rec3749 4 14 (by decide) (by decide)
      · right
        exact rec3763 4 14 (by decide) (by decide)
      · right
        exact rec3773 4 14 (by decide) (by decide)
      · right
        exact rec3785 4 14 (by decide) (by decide)
      · right
        exact rec3800 4 14 (by decide) (by decide)
      · right
        exact rec3817 4 14 (by decide) (by decide)
      · right
        exact rec3830 4 14 (by decide) (by decide)
      · right
        exact rec3840 4 14 (by decide) (by decide)
      · right
        exact rec3852 4 14 (by decide) (by decide)
      · right
        exact rec3867 4 14 (by decide) (by decide)
      · right
        exact rec3884 4 14 (by decide) (by decide)
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
        exact rec3898 4 14 (by decide) (by decide)
      · right
        exact rec3910 4 14 (by decide) (by decide)
      · right
        exact rec3922 4 14 (by decide) (by decide)
      · right
        exact rec3934 4 14 (by decide) (by decide)
      · right
        exact rec3946 4 14 (by decide) (by decide)
      · right
        exact rec3958 4 14 (by decide) (by decide)
      · right
        exact rec3970 4 14 (by decide) (by decide)
      · right
        exact rec3982 4 14 (by decide) (by decide)
      · right
        exact rec3994 4 14 (by decide) (by decide)
      · right
        exact rec4006 4 14 (by decide) (by decide)
      · right
        exact rec4018 4 14 (by decide) (by decide)
      · right
        exact rec4030 4 14 (by decide) (by decide)
      · right
        exact rec4042 4 14 (by decide) (by decide)
      · right
        exact rec4054 4 14 (by decide) (by decide)
      · right
        exact rec4066 4 14 (by decide) (by decide)
      · right
        exact rec4078 4 14 (by decide) (by decide)
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
        exact rec4091 4 14 (by decide) (by decide)
      · right
        exact rec4107 4 14 (by decide) (by decide)
      · right
        exact rec4123 4 14 (by decide) (by decide)
      · right
        exact rec4138 4 14 (by decide) (by decide)
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
        exact rec16104 4 14 (by decide) (by decide)
      · right
        exact rec16108 4 14 (by decide) (by decide)
      · right
        exact rec16110 4 14 (by decide) (by decide)
      · right
        exact rec16114 4 14 (by decide) (by decide)
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
        exact rec4280 4 14 (by decide) (by decide)
      · right
        exact rec4286 4 14 (by decide) (by decide)
      · right
        exact rec4295 4 14 (by decide) (by decide)
      · right
        exact rec4304 4 14 (by decide) (by decide)
      · right
        exact rec4310 4 14 (by decide) (by decide)
      · right
        exact rec4316 4 14 (by decide) (by decide)
      · right
        exact rec4326 4 14 (by decide) (by decide)
      · right
        exact rec4335 4 14 (by decide) (by decide)
      · right
        exact rec4341 4 14 (by decide) (by decide)
      · right
        exact rec4347 4 14 (by decide) (by decide)
      · right
        exact rec4357 4 14 (by decide) (by decide)
      · right
        exact rec4366 4 14 (by decide) (by decide)
      · right
        exact rec4372 4 14 (by decide) (by decide)
      · right
        exact rec4378 4 14 (by decide) (by decide)
      · right
        exact rec4384 4 14 (by decide) (by decide)
      · right
        exact rec4390 4 14 (by decide) (by decide)
      · right
        exact rec4396 4 14 (by decide) (by decide)
      · right
        exact rec4402 4 14 (by decide) (by decide)
      · right
        exact rec4408 4 14 (by decide) (by decide)
      · right
        exact rec4414 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 505)).length = 2 := by decide +kernel
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
    exact rec3052 4 15 (by decide) (by decide)
end Section14Coverage_4_2_p0_16

#print axioms solution
