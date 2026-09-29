-- Prove2me | solution 1 for Freiman.section14_s0012_coverage0004_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T03:53:22.654541+00:00
-- url     : https://prove2.me/submissions/ae389a6a-3c9e-46ce-8afe-9478f8a425bb

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
namespace Section14Coverage_12_4_p0_16
private theorem rec5576 (si parent : ℕ) (hs : si ∈ ([2, 4, 6, 8, 10, 12, 14, 16] : List ℕ)) (hp : parent ∈ ([0, 4] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[2,4,6,8,10,12,14,16],[0,4],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[201]? = some (⟨82,(-1),[2,4,6,8,10,12,14,16],[0,4],387⟩) from rfl))
private theorem rec5583 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[3,4,7,8,12,15,16],[5],388⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[208]? = some (⟨82,(-1),[3,4,7,8,12,15,16],[5],388⟩) from rfl))
private theorem rec5591 (si parent : ℕ) (hs : si ∈ ([4, 8, 10, 12, 16] : List ℕ)) (hp : parent ∈ ([8, 12] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[4,8,10,12,16],[8,12],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[216]? = some (⟨82,(-1),[4,8,10,12,16],[8,12],387⟩) from rfl))
private theorem rec5592 (si parent : ℕ) (hs : si ∈ ([4, 8, 11, 12, 16] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[4,8,11,12,16],[1],388⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[217]? = some (⟨82,(-1),[4,8,11,12,16],[1],388⟩) from rfl))
private theorem rec5593 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([9, 13] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[4,8,12,16],[9,13],388⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[218]? = some (⟨82,(-1),[4,8,12,16],[9,13],388⟩) from rfl))
private theorem rec5594 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[4,8,12,16],[2],389⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[219]? = some (⟨82,(-1),[4,8,12,16],[2],389⟩) from rfl))
private theorem rec5595 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([7, 11, 15] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[4,8,12,16],[7,11,15],391⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[220]? = some (⟨82,(-1),[4,8,12,16],[7,11,15],391⟩) from rfl))
private theorem rec5596 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[4,8,12,16],[6],392⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[221]? = some (⟨82,(-1),[4,8,12,16],[6],392⟩) from rfl))
private theorem rec5597 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[4,8,12,16],[14],629⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[222]? = some (⟨82,(-1),[4,8,12,16],[14],629⟩) from rfl))
private theorem rec5601 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[8,12],[3],391⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[226]? = some (⟨82,(-1),[8,12],[3],391⟩) from rfl))
private theorem rec5719 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(0),[4,8,12,16],[10],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[344]? = some (⟨89,(0),[4,8,12,16],[10],400⟩) from rfl))
private theorem rec5722 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(1),[4,8,12,16],[10],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[347]? = some (⟨89,(1),[4,8,12,16],[10],401⟩) from rfl))
private theorem rec5725 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(2),[4,8,12,16],[10],402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[350]? = some (⟨89,(2),[4,8,12,16],[10],402⟩) from rfl))
private theorem rec5728 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(3),[4,8,12,16],[10],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[353]? = some (⟨89,(3),[4,8,12,16],[10],403⟩) from rfl))
private theorem rec5731 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(4),[4,8,12,16],[10],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[356]? = some (⟨89,(4),[4,8,12,16],[10],400⟩) from rfl))
private theorem rec5734 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(5),[4,8,12,16],[10],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[359]? = some (⟨89,(5),[4,8,12,16],[10],401⟩) from rfl))
private theorem rec5737 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(6),[4,8,12,16],[10],404⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[362]? = some (⟨89,(6),[4,8,12,16],[10],404⟩) from rfl))
private theorem rec5740 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(7),[4,8,12,16],[10],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[365]? = some (⟨89,(7),[4,8,12,16],[10],403⟩) from rfl))
private theorem rec5743 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(8),[4,8,12,16],[10],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[368]? = some (⟨89,(8),[4,8,12,16],[10],400⟩) from rfl))
private theorem rec5746 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(9),[4,8,12,16],[10],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[371]? = some (⟨89,(9),[4,8,12,16],[10],401⟩) from rfl))
private theorem rec5749 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(10),[4,8,12,16],[10],402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[374]? = some (⟨89,(10),[4,8,12,16],[10],402⟩) from rfl))
private theorem rec5752 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(11),[4,8,12,16],[10],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[377]? = some (⟨89,(11),[4,8,12,16],[10],403⟩) from rfl))
private theorem rec5755 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(12),[4,8,12,16],[10],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[380]? = some (⟨89,(12),[4,8,12,16],[10],400⟩) from rfl))
private theorem rec5758 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(13),[4,8,12,16],[10],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[383]? = some (⟨89,(13),[4,8,12,16],[10],401⟩) from rfl))
private theorem rec5761 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(14),[4,8,12,16],[10],405⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[386]? = some (⟨89,(14),[4,8,12,16],[10],405⟩) from rfl))
private theorem rec5764 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 89 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(15),[4,8,12,16],[10],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[389]? = some (⟨89,(15),[4,8,12,16],[10],403⟩) from rfl))
private theorem rec5767 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(0),[4,8,12,16],[10],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[392]? = some (⟨92,(0),[4,8,12,16],[10],406⟩) from rfl))
private theorem rec5770 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(1),[4,8,12,16],[10],407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[395]? = some (⟨92,(1),[4,8,12,16],[10],407⟩) from rfl))
private theorem rec5773 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(2),[4,8,12,16],[10],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[398]? = some (⟨92,(2),[4,8,12,16],[10],406⟩) from rfl))
private theorem rec5776 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(3),[4,8,12,16],[10],408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[401]? = some (⟨92,(3),[4,8,12,16],[10],408⟩) from rfl))
private theorem rec5779 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(4),[4,8,12,16],[10],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[404]? = some (⟨92,(4),[4,8,12,16],[10],409⟩) from rfl))
private theorem rec5782 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(5),[4,8,12,16],[10],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[407]? = some (⟨92,(5),[4,8,12,16],[10],409⟩) from rfl))
private theorem rec5785 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(6),[4,8,12,16],[10],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[410]? = some (⟨92,(6),[4,8,12,16],[10],409⟩) from rfl))
private theorem rec5788 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(7),[4,8,12,16],[10],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[413]? = some (⟨92,(7),[4,8,12,16],[10],409⟩) from rfl))
private theorem rec5791 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(8),[4,8,12,16],[10],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[416]? = some (⟨92,(8),[4,8,12,16],[10],410⟩) from rfl))
private theorem rec5794 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(9),[4,8,12,16],[10],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[419]? = some (⟨92,(9),[4,8,12,16],[10],410⟩) from rfl))
private theorem rec5797 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(10),[4,8,12,16],[10],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[422]? = some (⟨92,(10),[4,8,12,16],[10],410⟩) from rfl))
private theorem rec5800 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(11),[4,8,12,16],[10],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[425]? = some (⟨92,(11),[4,8,12,16],[10],410⟩) from rfl))
private theorem rec5803 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(12),[4,8,12,16],[10],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[428]? = some (⟨92,(12),[4,8,12,16],[10],411⟩) from rfl))
private theorem rec5806 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(13),[4,8,12,16],[10],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[431]? = some (⟨92,(13),[4,8,12,16],[10],411⟩) from rfl))
private theorem rec5809 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(14),[4,8,12,16],[10],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[434]? = some (⟨92,(14),[4,8,12,16],[10],411⟩) from rfl))
private theorem rec5812 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 92 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(15),[4,8,12,16],[10],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[437]? = some (⟨92,(15),[4,8,12,16],[10],411⟩) from rfl))
private theorem rec5815 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(0),[4,8,12,16],[10],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[440]? = some (⟨95,(0),[4,8,12,16],[10],412⟩) from rfl))
private theorem rec5818 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(1),[4,8,12,16],[10],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[443]? = some (⟨95,(1),[4,8,12,16],[10],412⟩) from rfl))
private theorem rec5821 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(2),[4,8,12,16],[10],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[446]? = some (⟨95,(2),[4,8,12,16],[10],412⟩) from rfl))
private theorem rec5824 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(3),[4,8,12,16],[10],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[449]? = some (⟨95,(3),[4,8,12,16],[10],412⟩) from rfl))
private theorem rec5827 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(4),[4,8,12,16],[10],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[452]? = some (⟨95,(4),[4,8,12,16],[10],413⟩) from rfl))
private theorem rec5830 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(5),[4,8,12,16],[10],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[455]? = some (⟨95,(5),[4,8,12,16],[10],413⟩) from rfl))
private theorem rec5833 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(6),[4,8,12,16],[10],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[458]? = some (⟨95,(6),[4,8,12,16],[10],413⟩) from rfl))
private theorem rec5836 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(7),[4,8,12,16],[10],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[461]? = some (⟨95,(7),[4,8,12,16],[10],413⟩) from rfl))
private theorem rec5839 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(8),[4,8,12,16],[10],414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[464]? = some (⟨95,(8),[4,8,12,16],[10],414⟩) from rfl))
private theorem rec5842 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(9),[4,8,12,16],[10],415⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[467]? = some (⟨95,(9),[4,8,12,16],[10],415⟩) from rfl))
private theorem rec5845 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(10),[4,8,12,16],[10],414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[470]? = some (⟨95,(10),[4,8,12,16],[10],414⟩) from rfl))
private theorem rec5848 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(11),[4,8,12,16],[10],416⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[473]? = some (⟨95,(11),[4,8,12,16],[10],416⟩) from rfl))
private theorem rec5851 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(12),[4,8,12,16],[10],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[476]? = some (⟨95,(12),[4,8,12,16],[10],417⟩) from rfl))
private theorem rec5854 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(13),[4,8,12,16],[10],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[479]? = some (⟨95,(13),[4,8,12,16],[10],417⟩) from rfl))
private theorem rec5857 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(14),[4,8,12,16],[10],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[482]? = some (⟨95,(14),[4,8,12,16],[10],417⟩) from rfl))
private theorem rec5860 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 95 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(15),[4,8,12,16],[10],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[485]? = some (⟨95,(15),[4,8,12,16],[10],417⟩) from rfl))
private theorem rec5863 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(0),[4,8,12,16],[10],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[488]? = some (⟨96,(0),[4,8,12,16],[10],418⟩) from rfl))
private theorem rec5866 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(1),[4,8,12,16],[10],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[491]? = some (⟨96,(1),[4,8,12,16],[10],419⟩) from rfl))
private theorem rec5869 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(2),[4,8,12,16],[10],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[494]? = some (⟨96,(2),[4,8,12,16],[10],420⟩) from rfl))
private theorem rec5872 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(3),[4,8,12,16],[10],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[497]? = some (⟨96,(3),[4,8,12,16],[10],421⟩) from rfl))
private theorem rec5875 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(4),[4,8,12,16],[10],422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[500]? = some (⟨96,(4),[4,8,12,16],[10],422⟩) from rfl))
private theorem rec5878 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(5),[4,8,12,16],[10],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[503]? = some (⟨96,(5),[4,8,12,16],[10],419⟩) from rfl))
private theorem rec5881 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(6),[4,8,12,16],[10],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[506]? = some (⟨96,(6),[4,8,12,16],[10],420⟩) from rfl))
private theorem rec5884 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(7),[4,8,12,16],[10],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[509]? = some (⟨96,(7),[4,8,12,16],[10],421⟩) from rfl))
private theorem rec5887 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(8),[4,8,12,16],[10],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[512]? = some (⟨96,(8),[4,8,12,16],[10],418⟩) from rfl))
private theorem rec5890 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(9),[4,8,12,16],[10],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[515]? = some (⟨96,(9),[4,8,12,16],[10],419⟩) from rfl))
private theorem rec5893 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(10),[4,8,12,16],[10],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[518]? = some (⟨96,(10),[4,8,12,16],[10],420⟩) from rfl))
private theorem rec5896 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(11),[4,8,12,16],[10],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[521]? = some (⟨96,(11),[4,8,12,16],[10],421⟩) from rfl))
private theorem rec5899 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(12),[4,8,12,16],[10],423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[524]? = some (⟨96,(12),[4,8,12,16],[10],423⟩) from rfl))
private theorem rec5902 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(13),[4,8,12,16],[10],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[527]? = some (⟨96,(13),[4,8,12,16],[10],419⟩) from rfl))
private theorem rec5905 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(14),[4,8,12,16],[10],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[530]? = some (⟨96,(14),[4,8,12,16],[10],420⟩) from rfl))
private theorem rec5908 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 96 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(15),[4,8,12,16],[10],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[533]? = some (⟨96,(15),[4,8,12,16],[10],421⟩) from rfl))
private theorem rec5911 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 100 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(0),[4,8,12,16],[10],424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[536]? = some (⟨100,(0),[4,8,12,16],[10],424⟩) from rfl))
private theorem rec5914 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 100 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(1),[4,8,12,16],[10],425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[539]? = some (⟨100,(1),[4,8,12,16],[10],425⟩) from rfl))
private theorem rec5917 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 100 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(2),[4,8,12,16],[10],426⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[542]? = some (⟨100,(2),[4,8,12,16],[10],426⟩) from rfl))
private theorem rec5920 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 100 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(3),[4,8,12,16],[10],427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[545]? = some (⟨100,(3),[4,8,12,16],[10],427⟩) from rfl))
private theorem rec5923 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(0),[4,8,12,16],[10],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[548]? = some (⟨101,(0),[4,8,12,16],[10],428⟩) from rfl))
private theorem rec5926 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(1),[4,8,12,16],[10],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[551]? = some (⟨101,(1),[4,8,12,16],[10],429⟩) from rfl))
private theorem rec5929 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(2),[4,8,12,16],[10],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[554]? = some (⟨101,(2),[4,8,12,16],[10],430⟩) from rfl))
private theorem rec5932 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(3),[4,8,12,16],[10],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[557]? = some (⟨101,(3),[4,8,12,16],[10],431⟩) from rfl))
private theorem rec5935 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(4),[4,8,12,16],[10],432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[560]? = some (⟨101,(4),[4,8,12,16],[10],432⟩) from rfl))
private theorem rec5938 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(5),[4,8,12,16],[10],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[563]? = some (⟨101,(5),[4,8,12,16],[10],429⟩) from rfl))
private theorem rec5941 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(6),[4,8,12,16],[10],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[566]? = some (⟨101,(6),[4,8,12,16],[10],430⟩) from rfl))
private theorem rec5944 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(7),[4,8,12,16],[10],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[569]? = some (⟨101,(7),[4,8,12,16],[10],431⟩) from rfl))
private theorem rec5947 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(8),[4,8,12,16],[10],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[572]? = some (⟨101,(8),[4,8,12,16],[10],428⟩) from rfl))
private theorem rec5950 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(9),[4,8,12,16],[10],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[575]? = some (⟨101,(9),[4,8,12,16],[10],429⟩) from rfl))
private theorem rec5953 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(10),[4,8,12,16],[10],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[578]? = some (⟨101,(10),[4,8,12,16],[10],430⟩) from rfl))
private theorem rec5956 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(11),[4,8,12,16],[10],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[581]? = some (⟨101,(11),[4,8,12,16],[10],431⟩) from rfl))
private theorem rec5959 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(12),[4,8,12,16],[10],433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[584]? = some (⟨101,(12),[4,8,12,16],[10],433⟩) from rfl))
private theorem rec5962 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(13),[4,8,12,16],[10],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[587]? = some (⟨101,(13),[4,8,12,16],[10],429⟩) from rfl))
private theorem rec5965 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(14),[4,8,12,16],[10],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[590]? = some (⟨101,(14),[4,8,12,16],[10],430⟩) from rfl))
private theorem rec5968 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 101 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(15),[4,8,12,16],[10],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[593]? = some (⟨101,(15),[4,8,12,16],[10],431⟩) from rfl))
private theorem rec5971 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(0),[4,8,12,16],[10],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[596]? = some (⟨104,(0),[4,8,12,16],[10],434⟩) from rfl))
private theorem rec5974 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(1),[4,8,12,16],[10],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[599]? = some (⟨104,(1),[4,8,12,16],[10],434⟩) from rfl))
private theorem rec5977 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(2),[4,8,12,16],[10],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[602]? = some (⟨104,(2),[4,8,12,16],[10],434⟩) from rfl))
private theorem rec5980 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(3),[4,8,12,16],[10],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[605]? = some (⟨104,(3),[4,8,12,16],[10],434⟩) from rfl))
private theorem rec5983 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(4),[4,8,12,16],[10],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[608]? = some (⟨104,(4),[4,8,12,16],[10],434⟩) from rfl))
private theorem rec5986 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(5),[4,8,12,16],[10],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[611]? = some (⟨104,(5),[4,8,12,16],[10],435⟩) from rfl))
private theorem rec5989 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(6),[4,8,12,16],[10],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[614]? = some (⟨104,(6),[4,8,12,16],[10],435⟩) from rfl))
private theorem rec5992 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(7),[4,8,12,16],[10],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[617]? = some (⟨104,(7),[4,8,12,16],[10],435⟩) from rfl))
private theorem rec5995 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(8),[4,8,12,16],[10],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[620]? = some (⟨104,(8),[4,8,12,16],[10],435⟩) from rfl))
private theorem rec5998 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(9),[4,8,12,16],[10],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[623]? = some (⟨104,(9),[4,8,12,16],[10],435⟩) from rfl))
private theorem rec6001 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(10),[4,8,12,16],[10],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[626]? = some (⟨104,(10),[4,8,12,16],[10],436⟩) from rfl))
private theorem rec6004 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(11),[4,8,12,16],[10],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[629]? = some (⟨104,(11),[4,8,12,16],[10],437⟩) from rfl))
private theorem rec6007 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(12),[4,8,12,16],[10],438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[632]? = some (⟨104,(12),[4,8,12,16],[10],438⟩) from rfl))
private theorem rec6010 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(13),[4,8,12,16],[10],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[635]? = some (⟨104,(13),[4,8,12,16],[10],437⟩) from rfl))
private theorem rec6013 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(14),[4,8,12,16],[10],439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[638]? = some (⟨104,(14),[4,8,12,16],[10],439⟩) from rfl))
private theorem rec6016 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(15),[4,8,12,16],[10],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[641]? = some (⟨104,(15),[4,8,12,16],[10],436⟩) from rfl))
private theorem rec6019 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(16),[4,8,12,16],[10],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[644]? = some (⟨104,(16),[4,8,12,16],[10],440⟩) from rfl))
private theorem rec6022 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(17),[4,8,12,16],[10],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[647]? = some (⟨104,(17),[4,8,12,16],[10],440⟩) from rfl))
private theorem rec6025 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(18),[4,8,12,16],[10],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[650]? = some (⟨104,(18),[4,8,12,16],[10],440⟩) from rfl))
private theorem rec6028 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(19),[4,8,12,16],[10],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[653]? = some (⟨104,(19),[4,8,12,16],[10],440⟩) from rfl))
private theorem rec6031 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(20),[4,8,12,16],[10],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[656]? = some (⟨104,(20),[4,8,12,16],[10],436⟩) from rfl))
private theorem rec6034 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(21),[4,8,12,16],[10],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[659]? = some (⟨104,(21),[4,8,12,16],[10],437⟩) from rfl))
private theorem rec6037 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(22),[4,8,12,16],[10],438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[662]? = some (⟨104,(22),[4,8,12,16],[10],438⟩) from rfl))
private theorem rec6040 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(23),[4,8,12,16],[10],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[665]? = some (⟨104,(23),[4,8,12,16],[10],437⟩) from rfl))
private theorem rec6043 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 104 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(24),[4,8,12,16],[10],439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[668]? = some (⟨104,(24),[4,8,12,16],[10],439⟩) from rfl))
private theorem rec6046 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(0),[4,8,12,16],[10],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[671]? = some (⟨106,(0),[4,8,12,16],[10],441⟩) from rfl))
private theorem rec6049 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(1),[4,8,12,16],[10],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[674]? = some (⟨106,(1),[4,8,12,16],[10],442⟩) from rfl))
private theorem rec6052 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(2),[4,8,12,16],[10],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[677]? = some (⟨106,(2),[4,8,12,16],[10],441⟩) from rfl))
private theorem rec6055 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(3),[4,8,12,16],[10],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[680]? = some (⟨106,(3),[4,8,12,16],[10],443⟩) from rfl))
private theorem rec6058 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(4),[4,8,12,16],[10],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[683]? = some (⟨106,(4),[4,8,12,16],[10],444⟩) from rfl))
private theorem rec6061 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(5),[4,8,12,16],[10],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[686]? = some (⟨106,(5),[4,8,12,16],[10],441⟩) from rfl))
private theorem rec6064 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(6),[4,8,12,16],[10],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[689]? = some (⟨106,(6),[4,8,12,16],[10],442⟩) from rfl))
private theorem rec6067 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(7),[4,8,12,16],[10],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[692]? = some (⟨106,(7),[4,8,12,16],[10],441⟩) from rfl))
private theorem rec6070 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(8),[4,8,12,16],[10],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[695]? = some (⟨106,(8),[4,8,12,16],[10],443⟩) from rfl))
private theorem rec6073 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(9),[4,8,12,16],[10],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[698]? = some (⟨106,(9),[4,8,12,16],[10],444⟩) from rfl))
private theorem rec6076 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(10),[4,8,12,16],[10],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[701]? = some (⟨106,(10),[4,8,12,16],[10],445⟩) from rfl))
private theorem rec6079 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(11),[4,8,12,16],[10],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[704]? = some (⟨106,(11),[4,8,12,16],[10],445⟩) from rfl))
private theorem rec6082 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(12),[4,8,12,16],[10],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[707]? = some (⟨106,(12),[4,8,12,16],[10],445⟩) from rfl))
private theorem rec6085 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(13),[4,8,12,16],[10],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[710]? = some (⟨106,(13),[4,8,12,16],[10],445⟩) from rfl))
private theorem rec6088 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(14),[4,8,12,16],[10],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[713]? = some (⟨106,(14),[4,8,12,16],[10],444⟩) from rfl))
private theorem rec6091 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(15),[4,8,12,16],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[716]? = some (⟨106,(15),[4,8,12,16],[10],446⟩) from rfl))
private theorem rec6094 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(16),[4,8,12,16],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[719]? = some (⟨106,(16),[4,8,12,16],[10],446⟩) from rfl))
private theorem rec6097 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(17),[4,8,12,16],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[722]? = some (⟨106,(17),[4,8,12,16],[10],446⟩) from rfl))
private theorem rec6100 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(18),[4,8,12,16],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[725]? = some (⟨106,(18),[4,8,12,16],[10],446⟩) from rfl))
private theorem rec6103 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(19),[4,8,12,16],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[728]? = some (⟨106,(19),[4,8,12,16],[10],446⟩) from rfl))
private theorem rec6106 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(20),[4,8,12,16],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[731]? = some (⟨106,(20),[4,8,12,16],[10],447⟩) from rfl))
private theorem rec6109 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(21),[4,8,12,16],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[734]? = some (⟨106,(21),[4,8,12,16],[10],447⟩) from rfl))
private theorem rec6112 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(22),[4,8,12,16],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[737]? = some (⟨106,(22),[4,8,12,16],[10],447⟩) from rfl))
private theorem rec6115 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(23),[4,8,12,16],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[740]? = some (⟨106,(23),[4,8,12,16],[10],447⟩) from rfl))
private theorem rec6118 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 106 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(24),[4,8,12,16],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[743]? = some (⟨106,(24),[4,8,12,16],[10],447⟩) from rfl))
private theorem rec6121 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(0),[4,8,12,16],[10],448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[746]? = some (⟨109,(0),[4,8,12,16],[10],448⟩) from rfl))
private theorem rec6124 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(1),[4,8,12,16],[10],448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[749]? = some (⟨109,(1),[4,8,12,16],[10],448⟩) from rfl))
private theorem rec6127 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(2),[4,8,12,16],[10],449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[752]? = some (⟨109,(2),[4,8,12,16],[10],449⟩) from rfl))
private theorem rec6130 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(3),[4,8,12,16],[10],449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[755]? = some (⟨109,(3),[4,8,12,16],[10],449⟩) from rfl))
private theorem rec6133 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(4),[4,8,12,16],[10],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[758]? = some (⟨109,(4),[4,8,12,16],[10],450⟩) from rfl))
private theorem rec6136 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(5),[4,8,12,16],[10],451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[761]? = some (⟨109,(5),[4,8,12,16],[10],451⟩) from rfl))
private theorem rec6139 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(6),[4,8,12,16],[10],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[764]? = some (⟨109,(6),[4,8,12,16],[10],450⟩) from rfl))
private theorem rec6142 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(7),[4,8,12,16],[10],452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[767]? = some (⟨109,(7),[4,8,12,16],[10],452⟩) from rfl))
private theorem rec6145 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(8),[4,8,12,16],[10],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[770]? = some (⟨109,(8),[4,8,12,16],[10],450⟩) from rfl))
private theorem rec6148 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 109 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(9),[4,8,12,16],[10],451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[773]? = some (⟨109,(9),[4,8,12,16],[10],451⟩) from rfl))
private theorem rec6151 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(0),[4,8,12,16],[10],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[776]? = some (⟨111,(0),[4,8,12,16],[10],453⟩) from rfl))
private theorem rec6154 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(1),[4,8,12,16],[10],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[779]? = some (⟨111,(1),[4,8,12,16],[10],454⟩) from rfl))
private theorem rec6157 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(2),[4,8,12,16],[10],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[782]? = some (⟨111,(2),[4,8,12,16],[10],453⟩) from rfl))
private theorem rec6160 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(3),[4,8,12,16],[10],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[785]? = some (⟨111,(3),[4,8,12,16],[10],455⟩) from rfl))
private theorem rec6163 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(4),[4,8,12,16],[10],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[788]? = some (⟨111,(4),[4,8,12,16],[10],456⟩) from rfl))
private theorem rec6166 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(5),[4,8,12,16],[10],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[791]? = some (⟨111,(5),[4,8,12,16],[10],453⟩) from rfl))
private theorem rec6169 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(6),[4,8,12,16],[10],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[794]? = some (⟨111,(6),[4,8,12,16],[10],454⟩) from rfl))
private theorem rec6172 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(7),[4,8,12,16],[10],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[797]? = some (⟨111,(7),[4,8,12,16],[10],453⟩) from rfl))
private theorem rec6175 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(8),[4,8,12,16],[10],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[800]? = some (⟨111,(8),[4,8,12,16],[10],455⟩) from rfl))
private theorem rec6178 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(9),[4,8,12,16],[10],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[803]? = some (⟨111,(9),[4,8,12,16],[10],456⟩) from rfl))
private theorem rec6181 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(10),[4,8,12,16],[10],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[806]? = some (⟨111,(10),[4,8,12,16],[10],457⟩) from rfl))
private theorem rec6184 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(11),[4,8,12,16],[10],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[809]? = some (⟨111,(11),[4,8,12,16],[10],457⟩) from rfl))
private theorem rec6187 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(12),[4,8,12,16],[10],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[812]? = some (⟨111,(12),[4,8,12,16],[10],457⟩) from rfl))
private theorem rec6190 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(13),[4,8,12,16],[10],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[815]? = some (⟨111,(13),[4,8,12,16],[10],457⟩) from rfl))
private theorem rec6193 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(14),[4,8,12,16],[10],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[818]? = some (⟨111,(14),[4,8,12,16],[10],456⟩) from rfl))
private theorem rec6196 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(15),[4,8,12,16],[10],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[821]? = some (⟨111,(15),[4,8,12,16],[10],458⟩) from rfl))
private theorem rec6199 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(16),[4,8,12,16],[10],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[824]? = some (⟨111,(16),[4,8,12,16],[10],458⟩) from rfl))
private theorem rec6202 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(17),[4,8,12,16],[10],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[827]? = some (⟨111,(17),[4,8,12,16],[10],458⟩) from rfl))
private theorem rec6205 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(18),[4,8,12,16],[10],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[830]? = some (⟨111,(18),[4,8,12,16],[10],458⟩) from rfl))
private theorem rec6208 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(19),[4,8,12,16],[10],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[833]? = some (⟨111,(19),[4,8,12,16],[10],458⟩) from rfl))
private theorem rec6211 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(20),[4,8,12,16],[10],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[836]? = some (⟨111,(20),[4,8,12,16],[10],459⟩) from rfl))
private theorem rec6214 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(21),[4,8,12,16],[10],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[839]? = some (⟨111,(21),[4,8,12,16],[10],459⟩) from rfl))
private theorem rec6217 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(22),[4,8,12,16],[10],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[842]? = some (⟨111,(22),[4,8,12,16],[10],459⟩) from rfl))
private theorem rec6220 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(23),[4,8,12,16],[10],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[845]? = some (⟨111,(23),[4,8,12,16],[10],459⟩) from rfl))
private theorem rec6223 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 111 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(24),[4,8,12,16],[10],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[848]? = some (⟨111,(24),[4,8,12,16],[10],459⟩) from rfl))
private theorem rec6226 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(0),[4,8,12,16],[10],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[851]? = some (⟨114,(0),[4,8,12,16],[10],460⟩) from rfl))
private theorem rec6229 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(1),[4,8,12,16],[10],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[854]? = some (⟨114,(1),[4,8,12,16],[10],460⟩) from rfl))
private theorem rec6232 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(2),[4,8,12,16],[10],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[857]? = some (⟨114,(2),[4,8,12,16],[10],460⟩) from rfl))
private theorem rec6235 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(3),[4,8,12,16],[10],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[860]? = some (⟨114,(3),[4,8,12,16],[10],460⟩) from rfl))
private theorem rec6238 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(4),[4,8,12,16],[10],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[863]? = some (⟨114,(4),[4,8,12,16],[10],460⟩) from rfl))
private theorem rec6241 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(5),[4,8,12,16],[10],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[866]? = some (⟨114,(5),[4,8,12,16],[10],461⟩) from rfl))
private theorem rec6244 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(6),[4,8,12,16],[10],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[869]? = some (⟨114,(6),[4,8,12,16],[10],461⟩) from rfl))
private theorem rec6247 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(7),[4,8,12,16],[10],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[872]? = some (⟨114,(7),[4,8,12,16],[10],461⟩) from rfl))
private theorem rec6250 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(8),[4,8,12,16],[10],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[875]? = some (⟨114,(8),[4,8,12,16],[10],461⟩) from rfl))
private theorem rec6253 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(9),[4,8,12,16],[10],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[878]? = some (⟨114,(9),[4,8,12,16],[10],461⟩) from rfl))
private theorem rec6256 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(10),[4,8,12,16],[10],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[881]? = some (⟨114,(10),[4,8,12,16],[10],462⟩) from rfl))
private theorem rec6259 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(11),[4,8,12,16],[10],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[884]? = some (⟨114,(11),[4,8,12,16],[10],463⟩) from rfl))
private theorem rec6262 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(12),[4,8,12,16],[10],464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[887]? = some (⟨114,(12),[4,8,12,16],[10],464⟩) from rfl))
private theorem rec6265 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(13),[4,8,12,16],[10],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[890]? = some (⟨114,(13),[4,8,12,16],[10],463⟩) from rfl))
private theorem rec6268 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(14),[4,8,12,16],[10],465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[893]? = some (⟨114,(14),[4,8,12,16],[10],465⟩) from rfl))
private theorem rec6271 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(15),[4,8,12,16],[10],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[896]? = some (⟨114,(15),[4,8,12,16],[10],462⟩) from rfl))
private theorem rec6274 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(16),[4,8,12,16],[10],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[899]? = some (⟨114,(16),[4,8,12,16],[10],466⟩) from rfl))
private theorem rec6277 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(17),[4,8,12,16],[10],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[902]? = some (⟨114,(17),[4,8,12,16],[10],466⟩) from rfl))
private theorem rec6280 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(18),[4,8,12,16],[10],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[905]? = some (⟨114,(18),[4,8,12,16],[10],466⟩) from rfl))
private theorem rec6283 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(19),[4,8,12,16],[10],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[908]? = some (⟨114,(19),[4,8,12,16],[10],466⟩) from rfl))
private theorem rec6286 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(20),[4,8,12,16],[10],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[911]? = some (⟨114,(20),[4,8,12,16],[10],462⟩) from rfl))
private theorem rec6289 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(21),[4,8,12,16],[10],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[914]? = some (⟨114,(21),[4,8,12,16],[10],463⟩) from rfl))
private theorem rec6292 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(22),[4,8,12,16],[10],464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[917]? = some (⟨114,(22),[4,8,12,16],[10],464⟩) from rfl))
private theorem rec6295 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(23),[4,8,12,16],[10],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[920]? = some (⟨114,(23),[4,8,12,16],[10],463⟩) from rfl))
private theorem rec6298 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 114 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(24),[4,8,12,16],[10],465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[923]? = some (⟨114,(24),[4,8,12,16],[10],465⟩) from rfl))
private theorem rec6301 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(0),[4,8,12,16],[10],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[926]? = some (⟨116,(0),[4,8,12,16],[10],467⟩) from rfl))
private theorem rec6304 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(1),[4,8,12,16],[10],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[929]? = some (⟨116,(1),[4,8,12,16],[10],468⟩) from rfl))
private theorem rec6307 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(2),[4,8,12,16],[10],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[932]? = some (⟨116,(2),[4,8,12,16],[10],467⟩) from rfl))
private theorem rec6310 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(3),[4,8,12,16],[10],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[935]? = some (⟨116,(3),[4,8,12,16],[10],469⟩) from rfl))
private theorem rec6313 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(4),[4,8,12,16],[10],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[938]? = some (⟨116,(4),[4,8,12,16],[10],470⟩) from rfl))
private theorem rec6316 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(5),[4,8,12,16],[10],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[941]? = some (⟨116,(5),[4,8,12,16],[10],467⟩) from rfl))
private theorem rec6319 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(6),[4,8,12,16],[10],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[944]? = some (⟨116,(6),[4,8,12,16],[10],468⟩) from rfl))
private theorem rec6322 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(7),[4,8,12,16],[10],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[947]? = some (⟨116,(7),[4,8,12,16],[10],467⟩) from rfl))
private theorem rec6325 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(8),[4,8,12,16],[10],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[950]? = some (⟨116,(8),[4,8,12,16],[10],469⟩) from rfl))
private theorem rec6328 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(9),[4,8,12,16],[10],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[953]? = some (⟨116,(9),[4,8,12,16],[10],470⟩) from rfl))
private theorem rec6331 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(10),[4,8,12,16],[10],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[956]? = some (⟨116,(10),[4,8,12,16],[10],471⟩) from rfl))
private theorem rec6334 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(11),[4,8,12,16],[10],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[959]? = some (⟨116,(11),[4,8,12,16],[10],471⟩) from rfl))
private theorem rec6337 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(12),[4,8,12,16],[10],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[962]? = some (⟨116,(12),[4,8,12,16],[10],471⟩) from rfl))
private theorem rec6340 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(13),[4,8,12,16],[10],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[965]? = some (⟨116,(13),[4,8,12,16],[10],471⟩) from rfl))
private theorem rec6343 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(14),[4,8,12,16],[10],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[968]? = some (⟨116,(14),[4,8,12,16],[10],470⟩) from rfl))
private theorem rec6346 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(15),[4,8,12,16],[10],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[971]? = some (⟨116,(15),[4,8,12,16],[10],472⟩) from rfl))
private theorem rec6349 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(16),[4,8,12,16],[10],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[974]? = some (⟨116,(16),[4,8,12,16],[10],472⟩) from rfl))
private theorem rec6352 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(17),[4,8,12,16],[10],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[977]? = some (⟨116,(17),[4,8,12,16],[10],472⟩) from rfl))
private theorem rec6355 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(18),[4,8,12,16],[10],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[980]? = some (⟨116,(18),[4,8,12,16],[10],472⟩) from rfl))
private theorem rec6358 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(19),[4,8,12,16],[10],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[983]? = some (⟨116,(19),[4,8,12,16],[10],472⟩) from rfl))
private theorem rec6361 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(20),[4,8,12,16],[10],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[986]? = some (⟨116,(20),[4,8,12,16],[10],473⟩) from rfl))
private theorem rec6364 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(21),[4,8,12,16],[10],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[989]? = some (⟨116,(21),[4,8,12,16],[10],473⟩) from rfl))
private theorem rec6367 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(22),[4,8,12,16],[10],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[992]? = some (⟨116,(22),[4,8,12,16],[10],473⟩) from rfl))
private theorem rec6370 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(23),[4,8,12,16],[10],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[995]? = some (⟨116,(23),[4,8,12,16],[10],473⟩) from rfl))
private theorem rec6373 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 116 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(24),[4,8,12,16],[10],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[998]? = some (⟨116,(24),[4,8,12,16],[10],473⟩) from rfl))
private theorem rec6376 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(0),[4,8,12,16],[10],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1001]? = some (⟨119,(0),[4,8,12,16],[10],474⟩) from rfl))
private theorem rec6379 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(1),[4,8,12,16],[10],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1004]? = some (⟨119,(1),[4,8,12,16],[10],474⟩) from rfl))
private theorem rec6382 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(2),[4,8,12,16],[10],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1007]? = some (⟨119,(2),[4,8,12,16],[10],474⟩) from rfl))
private theorem rec6385 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(3),[4,8,12,16],[10],712⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1010]? = some (⟨119,(3),[4,8,12,16],[10],712⟩) from rfl))
private theorem rec6389 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(4),[4,8,12,16],[10],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1014]? = some (⟨119,(4),[4,8,12,16],[10],474⟩) from rfl))
private theorem rec6392 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(5),[4,8,12,16],[10],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1017]? = some (⟨119,(5),[4,8,12,16],[10],475⟩) from rfl))
private theorem rec6395 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(6),[4,8,12,16],[10],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1020]? = some (⟨119,(6),[4,8,12,16],[10],475⟩) from rfl))
private theorem rec6398 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(7),[4,8,12,16],[10],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1023]? = some (⟨119,(7),[4,8,12,16],[10],475⟩) from rfl))
private theorem rec6401 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(8),[4,8,12,16],[10],714⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1026]? = some (⟨119,(8),[4,8,12,16],[10],714⟩) from rfl))
private theorem rec6405 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(9),[4,8,12,16],[10],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1030]? = some (⟨119,(9),[4,8,12,16],[10],475⟩) from rfl))
private theorem rec6408 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(10),[4,8,12,16],[10],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1033]? = some (⟨119,(10),[4,8,12,16],[10],476⟩) from rfl))
private theorem rec6411 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(11),[4,8,12,16],[10],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1036]? = some (⟨119,(11),[4,8,12,16],[10],477⟩) from rfl))
private theorem rec6414 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(12),[4,8,12,16],[10],478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1039]? = some (⟨119,(12),[4,8,12,16],[10],478⟩) from rfl))
private theorem rec6417 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(13),[4,8,12,16],[10],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1042]? = some (⟨119,(13),[4,8,12,16],[10],718⟩) from rfl))
private theorem rec6421 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(14),[4,8,12,16],[10],479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1046]? = some (⟨119,(14),[4,8,12,16],[10],479⟩) from rfl))
private theorem rec6424 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(15),[4,8,12,16],[10],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1049]? = some (⟨119,(15),[4,8,12,16],[10],476⟩) from rfl))
private theorem rec6427 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(16),[4,8,12,16],[10],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1052]? = some (⟨119,(16),[4,8,12,16],[10],480⟩) from rfl))
private theorem rec6430 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(17),[4,8,12,16],[10],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1055]? = some (⟨119,(17),[4,8,12,16],[10],480⟩) from rfl))
private theorem rec6433 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(18),[4,8,12,16],[10],721⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1058]? = some (⟨119,(18),[4,8,12,16],[10],721⟩) from rfl))
private theorem rec6437 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(19),[4,8,12,16],[10],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1062]? = some (⟨119,(19),[4,8,12,16],[10],480⟩) from rfl))
private theorem rec6440 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(20),[4,8,12,16],[10],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1065]? = some (⟨119,(20),[4,8,12,16],[10],476⟩) from rfl))
private theorem rec6443 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(21),[4,8,12,16],[10],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1068]? = some (⟨119,(21),[4,8,12,16],[10],477⟩) from rfl))
private theorem rec6446 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(22),[4,8,12,16],[10],478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1071]? = some (⟨119,(22),[4,8,12,16],[10],478⟩) from rfl))
private theorem rec6449 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(23),[4,8,12,16],[10],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1074]? = some (⟨119,(23),[4,8,12,16],[10],718⟩) from rfl))
private theorem rec6453 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 119 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(24),[4,8,12,16],[10],479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1078]? = some (⟨119,(24),[4,8,12,16],[10],479⟩) from rfl))
private theorem rec6456 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(0),[4,8,12,16],[10],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1081]? = some (⟨121,(0),[4,8,12,16],[10],481⟩) from rfl))
private theorem rec6459 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(1),[4,8,12,16],[10],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1084]? = some (⟨121,(1),[4,8,12,16],[10],482⟩) from rfl))
private theorem rec6462 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(2),[4,8,12,16],[10],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1087]? = some (⟨121,(2),[4,8,12,16],[10],481⟩) from rfl))
private theorem rec6465 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(3),[4,8,12,16],[10],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1090]? = some (⟨121,(3),[4,8,12,16],[10],483⟩) from rfl))
private theorem rec6468 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(4),[4,8,12,16],[10],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1093]? = some (⟨121,(4),[4,8,12,16],[10],484⟩) from rfl))
private theorem rec6471 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(5),[4,8,12,16],[10],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1096]? = some (⟨121,(5),[4,8,12,16],[10],481⟩) from rfl))
private theorem rec6474 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(6),[4,8,12,16],[10],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1099]? = some (⟨121,(6),[4,8,12,16],[10],482⟩) from rfl))
private theorem rec6477 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(7),[4,8,12,16],[10],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1102]? = some (⟨121,(7),[4,8,12,16],[10],481⟩) from rfl))
private theorem rec6480 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(8),[4,8,12,16],[10],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1105]? = some (⟨121,(8),[4,8,12,16],[10],483⟩) from rfl))
private theorem rec6483 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(9),[4,8,12,16],[10],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1108]? = some (⟨121,(9),[4,8,12,16],[10],484⟩) from rfl))
private theorem rec6486 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(10),[4,8,12,16],[10],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1111]? = some (⟨121,(10),[4,8,12,16],[10],485⟩) from rfl))
private theorem rec6489 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(11),[4,8,12,16],[10],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1114]? = some (⟨121,(11),[4,8,12,16],[10],485⟩) from rfl))
private theorem rec6492 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(12),[4,8,12,16],[10],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1117]? = some (⟨121,(12),[4,8,12,16],[10],485⟩) from rfl))
private theorem rec6495 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(13),[4,8,12,16],[10],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1120]? = some (⟨121,(13),[4,8,12,16],[10],485⟩) from rfl))
private theorem rec6498 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(14),[4,8,12,16],[10],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1123]? = some (⟨121,(14),[4,8,12,16],[10],484⟩) from rfl))
private theorem rec6501 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(15),[4,8,12,16],[10],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1126]? = some (⟨121,(15),[4,8,12,16],[10],486⟩) from rfl))
private theorem rec6504 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(16),[4,8,12,16],[10],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1129]? = some (⟨121,(16),[4,8,12,16],[10],486⟩) from rfl))
private theorem rec6507 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(17),[4,8,12,16],[10],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1132]? = some (⟨121,(17),[4,8,12,16],[10],486⟩) from rfl))
private theorem rec6510 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(18),[4,8,12,16],[10],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1135]? = some (⟨121,(18),[4,8,12,16],[10],486⟩) from rfl))
private theorem rec6513 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(19),[4,8,12,16],[10],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1138]? = some (⟨121,(19),[4,8,12,16],[10],486⟩) from rfl))
private theorem rec6516 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(20),[4,8,12,16],[10],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1141]? = some (⟨121,(20),[4,8,12,16],[10],487⟩) from rfl))
private theorem rec6519 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(21),[4,8,12,16],[10],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1144]? = some (⟨121,(21),[4,8,12,16],[10],487⟩) from rfl))
private theorem rec6522 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(22),[4,8,12,16],[10],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1147]? = some (⟨121,(22),[4,8,12,16],[10],487⟩) from rfl))
private theorem rec6525 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(23),[4,8,12,16],[10],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1150]? = some (⟨121,(23),[4,8,12,16],[10],487⟩) from rfl))
private theorem rec6528 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 121 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(24),[4,8,12,16],[10],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1153]? = some (⟨121,(24),[4,8,12,16],[10],487⟩) from rfl))
private theorem rec6531 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(0),[4,8,12,16],[10],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1156]? = some (⟨124,(0),[4,8,12,16],[10],488⟩) from rfl))
private theorem rec6534 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(1),[4,8,12,16],[10],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[2]? = some (⟨124,(1),[4,8,12,16],[10],489⟩) from rfl))
private theorem rec6537 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(2),[4,8,12,16],[10],490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[5]? = some (⟨124,(2),[4,8,12,16],[10],490⟩) from rfl))
private theorem rec6540 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(3),[4,8,12,16],[10],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[8]? = some (⟨124,(3),[4,8,12,16],[10],491⟩) from rfl))
private theorem rec6543 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(4),[4,8,12,16],[10],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[11]? = some (⟨124,(4),[4,8,12,16],[10],488⟩) from rfl))
private theorem rec6546 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(5),[4,8,12,16],[10],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[14]? = some (⟨124,(5),[4,8,12,16],[10],489⟩) from rfl))
private theorem rec6549 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(6),[4,8,12,16],[10],492⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[17]? = some (⟨124,(6),[4,8,12,16],[10],492⟩) from rfl))
private theorem rec6552 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(7),[4,8,12,16],[10],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[20]? = some (⟨124,(7),[4,8,12,16],[10],491⟩) from rfl))
private theorem rec6555 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(8),[4,8,12,16],[10],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[23]? = some (⟨124,(8),[4,8,12,16],[10],488⟩) from rfl))
private theorem rec6558 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(9),[4,8,12,16],[10],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[26]? = some (⟨124,(9),[4,8,12,16],[10],489⟩) from rfl))
private theorem rec6561 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(10),[4,8,12,16],[10],490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[29]? = some (⟨124,(10),[4,8,12,16],[10],490⟩) from rfl))
private theorem rec6564 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(11),[4,8,12,16],[10],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[32]? = some (⟨124,(11),[4,8,12,16],[10],491⟩) from rfl))
private theorem rec6567 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(12),[4,8,12,16],[10],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[35]? = some (⟨124,(12),[4,8,12,16],[10],488⟩) from rfl))
private theorem rec6570 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(13),[4,8,12,16],[10],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[38]? = some (⟨124,(13),[4,8,12,16],[10],489⟩) from rfl))
private theorem rec6573 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(14),[4,8,12,16],[10],493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[41]? = some (⟨124,(14),[4,8,12,16],[10],493⟩) from rfl))
private theorem rec6576 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 124 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(15),[4,8,12,16],[10],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[44]? = some (⟨124,(15),[4,8,12,16],[10],491⟩) from rfl))
private theorem rec6579 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(0),[4,8,12,16],[10],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[47]? = some (⟨127,(0),[4,8,12,16],[10],494⟩) from rfl))
private theorem rec6582 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(1),[4,8,12,16],[10],495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[50]? = some (⟨127,(1),[4,8,12,16],[10],495⟩) from rfl))
private theorem rec6585 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(2),[4,8,12,16],[10],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[53]? = some (⟨127,(2),[4,8,12,16],[10],494⟩) from rfl))
private theorem rec6588 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(3),[4,8,12,16],[10],496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[56]? = some (⟨127,(3),[4,8,12,16],[10],496⟩) from rfl))
private theorem rec6591 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(4),[4,8,12,16],[10],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[59]? = some (⟨127,(4),[4,8,12,16],[10],497⟩) from rfl))
private theorem rec6594 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(5),[4,8,12,16],[10],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[62]? = some (⟨127,(5),[4,8,12,16],[10],497⟩) from rfl))
private theorem rec6597 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(6),[4,8,12,16],[10],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[65]? = some (⟨127,(6),[4,8,12,16],[10],497⟩) from rfl))
private theorem rec6600 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(7),[4,8,12,16],[10],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[68]? = some (⟨127,(7),[4,8,12,16],[10],497⟩) from rfl))
private theorem rec6603 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(8),[4,8,12,16],[10],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[71]? = some (⟨127,(8),[4,8,12,16],[10],498⟩) from rfl))
private theorem rec6606 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(9),[4,8,12,16],[10],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[74]? = some (⟨127,(9),[4,8,12,16],[10],498⟩) from rfl))
private theorem rec6609 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(10),[4,8,12,16],[10],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[77]? = some (⟨127,(10),[4,8,12,16],[10],498⟩) from rfl))
private theorem rec6612 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(11),[4,8,12,16],[10],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[80]? = some (⟨127,(11),[4,8,12,16],[10],498⟩) from rfl))
private theorem rec6615 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(12),[4,8,12,16],[10],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[83]? = some (⟨127,(12),[4,8,12,16],[10],499⟩) from rfl))
private theorem rec6618 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(13),[4,8,12,16],[10],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[86]? = some (⟨127,(13),[4,8,12,16],[10],499⟩) from rfl))
private theorem rec6621 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(14),[4,8,12,16],[10],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[89]? = some (⟨127,(14),[4,8,12,16],[10],499⟩) from rfl))
private theorem rec6624 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 127 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(15),[4,8,12,16],[10],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[92]? = some (⟨127,(15),[4,8,12,16],[10],499⟩) from rfl))
private theorem rec6627 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(0),[4,8,12],[10],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[95]? = some (⟨129,(0),[4,8,12],[10],500⟩) from rfl))
private theorem rec6630 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(1),[4,8,12],[10],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[98]? = some (⟨129,(1),[4,8,12],[10],501⟩) from rfl))
private theorem rec6633 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(2),[4,8,12],[10],502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[101]? = some (⟨129,(2),[4,8,12],[10],502⟩) from rfl))
private theorem rec6636 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(3),[4,8,12],[10],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[104]? = some (⟨129,(3),[4,8,12],[10],503⟩) from rfl))
private theorem rec6639 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(4),[4,8,12],[10],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[107]? = some (⟨129,(4),[4,8,12],[10],500⟩) from rfl))
private theorem rec6642 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(5),[4,8,12],[10],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[110]? = some (⟨129,(5),[4,8,12],[10],501⟩) from rfl))
private theorem rec6645 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(6),[4,8,12],[10],504⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[113]? = some (⟨129,(6),[4,8,12],[10],504⟩) from rfl))
private theorem rec6648 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(7),[4,8,12],[10],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[116]? = some (⟨129,(7),[4,8,12],[10],503⟩) from rfl))
private theorem rec6651 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(8),[4,8,12],[10],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[119]? = some (⟨129,(8),[4,8,12],[10],500⟩) from rfl))
private theorem rec6654 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(9),[4,8,12],[10],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[122]? = some (⟨129,(9),[4,8,12],[10],501⟩) from rfl))
private theorem rec6657 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(10),[4,8,12],[10],502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[125]? = some (⟨129,(10),[4,8,12],[10],502⟩) from rfl))
private theorem rec6660 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(11),[4,8,12],[10],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[128]? = some (⟨129,(11),[4,8,12],[10],503⟩) from rfl))
private theorem rec6663 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(12),[4,8,12],[10],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[131]? = some (⟨129,(12),[4,8,12],[10],500⟩) from rfl))
private theorem rec6666 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(13),[4,8,12],[10],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[134]? = some (⟨129,(13),[4,8,12],[10],501⟩) from rfl))
private theorem rec6669 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(14),[4,8,12],[10],505⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[137]? = some (⟨129,(14),[4,8,12],[10],505⟩) from rfl))
private theorem rec6672 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 129 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(15),[4,8,12],[10],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[140]? = some (⟨129,(15),[4,8,12],[10],503⟩) from rfl))
private theorem rec6675 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 132 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(0),[4,8,12],[10],506⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[143]? = some (⟨132,(0),[4,8,12],[10],506⟩) from rfl))
private theorem rec6678 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 132 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(1),[4,8,12],[10],507⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[146]? = some (⟨132,(1),[4,8,12],[10],507⟩) from rfl))
private theorem rec6681 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 132 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(2),[4,8,12],[10],508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[149]? = some (⟨132,(2),[4,8,12],[10],508⟩) from rfl))
private theorem rec6684 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 132 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(3),[4,8,12],[10],509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[152]? = some (⟨132,(3),[4,8,12],[10],509⟩) from rfl))
private theorem rec6688 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(0),[8,12],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[156]? = some (⟨134,(0),[8,12],[10],1266⟩) from rfl))
private theorem rec6691 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(1),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[159]? = some (⟨134,(1),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6694 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(2),[4,8,12,16],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[162]? = some (⟨134,(2),[4,8,12,16],[10],1266⟩) from rfl))
private theorem rec6697 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(3),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[165]? = some (⟨134,(3),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec6700 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(4),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[168]? = some (⟨134,(4),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6703 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(5),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[171]? = some (⟨134,(5),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6706 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(6),[4,8,12,16],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[174]? = some (⟨134,(6),[4,8,12,16],[10],1266⟩) from rfl))
private theorem rec6709 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(7),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[177]? = some (⟨134,(7),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec6712 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(8),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[180]? = some (⟨134,(8),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6715 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(9),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[183]? = some (⟨134,(9),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6718 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(10),[4,8,12,16],[10],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[186]? = some (⟨134,(10),[4,8,12,16],[10],512⟩) from rfl))
private theorem rec6721 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(11),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[189]? = some (⟨134,(11),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec6724 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(12),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[192]? = some (⟨134,(12),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6727 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(13),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[195]? = some (⟨134,(13),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6730 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(14),[4,8,12,16],[10],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[198]? = some (⟨134,(14),[4,8,12,16],[10],1266⟩) from rfl))
private theorem rec6733 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(15),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[201]? = some (⟨134,(15),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec6736 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(16),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[204]? = some (⟨134,(16),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6739 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(17),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[207]? = some (⟨134,(17),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec6742 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(18),[4,8,12,16],[10],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[210]? = some (⟨134,(18),[4,8,12,16],[10],514⟩) from rfl))
private theorem rec6745 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 134 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(19),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[213]? = some (⟨134,(19),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec6748 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(0),[4,8,12,16],[10],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[216]? = some (⟨135,(0),[4,8,12,16],[10],515⟩) from rfl))
private theorem rec6751 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(1),[4,8,12,16],[10],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[219]? = some (⟨135,(1),[4,8,12,16],[10],515⟩) from rfl))
private theorem rec6754 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(2),[4,8,12,16],[10],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[222]? = some (⟨135,(2),[4,8,12,16],[10],516⟩) from rfl))
private theorem rec6757 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(3),[4,8,12,16],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[225]? = some (⟨135,(3),[4,8,12,16],[10],517⟩) from rfl))
private theorem rec6760 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(4),[4,8,12,16],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[228]? = some (⟨135,(4),[4,8,12,16],[10],518⟩) from rfl))
private theorem rec6763 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(5),[4,8,12,16],[10],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[231]? = some (⟨135,(5),[4,8,12,16],[10],515⟩) from rfl))
private theorem rec6766 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(6),[4,8,12,16],[10],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[234]? = some (⟨135,(6),[4,8,12,16],[10],515⟩) from rfl))
private theorem rec6769 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(7),[4,8,12,16],[10],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[237]? = some (⟨135,(7),[4,8,12,16],[10],516⟩) from rfl))
private theorem rec6772 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(8),[4,8,12,16],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[240]? = some (⟨135,(8),[4,8,12,16],[10],517⟩) from rfl))
private theorem rec6775 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(9),[4,8,12,16],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[243]? = some (⟨135,(9),[4,8,12,16],[10],518⟩) from rfl))
private theorem rec6778 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(10),[4,8,12,16],[10],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[246]? = some (⟨135,(10),[4,8,12,16],[10],519⟩) from rfl))
private theorem rec6781 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(11),[4,8,12,16],[10],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[249]? = some (⟨135,(11),[4,8,12,16],[10],519⟩) from rfl))
private theorem rec6784 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(12),[4,8,12,16],[10],520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[252]? = some (⟨135,(12),[4,8,12,16],[10],520⟩) from rfl))
private theorem rec6787 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(13),[4,8,12,16],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[255]? = some (⟨135,(13),[4,8,12,16],[10],517⟩) from rfl))
private theorem rec6790 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(14),[4,8,12,16],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[258]? = some (⟨135,(14),[4,8,12,16],[10],518⟩) from rfl))
private theorem rec6793 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(15),[4,8,12,16],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[261]? = some (⟨135,(15),[4,8,12,16],[10],521⟩) from rfl))
private theorem rec6796 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(16),[4,8,12,16],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[264]? = some (⟨135,(16),[4,8,12,16],[10],521⟩) from rfl))
private theorem rec6799 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(17),[4,8,12,16],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[267]? = some (⟨135,(17),[4,8,12,16],[10],521⟩) from rfl))
private theorem rec6805 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(18),[12],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[273]? = some (⟨135,(18),[12],[10],521⟩) from rfl))
private theorem rec6807 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(19),[4,8,12,16],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[275]? = some (⟨135,(19),[4,8,12,16],[10],521⟩) from rfl))
private theorem rec6810 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(20),[4,8,12,16],[10],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[278]? = some (⟨135,(20),[4,8,12,16],[10],522⟩) from rfl))
private theorem rec6813 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(21),[4,8,12,16],[10],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[281]? = some (⟨135,(21),[4,8,12,16],[10],522⟩) from rfl))
private theorem rec6816 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(22),[4,8,12,16],[10],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[284]? = some (⟨135,(22),[4,8,12,16],[10],522⟩) from rfl))
private theorem rec6819 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(23),[4,8,12,16],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[287]? = some (⟨135,(23),[4,8,12,16],[10],517⟩) from rfl))
private theorem rec6823 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 135 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(24),[8,12],[10],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[291]? = some (⟨135,(24),[8,12],[10],522⟩) from rfl))
private theorem rec6827 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(0),[4,8,12,16],[10],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[295]? = some (⟨136,(0),[4,8,12,16],[10],524⟩) from rfl))
private theorem rec6831 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(1),[4,8,12,16],[10],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[299]? = some (⟨136,(1),[4,8,12,16],[10],524⟩) from rfl))
private theorem rec6834 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(2),[4,8,12,16],[10],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[302]? = some (⟨136,(2),[4,8,12,16],[10],524⟩) from rfl))
private theorem rec6837 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(3),[4,8,12,16],[10],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[305]? = some (⟨136,(3),[4,8,12,16],[10],524⟩) from rfl))
private theorem rec6840 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(4),[4,8,12,16],[10],525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[308]? = some (⟨136,(4),[4,8,12,16],[10],525⟩) from rfl))
private theorem rec6843 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(5),[4,8,12,16],[10],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[311]? = some (⟨136,(5),[4,8,12,16],[10],523⟩) from rfl))
private theorem rec6846 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(6),[4,8,12,16],[10],527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[314]? = some (⟨136,(6),[4,8,12,16],[10],527⟩) from rfl))
private theorem rec6850 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(7),[4,8,12,16],[10],527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[318]? = some (⟨136,(7),[4,8,12,16],[10],527⟩) from rfl))
private theorem rec6853 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(8),[4,8,12,16],[10],527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[321]? = some (⟨136,(8),[4,8,12,16],[10],527⟩) from rfl))
private theorem rec6856 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(9),[4,8,12,16],[10],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[324]? = some (⟨136,(9),[4,8,12,16],[10],528⟩) from rfl))
private theorem rec6859 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(10),[4,8,12,16],[10],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[327]? = some (⟨136,(10),[4,8,12,16],[10],523⟩) from rfl))
private theorem rec6862 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(11),[4,8,12,16],[10],526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[330]? = some (⟨136,(11),[4,8,12,16],[10],526⟩) from rfl))
private theorem rec6865 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(12),[4,8,12,16],[10],529⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[333]? = some (⟨136,(12),[4,8,12,16],[10],529⟩) from rfl))
private theorem rec6868 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(13),[4,8,12,16],[10],530⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[336]? = some (⟨136,(13),[4,8,12,16],[10],530⟩) from rfl))
private theorem rec6871 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(14),[4,8,12,16],[10],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[339]? = some (⟨136,(14),[4,8,12,16],[10],531⟩) from rfl))
private theorem rec6874 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(15),[4,8,12,16],[10],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[342]? = some (⟨136,(15),[4,8,12,16],[10],523⟩) from rfl))
private theorem rec6877 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(16),[4,8,12,16],[10],526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[345]? = some (⟨136,(16),[4,8,12,16],[10],526⟩) from rfl))
private theorem rec6880 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(17),[4,8,12,16],[10],532⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[348]? = some (⟨136,(17),[4,8,12,16],[10],532⟩) from rfl))
private theorem rec6883 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(18),[4,8,12,16],[10],533⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[351]? = some (⟨136,(18),[4,8,12,16],[10],533⟩) from rfl))
private theorem rec6886 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(19),[4,8,12,16],[10],534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[354]? = some (⟨136,(19),[4,8,12,16],[10],534⟩) from rfl))
private theorem rec6889 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(20),[4,8,12,16],[10],535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[357]? = some (⟨136,(20),[4,8,12,16],[10],535⟩) from rfl))
private theorem rec6892 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(21),[4,8,12,16],[10],536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[360]? = some (⟨136,(21),[4,8,12,16],[10],536⟩) from rfl))
private theorem rec6895 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(22),[4,8,12,16],[10],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[363]? = some (⟨136,(22),[4,8,12,16],[10],537⟩) from rfl))
private theorem rec6898 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(23),[4,8,12,16],[10],538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[366]? = some (⟨136,(23),[4,8,12,16],[10],538⟩) from rfl))
private theorem rec6902 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 136 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(24),[8,12],[10],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[370]? = some (⟨136,(24),[8,12],[10],531⟩) from rfl))
private theorem rec6905 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(0),[4,8,12,16],[10],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[373]? = some (⟨138,(0),[4,8,12,16],[10],539⟩) from rfl))
private theorem rec6908 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(1),[4,8,12,16],[10],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[376]? = some (⟨138,(1),[4,8,12,16],[10],539⟩) from rfl))
private theorem rec6911 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(2),[4,8,12,16],[10],540⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[379]? = some (⟨138,(2),[4,8,12,16],[10],540⟩) from rfl))
private theorem rec6914 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(3),[4,8,12,16],[10],541⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[382]? = some (⟨138,(3),[4,8,12,16],[10],541⟩) from rfl))
private theorem rec6917 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(4),[4,8,12,16],[10],542⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[385]? = some (⟨138,(4),[4,8,12,16],[10],542⟩) from rfl))
private theorem rec6921 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(5),[8,12],[10],1635⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[389]? = some (⟨138,(5),[8,12],[10],1635⟩) from rfl))
private theorem rec6925 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(6),[8,12],[10],1635⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[393]? = some (⟨138,(6),[8,12],[10],1635⟩) from rfl))
private theorem rec6929 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(7),[8,12],[10],1636⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[397]? = some (⟨138,(7),[8,12],[10],1636⟩) from rfl))
private theorem rec6933 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(8),[8,12],[10],1637⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[401]? = some (⟨138,(8),[8,12],[10],1637⟩) from rfl))
private theorem rec6937 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(9),[8,12],[10],1638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[405]? = some (⟨138,(9),[8,12],[10],1638⟩) from rfl))
private theorem rec6940 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(10),[4,8,12,16],[10],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[408]? = some (⟨138,(10),[4,8,12,16],[10],545⟩) from rfl))
private theorem rec6943 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(11),[4,8,12,16],[10],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[411]? = some (⟨138,(11),[4,8,12,16],[10],545⟩) from rfl))
private theorem rec6946 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(12),[4,8,12,16],[10],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[414]? = some (⟨138,(12),[4,8,12,16],[10],544⟩) from rfl))
private theorem rec6949 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(13),[4,8,12,16],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[417]? = some (⟨138,(13),[4,8,12,16],[10],517⟩) from rfl))
private theorem rec6952 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(14),[4,8,12,16],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[420]? = some (⟨138,(14),[4,8,12,16],[10],518⟩) from rfl))
private theorem rec6955 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(15),[4,8,12,16],[10],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[423]? = some (⟨138,(15),[4,8,12,16],[10],546⟩) from rfl))
private theorem rec6958 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(16),[4,8,12,16],[10],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[426]? = some (⟨138,(16),[4,8,12,16],[10],546⟩) from rfl))
private theorem rec6961 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(17),[4,8,12,16],[10],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[429]? = some (⟨138,(17),[4,8,12,16],[10],544⟩) from rfl))
private theorem rec6964 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(18),[4,8,12,16],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[432]? = some (⟨138,(18),[4,8,12,16],[10],517⟩) from rfl))
private theorem rec6967 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(19),[4,8,12,16],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[435]? = some (⟨138,(19),[4,8,12,16],[10],518⟩) from rfl))
private theorem rec6970 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(20),[4,8,12,16],[10],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[438]? = some (⟨138,(20),[4,8,12,16],[10],547⟩) from rfl))
private theorem rec6973 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(21),[4,8,12,16],[10],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[441]? = some (⟨138,(21),[4,8,12,16],[10],547⟩) from rfl))
private theorem rec6976 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(22),[4,8,12,16],[10],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[444]? = some (⟨138,(22),[4,8,12,16],[10],547⟩) from rfl))
private theorem rec6979 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(23),[4,8,12,16],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[447]? = some (⟨138,(23),[4,8,12,16],[10],517⟩) from rfl))
private theorem rec6982 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 138 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(24),[4,8,12,16],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[450]? = some (⟨138,(24),[4,8,12,16],[10],518⟩) from rfl))
private theorem rec6985 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(0),[4,8,12,16],[10],548⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[453]? = some (⟨139,(0),[4,8,12,16],[10],548⟩) from rfl))
private theorem rec6988 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(1),[4,8,12,16],[10],549⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[456]? = some (⟨139,(1),[4,8,12,16],[10],549⟩) from rfl))
private theorem rec6991 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(2),[4,8,12,16],[10],548⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[459]? = some (⟨139,(2),[4,8,12,16],[10],548⟩) from rfl))
private theorem rec6994 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(3),[4,8,12,16],[10],550⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[462]? = some (⟨139,(3),[4,8,12,16],[10],550⟩) from rfl))
private theorem rec6997 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(4),[4,8,12,16],[10],551⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[465]? = some (⟨139,(4),[4,8,12,16],[10],551⟩) from rfl))
private theorem rec7001 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(5),[8,12],[10],1639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[469]? = some (⟨139,(5),[8,12],[10],1639⟩) from rfl))
private theorem rec7005 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(6),[8,12],[10],1640⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[473]? = some (⟨139,(6),[8,12],[10],1640⟩) from rfl))
private theorem rec7009 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(7),[8,12],[10],1641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[477]? = some (⟨139,(7),[8,12],[10],1641⟩) from rfl))
private theorem rec7012 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(8),[4,8,12,16],[10],555⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[480]? = some (⟨139,(8),[4,8,12,16],[10],555⟩) from rfl))
private theorem rec7015 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(9),[4,8,12,16],[10],556⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[483]? = some (⟨139,(9),[4,8,12,16],[10],556⟩) from rfl))
private theorem rec7018 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(10),[4,8,12,16],[10],557⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[486]? = some (⟨139,(10),[4,8,12,16],[10],557⟩) from rfl))
private theorem rec7021 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(11),[4,8,12,16],[10],558⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[489]? = some (⟨139,(11),[4,8,12,16],[10],558⟩) from rfl))
private theorem rec7024 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(12),[4,8,12,16],[10],559⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[492]? = some (⟨139,(12),[4,8,12,16],[10],559⟩) from rfl))
private theorem rec7027 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(13),[4,8,12,16],[10],560⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[495]? = some (⟨139,(13),[4,8,12,16],[10],560⟩) from rfl))
private theorem rec7030 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(14),[4,8,12,16],[10],561⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[498]? = some (⟨139,(14),[4,8,12,16],[10],561⟩) from rfl))
private theorem rec7033 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(15),[4,8,12,16],[10],562⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[501]? = some (⟨139,(15),[4,8,12,16],[10],562⟩) from rfl))
private theorem rec7036 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(16),[4,8,12,16],[10],555⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[504]? = some (⟨139,(16),[4,8,12,16],[10],555⟩) from rfl))
private theorem rec7039 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(17),[4,8,12,16],[10],556⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[507]? = some (⟨139,(17),[4,8,12,16],[10],556⟩) from rfl))
private theorem rec7042 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(18),[4,8,12,16],[10],557⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[510]? = some (⟨139,(18),[4,8,12,16],[10],557⟩) from rfl))
private theorem rec7045 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 139 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(19),[4,8,12,16],[10],558⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[513]? = some (⟨139,(19),[4,8,12,16],[10],558⟩) from rfl))
private theorem rec7048 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 140 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(0),[4,8,12,16],[10],563⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[516]? = some (⟨140,(0),[4,8,12,16],[10],563⟩) from rfl))
private theorem rec7051 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 140 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(1),[4,8,12,16],[10],564⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[519]? = some (⟨140,(1),[4,8,12,16],[10],564⟩) from rfl))
private theorem rec7054 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 140 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(2),[4,8,12,16],[10],565⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[522]? = some (⟨140,(2),[4,8,12,16],[10],565⟩) from rfl))
private theorem rec7057 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 140 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(3),[4,8,12,16],[10],1270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[525]? = some (⟨140,(3),[4,8,12,16],[10],1270⟩) from rfl))
private theorem rec7062 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 140 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(4),[4,8,12,16],[10],566⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[530]? = some (⟨140,(4),[4,8,12,16],[10],566⟩) from rfl))
private theorem rec7065 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 140 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(5),[4,8,12,16],[10],564⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[533]? = some (⟨140,(5),[4,8,12,16],[10],564⟩) from rfl))
private theorem rec7069 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 140 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(6),[8,12],[10],1642⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[537]? = some (⟨140,(6),[8,12],[10],1642⟩) from rfl))
private theorem rec7074 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 140 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(7),[8,12],[10],1643⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[542]? = some (⟨140,(7),[8,12],[10],1643⟩) from rfl))
private theorem rec7077 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(0),[4,8,12,16],[10],568⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[545]? = some (⟨142,(0),[4,8,12,16],[10],568⟩) from rfl))
private theorem rec7080 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(1),[4,8,12,16],[10],569⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[548]? = some (⟨142,(1),[4,8,12,16],[10],569⟩) from rfl))
private theorem rec7083 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(2),[4,8,12,16],[10],570⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[551]? = some (⟨142,(2),[4,8,12,16],[10],570⟩) from rfl))
private theorem rec7086 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(3),[4,8,12,16],[10],571⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[554]? = some (⟨142,(3),[4,8,12,16],[10],571⟩) from rfl))
private theorem rec7089 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(4),[4,8,12,16],[10],572⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[557]? = some (⟨142,(4),[4,8,12,16],[10],572⟩) from rfl))
private theorem rec7092 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(5),[4,8,12,16],[10],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[560]? = some (⟨142,(5),[4,8,12,16],[10],573⟩) from rfl))
private theorem rec7095 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(6),[4,8,12,16],[10],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[563]? = some (⟨142,(6),[4,8,12,16],[10],573⟩) from rfl))
private theorem rec7098 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(7),[4,8,12,16],[10],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[566]? = some (⟨142,(7),[4,8,12,16],[10],573⟩) from rfl))
private theorem rec7101 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(8),[4,8,12,16],[10],574⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[569]? = some (⟨142,(8),[4,8,12,16],[10],574⟩) from rfl))
private theorem rec7104 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(9),[4,8,12,16],[10],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[572]? = some (⟨142,(9),[4,8,12,16],[10],575⟩) from rfl))
private theorem rec7107 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(10),[4,8,12,16],[10],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[575]? = some (⟨142,(10),[4,8,12,16],[10],575⟩) from rfl))
private theorem rec7110 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(11),[4,8,12,16],[10],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[578]? = some (⟨142,(11),[4,8,12,16],[10],575⟩) from rfl))
private theorem rec7113 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(12),[4,8,12,16],[10],576⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[581]? = some (⟨142,(12),[4,8,12,16],[10],576⟩) from rfl))
private theorem rec7116 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(13),[4,8,12,16],[10],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[584]? = some (⟨142,(13),[4,8,12,16],[10],577⟩) from rfl))
private theorem rec7119 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(14),[4,8,12,16],[10],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[587]? = some (⟨142,(14),[4,8,12,16],[10],577⟩) from rfl))
private theorem rec7122 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 142 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(15),[4,8,12,16],[10],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[590]? = some (⟨142,(15),[4,8,12,16],[10],577⟩) from rfl))
private theorem rec7125 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(0),[4,8,12,16],[10],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[593]? = some (⟨143,(0),[4,8,12,16],[10],578⟩) from rfl))
private theorem rec7128 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(1),[4,8,12,16],[10],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[596]? = some (⟨143,(1),[4,8,12,16],[10],579⟩) from rfl))
private theorem rec7131 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(2),[4,8,12,16],[10],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[599]? = some (⟨143,(2),[4,8,12,16],[10],580⟩) from rfl))
private theorem rec7134 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(3),[4,8,12,16],[10],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[602]? = some (⟨143,(3),[4,8,12,16],[10],581⟩) from rfl))
private theorem rec7137 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(4),[4,8,12,16],[10],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[605]? = some (⟨143,(4),[4,8,12,16],[10],582⟩) from rfl))
private theorem rec7140 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(5),[4,8,12,16],[10],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[608]? = some (⟨143,(5),[4,8,12,16],[10],583⟩) from rfl))
private theorem rec7143 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(6),[4,8,12,16],[10],584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[611]? = some (⟨143,(6),[4,8,12,16],[10],584⟩) from rfl))
private theorem rec7146 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(7),[4,8,12,16],[10],585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[614]? = some (⟨143,(7),[4,8,12,16],[10],585⟩) from rfl))
private theorem rec7149 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(8),[4,8,12,16],[10],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[617]? = some (⟨143,(8),[4,8,12,16],[10],578⟩) from rfl))
private theorem rec7152 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(9),[4,8,12,16],[10],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[620]? = some (⟨143,(9),[4,8,12,16],[10],579⟩) from rfl))
private theorem rec7155 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(10),[4,8,12,16],[10],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[623]? = some (⟨143,(10),[4,8,12,16],[10],580⟩) from rfl))
private theorem rec7158 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(11),[4,8,12,16],[10],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[626]? = some (⟨143,(11),[4,8,12,16],[10],581⟩) from rfl))
private theorem rec7161 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(12),[4,8,12,16],[10],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[629]? = some (⟨143,(12),[4,8,12,16],[10],586⟩) from rfl))
private theorem rec7164 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(13),[4,8,12,16],[10],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[632]? = some (⟨143,(13),[4,8,12,16],[10],587⟩) from rfl))
private theorem rec7167 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(14),[4,8,12,16],[10],588⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[635]? = some (⟨143,(14),[4,8,12,16],[10],588⟩) from rfl))
private theorem rec7170 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 143 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(15),[4,8,12,16],[10],589⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[638]? = some (⟨143,(15),[4,8,12,16],[10],589⟩) from rfl))
private theorem rec7173 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 144 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(0),[4,8,12,16],[10],590⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[641]? = some (⟨144,(0),[4,8,12,16],[10],590⟩) from rfl))
private theorem rec7176 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 144 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(1),[4,8,12,16],[10],591⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[644]? = some (⟨144,(1),[4,8,12,16],[10],591⟩) from rfl))
private theorem rec7179 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 144 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(2),[4,8,12,16],[10],590⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[647]? = some (⟨144,(2),[4,8,12,16],[10],590⟩) from rfl))
private theorem rec7182 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 144 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(3),[4,8,12,16],[10],592⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[650]? = some (⟨144,(3),[4,8,12,16],[10],592⟩) from rfl))
private theorem rec7185 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(0),[4,8,12,16],[10],593⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[653]? = some (⟨145,(0),[4,8,12,16],[10],593⟩) from rfl))
private theorem rec7190 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(1),[12],[10],1714⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[658]? = some (⟨145,(1),[12],[10],1714⟩) from rfl))
private theorem rec7192 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(2),[4,8,12,16],[10],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[660]? = some (⟨145,(2),[4,8,12,16],[10],595⟩) from rfl))
private theorem rec7195 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(3),[4,8,12,16],[10],1271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[663]? = some (⟨145,(3),[4,8,12,16],[10],1271⟩) from rfl))
private theorem rec7199 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(4),[4,8,12,16],[10],597⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[667]? = some (⟨145,(4),[4,8,12,16],[10],597⟩) from rfl))
private theorem rec7202 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(5),[4,8,12,16],[10],598⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[670]? = some (⟨145,(5),[4,8,12,16],[10],598⟩) from rfl))
private theorem rec7205 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(6),[4,8,12,16],[10],599⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[673]? = some (⟨145,(6),[4,8,12,16],[10],599⟩) from rfl))
private theorem rec7208 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(7),[4,8,12,16],[10],600⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[676]? = some (⟨145,(7),[4,8,12,16],[10],600⟩) from rfl))
private theorem rec7211 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(8),[4,8,12,16],[10],593⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[679]? = some (⟨145,(8),[4,8,12,16],[10],593⟩) from rfl))
private theorem rec7214 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(9),[4,8,12,16],[10],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[682]? = some (⟨145,(9),[4,8,12,16],[10],594⟩) from rfl))
private theorem rec7217 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(10),[4,8,12,16],[10],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[685]? = some (⟨145,(10),[4,8,12,16],[10],595⟩) from rfl))
private theorem rec7220 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(11),[4,8,12,16],[10],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[688]? = some (⟨145,(11),[4,8,12,16],[10],596⟩) from rfl))
private theorem rec7223 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(12),[4,8,12,16],[10],601⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[691]? = some (⟨145,(12),[4,8,12,16],[10],601⟩) from rfl))
private theorem rec7226 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(13),[4,8,12,16],[10],602⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[694]? = some (⟨145,(13),[4,8,12,16],[10],602⟩) from rfl))
private theorem rec7229 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(14),[4,8,12,16],[10],603⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[697]? = some (⟨145,(14),[4,8,12,16],[10],603⟩) from rfl))
private theorem rec7232 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 145 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(15),[4,8,12,16],[10],604⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[700]? = some (⟨145,(15),[4,8,12,16],[10],604⟩) from rfl))
private theorem rec7235 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(0),[4,8,12,16],[10],869⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[703]? = some (⟨146,(0),[4,8,12,16],[10],869⟩) from rfl))
private theorem rec7239 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(1),[4,8,12,16],[10],870⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[707]? = some (⟨146,(1),[4,8,12,16],[10],870⟩) from rfl))
private theorem rec7243 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(2),[4,8,12,16],[10],607⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[711]? = some (⟨146,(2),[4,8,12,16],[10],607⟩) from rfl))
private theorem rec7246 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(3),[4,8,12,16],[10],871⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[714]? = some (⟨146,(3),[4,8,12,16],[10],871⟩) from rfl))
private theorem rec7250 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(4),[4,8,12,16],[10],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[718]? = some (⟨146,(4),[4,8,12,16],[10],609⟩) from rfl))
private theorem rec7253 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(5),[4,8,12,16],[10],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[721]? = some (⟨146,(5),[4,8,12,16],[10],610⟩) from rfl))
private theorem rec7256 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(6),[4,8,12,16],[10],611⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[724]? = some (⟨146,(6),[4,8,12,16],[10],611⟩) from rfl))
private theorem rec7259 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(7),[4,8,12,16],[10],612⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[727]? = some (⟨146,(7),[4,8,12,16],[10],612⟩) from rfl))
private theorem rec7262 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(8),[4,8,12,16],[10],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[730]? = some (⟨146,(8),[4,8,12,16],[10],613⟩) from rfl))
private theorem rec7265 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(9),[4,8,12,16],[10],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[733]? = some (⟨146,(9),[4,8,12,16],[10],614⟩) from rfl))
private theorem rec7268 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(10),[4,8,12,16],[10],615⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[736]? = some (⟨146,(10),[4,8,12,16],[10],615⟩) from rfl))
private theorem rec7271 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(11),[4,8,12,16],[10],616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[739]? = some (⟨146,(11),[4,8,12,16],[10],616⟩) from rfl))
private theorem rec7274 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(12),[4,8,12,16],[10],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[742]? = some (⟨146,(12),[4,8,12,16],[10],617⟩) from rfl))
private theorem rec7277 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(13),[4,8,12,16],[10],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[745]? = some (⟨146,(13),[4,8,12,16],[10],618⟩) from rfl))
private theorem rec7280 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(14),[4,8,12,16],[10],619⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[748]? = some (⟨146,(14),[4,8,12,16],[10],619⟩) from rfl))
private theorem rec7283 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 146 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(15),[4,8,12,16],[10],620⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[751]? = some (⟨146,(15),[4,8,12,16],[10],620⟩) from rfl))
private theorem rec7286 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(0),[4,8,12],[10],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[754]? = some (⟨150,(0),[4,8,12],[10],387⟩) from rfl))
private theorem rec7289 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(1),[4,8,12],[10],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[757]? = some (⟨150,(1),[4,8,12],[10],621⟩) from rfl))
private theorem rec7292 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(2),[4,8,12],[10],622⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[760]? = some (⟨150,(2),[4,8,12],[10],622⟩) from rfl))
private theorem rec7295 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(3),[4,8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[763]? = some (⟨150,(3),[4,8,12],[10],101⟩) from rfl))
private theorem rec7298 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(4),[4,8,12],[10],622⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[766]? = some (⟨150,(4),[4,8,12],[10],622⟩) from rfl))
private theorem rec7301 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(5),[4,8,12],[10],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[769]? = some (⟨150,(5),[4,8,12],[10],387⟩) from rfl))
private theorem rec7304 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(6),[4,8,12],[10],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[772]? = some (⟨150,(6),[4,8,12],[10],621⟩) from rfl))
private theorem rec7307 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(7),[4,8,12],[10],623⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[775]? = some (⟨150,(7),[4,8,12],[10],623⟩) from rfl))
private theorem rec7310 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(8),[4,8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[778]? = some (⟨150,(8),[4,8,12],[10],101⟩) from rfl))
private theorem rec7313 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(9),[4,8,12],[10],623⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[781]? = some (⟨150,(9),[4,8,12],[10],623⟩) from rfl))
private theorem rec7316 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(10),[4,8,12],[10],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[784]? = some (⟨150,(10),[4,8,12],[10],387⟩) from rfl))
private theorem rec7319 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(11),[4,8,12],[10],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[787]? = some (⟨150,(11),[4,8,12],[10],621⟩) from rfl))
private theorem rec7322 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(12),[4,8,12],[10],624⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[790]? = some (⟨150,(12),[4,8,12],[10],624⟩) from rfl))
private theorem rec7325 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(13),[4,8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[793]? = some (⟨150,(13),[4,8,12],[10],101⟩) from rfl))
private theorem rec7328 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(14),[4,8,12],[10],624⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[796]? = some (⟨150,(14),[4,8,12],[10],624⟩) from rfl))
private theorem rec7331 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(15),[4,8,12],[10],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[799]? = some (⟨150,(15),[4,8,12],[10],625⟩) from rfl))
private theorem rec7334 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(16),[4,8,12],[10],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[802]? = some (⟨150,(16),[4,8,12],[10],626⟩) from rfl))
private theorem rec7337 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(17),[4,8,12],[10],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[805]? = some (⟨150,(17),[4,8,12],[10],286⟩) from rfl))
private theorem rec7340 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(18),[4,8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[808]? = some (⟨150,(18),[4,8,12],[10],101⟩) from rfl))
private theorem rec7343 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(19),[4,8,12],[10],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[811]? = some (⟨150,(19),[4,8,12],[10],286⟩) from rfl))
private theorem rec7346 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(20),[4,8,12],[10],876⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[814]? = some (⟨150,(20),[4,8,12],[10],876⟩) from rfl))
private theorem rec7349 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(21),[4,8,12],[10],877⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[817]? = some (⟨150,(21),[4,8,12],[10],877⟩) from rfl))
private theorem rec7352 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(22),[4,8,12],[10],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[820]? = some (⟨150,(22),[4,8,12],[10],287⟩) from rfl))
private theorem rec7355 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(23),[4,8,12],[10],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[823]? = some (⟨150,(23),[4,8,12],[10],101⟩) from rfl))
private theorem rec7358 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 150 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(24),[4,8,12],[10],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[826]? = some (⟨150,(24),[4,8,12],[10],287⟩) from rfl))
private theorem rec16164 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(0),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1243]? = some (⟨517,(0),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16165 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(1),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1244]? = some (⟨517,(1),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16166 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(2),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1245]? = some (⟨517,(2),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16167 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(3),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1246]? = some (⟨517,(3),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16168 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(4),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1247]? = some (⟨517,(4),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16169 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(5),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1248]? = some (⟨517,(5),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16170 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(6),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1249]? = some (⟨517,(6),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16171 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(7),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1250]? = some (⟨517,(7),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16172 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(8),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1251]? = some (⟨517,(8),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16173 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 517 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨517,(9),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1252]? = some (⟨517,(9),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16415 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(0),[12],[10],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[207]? = some (⟨562,(0),[12],[10],1649⟩) from rfl))
private theorem rec16417 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(1),[12],[10],1666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[209]? = some (⟨562,(1),[12],[10],1666⟩) from rfl))
private theorem rec16419 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(2),[12],[10],1667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[211]? = some (⟨562,(2),[12],[10],1667⟩) from rfl))
private theorem rec16421 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(3),[12],[10],1668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[213]? = some (⟨562,(3),[12],[10],1668⟩) from rfl))
private theorem rec16423 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(4),[12],[10],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[215]? = some (⟨562,(4),[12],[10],396⟩) from rfl))
private theorem rec16425 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(5),[12],[10],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[217]? = some (⟨562,(5),[12],[10],1649⟩) from rfl))
private theorem rec16427 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(6),[12],[10],1666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[219]? = some (⟨562,(6),[12],[10],1666⟩) from rfl))
private theorem rec16429 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(7),[12],[10],1667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[221]? = some (⟨562,(7),[12],[10],1667⟩) from rfl))
private theorem rec16431 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(8),[12],[10],1668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[223]? = some (⟨562,(8),[12],[10],1668⟩) from rfl))
private theorem rec16433 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 562 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(9),[12],[10],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[225]? = some (⟨562,(9),[12],[10],396⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 12).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 12)).drop 0).take 16, section14Recorded section14Catalog 12 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 12 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 12).plans.drop 4).take 1 = [⟨5,82,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(622,⟨([1],[]),true,([1],[]),false,false,[]⟩),(517,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(518,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(562,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(563,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(88,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(89,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(90,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(91,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(92,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(93,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(94,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(95,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(96,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(97,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(98,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(99,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(100,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(101,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(102,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(103,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(104,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(105,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(106,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(107,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(108,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(109,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(110,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(111,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(112,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(113,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(114,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(115,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(116,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(117,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(118,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(119,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(120,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(121,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(122,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(123,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(124,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(125,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(126,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(127,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(128,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(129,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(130,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(131,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(132,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(623,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(134,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(135,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(136,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(137,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(138,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(139,⟨([3,2],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(140,⟨([3,1,1],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(141,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(142,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(143,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(144,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(145,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(146,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(624,⟨([1],[]),true,([],[]),true,false,[]⟩),(152,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec5576 12 0 (by decide) (by decide)
  · left
    exact rec5592 12 1 (by decide) (by decide)
  · left
    exact rec5594 12 2 (by decide) (by decide)
  · left
    exact rec5601 12 3 (by decide) (by decide)
  · left
    exact rec5576 12 4 (by decide) (by decide)
  · left
    exact rec5583 12 5 (by decide) (by decide)
  · left
    exact rec5596 12 6 (by decide) (by decide)
  · left
    exact rec5595 12 7 (by decide) (by decide)
  · left
    exact rec5591 12 8 (by decide) (by decide)
  · left
    exact rec5593 12 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(622,⟨([1],[]),true,([1],[]),false,false,[]⟩),(517,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(518,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(562,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(563,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(88,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(89,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(90,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(91,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(92,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(93,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(94,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(95,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(96,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(97,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(98,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(99,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(100,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(101,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(102,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(103,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(104,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(105,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(106,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(107,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(108,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(109,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(110,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(111,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(112,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(113,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(114,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(115,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(116,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(117,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(118,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(119,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(120,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(121,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(122,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(123,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(124,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(125,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(126,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(127,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(128,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(129,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(130,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(131,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(132,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(623,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(134,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(135,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(136,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(137,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(138,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(139,⟨([3,2],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(140,⟨([3,1,1],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(141,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(142,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(143,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(144,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(145,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(146,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(624,⟨([1],[]),true,([],[]),true,false,[]⟩),(152,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 622)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 517)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16164 12 10 (by decide) (by decide)
      · right
        exact rec16165 12 10 (by decide) (by decide)
      · right
        exact rec16166 12 10 (by decide) (by decide)
      · right
        exact rec16167 12 10 (by decide) (by decide)
      · right
        exact rec16168 12 10 (by decide) (by decide)
      · right
        exact rec16169 12 10 (by decide) (by decide)
      · right
        exact rec16170 12 10 (by decide) (by decide)
      · right
        exact rec16171 12 10 (by decide) (by decide)
      · right
        exact rec16172 12 10 (by decide) (by decide)
      · right
        exact rec16173 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 518)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 562)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16415 12 10 (by decide) (by decide)
      · right
        exact rec16417 12 10 (by decide) (by decide)
      · right
        exact rec16419 12 10 (by decide) (by decide)
      · right
        exact rec16421 12 10 (by decide) (by decide)
      · right
        exact rec16423 12 10 (by decide) (by decide)
      · right
        exact rec16425 12 10 (by decide) (by decide)
      · right
        exact rec16427 12 10 (by decide) (by decide)
      · right
        exact rec16429 12 10 (by decide) (by decide)
      · right
        exact rec16431 12 10 (by decide) (by decide)
      · right
        exact rec16433 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 563)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 88)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 89)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5719 12 10 (by decide) (by decide)
      · right
        exact rec5722 12 10 (by decide) (by decide)
      · right
        exact rec5725 12 10 (by decide) (by decide)
      · right
        exact rec5728 12 10 (by decide) (by decide)
      · right
        exact rec5731 12 10 (by decide) (by decide)
      · right
        exact rec5734 12 10 (by decide) (by decide)
      · right
        exact rec5737 12 10 (by decide) (by decide)
      · right
        exact rec5740 12 10 (by decide) (by decide)
      · right
        exact rec5743 12 10 (by decide) (by decide)
      · right
        exact rec5746 12 10 (by decide) (by decide)
      · right
        exact rec5749 12 10 (by decide) (by decide)
      · right
        exact rec5752 12 10 (by decide) (by decide)
      · right
        exact rec5755 12 10 (by decide) (by decide)
      · right
        exact rec5758 12 10 (by decide) (by decide)
      · right
        exact rec5761 12 10 (by decide) (by decide)
      · right
        exact rec5764 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 90)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 91)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 92)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5767 12 10 (by decide) (by decide)
      · right
        exact rec5770 12 10 (by decide) (by decide)
      · right
        exact rec5773 12 10 (by decide) (by decide)
      · right
        exact rec5776 12 10 (by decide) (by decide)
      · right
        exact rec5779 12 10 (by decide) (by decide)
      · right
        exact rec5782 12 10 (by decide) (by decide)
      · right
        exact rec5785 12 10 (by decide) (by decide)
      · right
        exact rec5788 12 10 (by decide) (by decide)
      · right
        exact rec5791 12 10 (by decide) (by decide)
      · right
        exact rec5794 12 10 (by decide) (by decide)
      · right
        exact rec5797 12 10 (by decide) (by decide)
      · right
        exact rec5800 12 10 (by decide) (by decide)
      · right
        exact rec5803 12 10 (by decide) (by decide)
      · right
        exact rec5806 12 10 (by decide) (by decide)
      · right
        exact rec5809 12 10 (by decide) (by decide)
      · right
        exact rec5812 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 93)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 94)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 95)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5815 12 10 (by decide) (by decide)
      · right
        exact rec5818 12 10 (by decide) (by decide)
      · right
        exact rec5821 12 10 (by decide) (by decide)
      · right
        exact rec5824 12 10 (by decide) (by decide)
      · right
        exact rec5827 12 10 (by decide) (by decide)
      · right
        exact rec5830 12 10 (by decide) (by decide)
      · right
        exact rec5833 12 10 (by decide) (by decide)
      · right
        exact rec5836 12 10 (by decide) (by decide)
      · right
        exact rec5839 12 10 (by decide) (by decide)
      · right
        exact rec5842 12 10 (by decide) (by decide)
      · right
        exact rec5845 12 10 (by decide) (by decide)
      · right
        exact rec5848 12 10 (by decide) (by decide)
      · right
        exact rec5851 12 10 (by decide) (by decide)
      · right
        exact rec5854 12 10 (by decide) (by decide)
      · right
        exact rec5857 12 10 (by decide) (by decide)
      · right
        exact rec5860 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 96)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5863 12 10 (by decide) (by decide)
      · right
        exact rec5866 12 10 (by decide) (by decide)
      · right
        exact rec5869 12 10 (by decide) (by decide)
      · right
        exact rec5872 12 10 (by decide) (by decide)
      · right
        exact rec5875 12 10 (by decide) (by decide)
      · right
        exact rec5878 12 10 (by decide) (by decide)
      · right
        exact rec5881 12 10 (by decide) (by decide)
      · right
        exact rec5884 12 10 (by decide) (by decide)
      · right
        exact rec5887 12 10 (by decide) (by decide)
      · right
        exact rec5890 12 10 (by decide) (by decide)
      · right
        exact rec5893 12 10 (by decide) (by decide)
      · right
        exact rec5896 12 10 (by decide) (by decide)
      · right
        exact rec5899 12 10 (by decide) (by decide)
      · right
        exact rec5902 12 10 (by decide) (by decide)
      · right
        exact rec5905 12 10 (by decide) (by decide)
      · right
        exact rec5908 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 97)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 98)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 99)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 100)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5911 12 10 (by decide) (by decide)
      · right
        exact rec5914 12 10 (by decide) (by decide)
      · right
        exact rec5917 12 10 (by decide) (by decide)
      · right
        exact rec5920 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 101)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5923 12 10 (by decide) (by decide)
      · right
        exact rec5926 12 10 (by decide) (by decide)
      · right
        exact rec5929 12 10 (by decide) (by decide)
      · right
        exact rec5932 12 10 (by decide) (by decide)
      · right
        exact rec5935 12 10 (by decide) (by decide)
      · right
        exact rec5938 12 10 (by decide) (by decide)
      · right
        exact rec5941 12 10 (by decide) (by decide)
      · right
        exact rec5944 12 10 (by decide) (by decide)
      · right
        exact rec5947 12 10 (by decide) (by decide)
      · right
        exact rec5950 12 10 (by decide) (by decide)
      · right
        exact rec5953 12 10 (by decide) (by decide)
      · right
        exact rec5956 12 10 (by decide) (by decide)
      · right
        exact rec5959 12 10 (by decide) (by decide)
      · right
        exact rec5962 12 10 (by decide) (by decide)
      · right
        exact rec5965 12 10 (by decide) (by decide)
      · right
        exact rec5968 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 102)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 103)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 104)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5971 12 10 (by decide) (by decide)
      · right
        exact rec5974 12 10 (by decide) (by decide)
      · right
        exact rec5977 12 10 (by decide) (by decide)
      · right
        exact rec5980 12 10 (by decide) (by decide)
      · right
        exact rec5983 12 10 (by decide) (by decide)
      · right
        exact rec5986 12 10 (by decide) (by decide)
      · right
        exact rec5989 12 10 (by decide) (by decide)
      · right
        exact rec5992 12 10 (by decide) (by decide)
      · right
        exact rec5995 12 10 (by decide) (by decide)
      · right
        exact rec5998 12 10 (by decide) (by decide)
      · right
        exact rec6001 12 10 (by decide) (by decide)
      · right
        exact rec6004 12 10 (by decide) (by decide)
      · right
        exact rec6007 12 10 (by decide) (by decide)
      · right
        exact rec6010 12 10 (by decide) (by decide)
      · right
        exact rec6013 12 10 (by decide) (by decide)
      · right
        exact rec6016 12 10 (by decide) (by decide)
      · right
        exact rec6019 12 10 (by decide) (by decide)
      · right
        exact rec6022 12 10 (by decide) (by decide)
      · right
        exact rec6025 12 10 (by decide) (by decide)
      · right
        exact rec6028 12 10 (by decide) (by decide)
      · right
        exact rec6031 12 10 (by decide) (by decide)
      · right
        exact rec6034 12 10 (by decide) (by decide)
      · right
        exact rec6037 12 10 (by decide) (by decide)
      · right
        exact rec6040 12 10 (by decide) (by decide)
      · right
        exact rec6043 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 105)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 106)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6046 12 10 (by decide) (by decide)
      · right
        exact rec6049 12 10 (by decide) (by decide)
      · right
        exact rec6052 12 10 (by decide) (by decide)
      · right
        exact rec6055 12 10 (by decide) (by decide)
      · right
        exact rec6058 12 10 (by decide) (by decide)
      · right
        exact rec6061 12 10 (by decide) (by decide)
      · right
        exact rec6064 12 10 (by decide) (by decide)
      · right
        exact rec6067 12 10 (by decide) (by decide)
      · right
        exact rec6070 12 10 (by decide) (by decide)
      · right
        exact rec6073 12 10 (by decide) (by decide)
      · right
        exact rec6076 12 10 (by decide) (by decide)
      · right
        exact rec6079 12 10 (by decide) (by decide)
      · right
        exact rec6082 12 10 (by decide) (by decide)
      · right
        exact rec6085 12 10 (by decide) (by decide)
      · right
        exact rec6088 12 10 (by decide) (by decide)
      · right
        exact rec6091 12 10 (by decide) (by decide)
      · right
        exact rec6094 12 10 (by decide) (by decide)
      · right
        exact rec6097 12 10 (by decide) (by decide)
      · right
        exact rec6100 12 10 (by decide) (by decide)
      · right
        exact rec6103 12 10 (by decide) (by decide)
      · right
        exact rec6106 12 10 (by decide) (by decide)
      · right
        exact rec6109 12 10 (by decide) (by decide)
      · right
        exact rec6112 12 10 (by decide) (by decide)
      · right
        exact rec6115 12 10 (by decide) (by decide)
      · right
        exact rec6118 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 107)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 108)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 109)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6121 12 10 (by decide) (by decide)
      · right
        exact rec6124 12 10 (by decide) (by decide)
      · right
        exact rec6127 12 10 (by decide) (by decide)
      · right
        exact rec6130 12 10 (by decide) (by decide)
      · right
        exact rec6133 12 10 (by decide) (by decide)
      · right
        exact rec6136 12 10 (by decide) (by decide)
      · right
        exact rec6139 12 10 (by decide) (by decide)
      · right
        exact rec6142 12 10 (by decide) (by decide)
      · right
        exact rec6145 12 10 (by decide) (by decide)
      · right
        exact rec6148 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 110)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 111)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6151 12 10 (by decide) (by decide)
      · right
        exact rec6154 12 10 (by decide) (by decide)
      · right
        exact rec6157 12 10 (by decide) (by decide)
      · right
        exact rec6160 12 10 (by decide) (by decide)
      · right
        exact rec6163 12 10 (by decide) (by decide)
      · right
        exact rec6166 12 10 (by decide) (by decide)
      · right
        exact rec6169 12 10 (by decide) (by decide)
      · right
        exact rec6172 12 10 (by decide) (by decide)
      · right
        exact rec6175 12 10 (by decide) (by decide)
      · right
        exact rec6178 12 10 (by decide) (by decide)
      · right
        exact rec6181 12 10 (by decide) (by decide)
      · right
        exact rec6184 12 10 (by decide) (by decide)
      · right
        exact rec6187 12 10 (by decide) (by decide)
      · right
        exact rec6190 12 10 (by decide) (by decide)
      · right
        exact rec6193 12 10 (by decide) (by decide)
      · right
        exact rec6196 12 10 (by decide) (by decide)
      · right
        exact rec6199 12 10 (by decide) (by decide)
      · right
        exact rec6202 12 10 (by decide) (by decide)
      · right
        exact rec6205 12 10 (by decide) (by decide)
      · right
        exact rec6208 12 10 (by decide) (by decide)
      · right
        exact rec6211 12 10 (by decide) (by decide)
      · right
        exact rec6214 12 10 (by decide) (by decide)
      · right
        exact rec6217 12 10 (by decide) (by decide)
      · right
        exact rec6220 12 10 (by decide) (by decide)
      · right
        exact rec6223 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 112)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 113)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 114)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6226 12 10 (by decide) (by decide)
      · right
        exact rec6229 12 10 (by decide) (by decide)
      · right
        exact rec6232 12 10 (by decide) (by decide)
      · right
        exact rec6235 12 10 (by decide) (by decide)
      · right
        exact rec6238 12 10 (by decide) (by decide)
      · right
        exact rec6241 12 10 (by decide) (by decide)
      · right
        exact rec6244 12 10 (by decide) (by decide)
      · right
        exact rec6247 12 10 (by decide) (by decide)
      · right
        exact rec6250 12 10 (by decide) (by decide)
      · right
        exact rec6253 12 10 (by decide) (by decide)
      · right
        exact rec6256 12 10 (by decide) (by decide)
      · right
        exact rec6259 12 10 (by decide) (by decide)
      · right
        exact rec6262 12 10 (by decide) (by decide)
      · right
        exact rec6265 12 10 (by decide) (by decide)
      · right
        exact rec6268 12 10 (by decide) (by decide)
      · right
        exact rec6271 12 10 (by decide) (by decide)
      · right
        exact rec6274 12 10 (by decide) (by decide)
      · right
        exact rec6277 12 10 (by decide) (by decide)
      · right
        exact rec6280 12 10 (by decide) (by decide)
      · right
        exact rec6283 12 10 (by decide) (by decide)
      · right
        exact rec6286 12 10 (by decide) (by decide)
      · right
        exact rec6289 12 10 (by decide) (by decide)
      · right
        exact rec6292 12 10 (by decide) (by decide)
      · right
        exact rec6295 12 10 (by decide) (by decide)
      · right
        exact rec6298 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 115)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 116)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6301 12 10 (by decide) (by decide)
      · right
        exact rec6304 12 10 (by decide) (by decide)
      · right
        exact rec6307 12 10 (by decide) (by decide)
      · right
        exact rec6310 12 10 (by decide) (by decide)
      · right
        exact rec6313 12 10 (by decide) (by decide)
      · right
        exact rec6316 12 10 (by decide) (by decide)
      · right
        exact rec6319 12 10 (by decide) (by decide)
      · right
        exact rec6322 12 10 (by decide) (by decide)
      · right
        exact rec6325 12 10 (by decide) (by decide)
      · right
        exact rec6328 12 10 (by decide) (by decide)
      · right
        exact rec6331 12 10 (by decide) (by decide)
      · right
        exact rec6334 12 10 (by decide) (by decide)
      · right
        exact rec6337 12 10 (by decide) (by decide)
      · right
        exact rec6340 12 10 (by decide) (by decide)
      · right
        exact rec6343 12 10 (by decide) (by decide)
      · right
        exact rec6346 12 10 (by decide) (by decide)
      · right
        exact rec6349 12 10 (by decide) (by decide)
      · right
        exact rec6352 12 10 (by decide) (by decide)
      · right
        exact rec6355 12 10 (by decide) (by decide)
      · right
        exact rec6358 12 10 (by decide) (by decide)
      · right
        exact rec6361 12 10 (by decide) (by decide)
      · right
        exact rec6364 12 10 (by decide) (by decide)
      · right
        exact rec6367 12 10 (by decide) (by decide)
      · right
        exact rec6370 12 10 (by decide) (by decide)
      · right
        exact rec6373 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 117)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 118)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 119)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6376 12 10 (by decide) (by decide)
      · right
        exact rec6379 12 10 (by decide) (by decide)
      · right
        exact rec6382 12 10 (by decide) (by decide)
      · right
        exact rec6385 12 10 (by decide) (by decide)
      · right
        exact rec6389 12 10 (by decide) (by decide)
      · right
        exact rec6392 12 10 (by decide) (by decide)
      · right
        exact rec6395 12 10 (by decide) (by decide)
      · right
        exact rec6398 12 10 (by decide) (by decide)
      · right
        exact rec6401 12 10 (by decide) (by decide)
      · right
        exact rec6405 12 10 (by decide) (by decide)
      · right
        exact rec6408 12 10 (by decide) (by decide)
      · right
        exact rec6411 12 10 (by decide) (by decide)
      · right
        exact rec6414 12 10 (by decide) (by decide)
      · right
        exact rec6417 12 10 (by decide) (by decide)
      · right
        exact rec6421 12 10 (by decide) (by decide)
      · right
        exact rec6424 12 10 (by decide) (by decide)
      · right
        exact rec6427 12 10 (by decide) (by decide)
      · right
        exact rec6430 12 10 (by decide) (by decide)
      · right
        exact rec6433 12 10 (by decide) (by decide)
      · right
        exact rec6437 12 10 (by decide) (by decide)
      · right
        exact rec6440 12 10 (by decide) (by decide)
      · right
        exact rec6443 12 10 (by decide) (by decide)
      · right
        exact rec6446 12 10 (by decide) (by decide)
      · right
        exact rec6449 12 10 (by decide) (by decide)
      · right
        exact rec6453 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 120)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 121)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6456 12 10 (by decide) (by decide)
      · right
        exact rec6459 12 10 (by decide) (by decide)
      · right
        exact rec6462 12 10 (by decide) (by decide)
      · right
        exact rec6465 12 10 (by decide) (by decide)
      · right
        exact rec6468 12 10 (by decide) (by decide)
      · right
        exact rec6471 12 10 (by decide) (by decide)
      · right
        exact rec6474 12 10 (by decide) (by decide)
      · right
        exact rec6477 12 10 (by decide) (by decide)
      · right
        exact rec6480 12 10 (by decide) (by decide)
      · right
        exact rec6483 12 10 (by decide) (by decide)
      · right
        exact rec6486 12 10 (by decide) (by decide)
      · right
        exact rec6489 12 10 (by decide) (by decide)
      · right
        exact rec6492 12 10 (by decide) (by decide)
      · right
        exact rec6495 12 10 (by decide) (by decide)
      · right
        exact rec6498 12 10 (by decide) (by decide)
      · right
        exact rec6501 12 10 (by decide) (by decide)
      · right
        exact rec6504 12 10 (by decide) (by decide)
      · right
        exact rec6507 12 10 (by decide) (by decide)
      · right
        exact rec6510 12 10 (by decide) (by decide)
      · right
        exact rec6513 12 10 (by decide) (by decide)
      · right
        exact rec6516 12 10 (by decide) (by decide)
      · right
        exact rec6519 12 10 (by decide) (by decide)
      · right
        exact rec6522 12 10 (by decide) (by decide)
      · right
        exact rec6525 12 10 (by decide) (by decide)
      · right
        exact rec6528 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 122)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 123)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 124)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6531 12 10 (by decide) (by decide)
      · right
        exact rec6534 12 10 (by decide) (by decide)
      · right
        exact rec6537 12 10 (by decide) (by decide)
      · right
        exact rec6540 12 10 (by decide) (by decide)
      · right
        exact rec6543 12 10 (by decide) (by decide)
      · right
        exact rec6546 12 10 (by decide) (by decide)
      · right
        exact rec6549 12 10 (by decide) (by decide)
      · right
        exact rec6552 12 10 (by decide) (by decide)
      · right
        exact rec6555 12 10 (by decide) (by decide)
      · right
        exact rec6558 12 10 (by decide) (by decide)
      · right
        exact rec6561 12 10 (by decide) (by decide)
      · right
        exact rec6564 12 10 (by decide) (by decide)
      · right
        exact rec6567 12 10 (by decide) (by decide)
      · right
        exact rec6570 12 10 (by decide) (by decide)
      · right
        exact rec6573 12 10 (by decide) (by decide)
      · right
        exact rec6576 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 125)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 126)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 127)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6579 12 10 (by decide) (by decide)
      · right
        exact rec6582 12 10 (by decide) (by decide)
      · right
        exact rec6585 12 10 (by decide) (by decide)
      · right
        exact rec6588 12 10 (by decide) (by decide)
      · right
        exact rec6591 12 10 (by decide) (by decide)
      · right
        exact rec6594 12 10 (by decide) (by decide)
      · right
        exact rec6597 12 10 (by decide) (by decide)
      · right
        exact rec6600 12 10 (by decide) (by decide)
      · right
        exact rec6603 12 10 (by decide) (by decide)
      · right
        exact rec6606 12 10 (by decide) (by decide)
      · right
        exact rec6609 12 10 (by decide) (by decide)
      · right
        exact rec6612 12 10 (by decide) (by decide)
      · right
        exact rec6615 12 10 (by decide) (by decide)
      · right
        exact rec6618 12 10 (by decide) (by decide)
      · right
        exact rec6621 12 10 (by decide) (by decide)
      · right
        exact rec6624 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 128)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 129)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6627 12 10 (by decide) (by decide)
      · right
        exact rec6630 12 10 (by decide) (by decide)
      · right
        exact rec6633 12 10 (by decide) (by decide)
      · right
        exact rec6636 12 10 (by decide) (by decide)
      · right
        exact rec6639 12 10 (by decide) (by decide)
      · right
        exact rec6642 12 10 (by decide) (by decide)
      · right
        exact rec6645 12 10 (by decide) (by decide)
      · right
        exact rec6648 12 10 (by decide) (by decide)
      · right
        exact rec6651 12 10 (by decide) (by decide)
      · right
        exact rec6654 12 10 (by decide) (by decide)
      · right
        exact rec6657 12 10 (by decide) (by decide)
      · right
        exact rec6660 12 10 (by decide) (by decide)
      · right
        exact rec6663 12 10 (by decide) (by decide)
      · right
        exact rec6666 12 10 (by decide) (by decide)
      · right
        exact rec6669 12 10 (by decide) (by decide)
      · right
        exact rec6672 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 130)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 131)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 132)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6675 12 10 (by decide) (by decide)
      · right
        exact rec6678 12 10 (by decide) (by decide)
      · right
        exact rec6681 12 10 (by decide) (by decide)
      · right
        exact rec6684 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 623)).length = 5 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 134)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6688 12 10 (by decide) (by decide)
      · right
        exact rec6691 12 10 (by decide) (by decide)
      · right
        exact rec6694 12 10 (by decide) (by decide)
      · right
        exact rec6697 12 10 (by decide) (by decide)
      · right
        exact rec6700 12 10 (by decide) (by decide)
      · right
        exact rec6703 12 10 (by decide) (by decide)
      · right
        exact rec6706 12 10 (by decide) (by decide)
      · right
        exact rec6709 12 10 (by decide) (by decide)
      · right
        exact rec6712 12 10 (by decide) (by decide)
      · right
        exact rec6715 12 10 (by decide) (by decide)
      · right
        exact rec6718 12 10 (by decide) (by decide)
      · right
        exact rec6721 12 10 (by decide) (by decide)
      · right
        exact rec6724 12 10 (by decide) (by decide)
      · right
        exact rec6727 12 10 (by decide) (by decide)
      · right
        exact rec6730 12 10 (by decide) (by decide)
      · right
        exact rec6733 12 10 (by decide) (by decide)
      · right
        exact rec6736 12 10 (by decide) (by decide)
      · right
        exact rec6739 12 10 (by decide) (by decide)
      · right
        exact rec6742 12 10 (by decide) (by decide)
      · right
        exact rec6745 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 135)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6748 12 10 (by decide) (by decide)
      · right
        exact rec6751 12 10 (by decide) (by decide)
      · right
        exact rec6754 12 10 (by decide) (by decide)
      · right
        exact rec6757 12 10 (by decide) (by decide)
      · right
        exact rec6760 12 10 (by decide) (by decide)
      · right
        exact rec6763 12 10 (by decide) (by decide)
      · right
        exact rec6766 12 10 (by decide) (by decide)
      · right
        exact rec6769 12 10 (by decide) (by decide)
      · right
        exact rec6772 12 10 (by decide) (by decide)
      · right
        exact rec6775 12 10 (by decide) (by decide)
      · right
        exact rec6778 12 10 (by decide) (by decide)
      · right
        exact rec6781 12 10 (by decide) (by decide)
      · right
        exact rec6784 12 10 (by decide) (by decide)
      · right
        exact rec6787 12 10 (by decide) (by decide)
      · right
        exact rec6790 12 10 (by decide) (by decide)
      · right
        exact rec6793 12 10 (by decide) (by decide)
      · right
        exact rec6796 12 10 (by decide) (by decide)
      · right
        exact rec6799 12 10 (by decide) (by decide)
      · right
        exact rec6805 12 10 (by decide) (by decide)
      · right
        exact rec6807 12 10 (by decide) (by decide)
      · right
        exact rec6810 12 10 (by decide) (by decide)
      · right
        exact rec6813 12 10 (by decide) (by decide)
      · right
        exact rec6816 12 10 (by decide) (by decide)
      · right
        exact rec6819 12 10 (by decide) (by decide)
      · right
        exact rec6823 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 136)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6827 12 10 (by decide) (by decide)
      · right
        exact rec6831 12 10 (by decide) (by decide)
      · right
        exact rec6834 12 10 (by decide) (by decide)
      · right
        exact rec6837 12 10 (by decide) (by decide)
      · right
        exact rec6840 12 10 (by decide) (by decide)
      · right
        exact rec6843 12 10 (by decide) (by decide)
      · right
        exact rec6846 12 10 (by decide) (by decide)
      · right
        exact rec6850 12 10 (by decide) (by decide)
      · right
        exact rec6853 12 10 (by decide) (by decide)
      · right
        exact rec6856 12 10 (by decide) (by decide)
      · right
        exact rec6859 12 10 (by decide) (by decide)
      · right
        exact rec6862 12 10 (by decide) (by decide)
      · right
        exact rec6865 12 10 (by decide) (by decide)
      · right
        exact rec6868 12 10 (by decide) (by decide)
      · right
        exact rec6871 12 10 (by decide) (by decide)
      · right
        exact rec6874 12 10 (by decide) (by decide)
      · right
        exact rec6877 12 10 (by decide) (by decide)
      · right
        exact rec6880 12 10 (by decide) (by decide)
      · right
        exact rec6883 12 10 (by decide) (by decide)
      · right
        exact rec6886 12 10 (by decide) (by decide)
      · right
        exact rec6889 12 10 (by decide) (by decide)
      · right
        exact rec6892 12 10 (by decide) (by decide)
      · right
        exact rec6895 12 10 (by decide) (by decide)
      · right
        exact rec6898 12 10 (by decide) (by decide)
      · right
        exact rec6902 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 137)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 138)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6905 12 10 (by decide) (by decide)
      · right
        exact rec6908 12 10 (by decide) (by decide)
      · right
        exact rec6911 12 10 (by decide) (by decide)
      · right
        exact rec6914 12 10 (by decide) (by decide)
      · right
        exact rec6917 12 10 (by decide) (by decide)
      · right
        exact rec6921 12 10 (by decide) (by decide)
      · right
        exact rec6925 12 10 (by decide) (by decide)
      · right
        exact rec6929 12 10 (by decide) (by decide)
      · right
        exact rec6933 12 10 (by decide) (by decide)
      · right
        exact rec6937 12 10 (by decide) (by decide)
      · right
        exact rec6940 12 10 (by decide) (by decide)
      · right
        exact rec6943 12 10 (by decide) (by decide)
      · right
        exact rec6946 12 10 (by decide) (by decide)
      · right
        exact rec6949 12 10 (by decide) (by decide)
      · right
        exact rec6952 12 10 (by decide) (by decide)
      · right
        exact rec6955 12 10 (by decide) (by decide)
      · right
        exact rec6958 12 10 (by decide) (by decide)
      · right
        exact rec6961 12 10 (by decide) (by decide)
      · right
        exact rec6964 12 10 (by decide) (by decide)
      · right
        exact rec6967 12 10 (by decide) (by decide)
      · right
        exact rec6970 12 10 (by decide) (by decide)
      · right
        exact rec6973 12 10 (by decide) (by decide)
      · right
        exact rec6976 12 10 (by decide) (by decide)
      · right
        exact rec6979 12 10 (by decide) (by decide)
      · right
        exact rec6982 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 139)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6985 12 10 (by decide) (by decide)
      · right
        exact rec6988 12 10 (by decide) (by decide)
      · right
        exact rec6991 12 10 (by decide) (by decide)
      · right
        exact rec6994 12 10 (by decide) (by decide)
      · right
        exact rec6997 12 10 (by decide) (by decide)
      · right
        exact rec7001 12 10 (by decide) (by decide)
      · right
        exact rec7005 12 10 (by decide) (by decide)
      · right
        exact rec7009 12 10 (by decide) (by decide)
      · right
        exact rec7012 12 10 (by decide) (by decide)
      · right
        exact rec7015 12 10 (by decide) (by decide)
      · right
        exact rec7018 12 10 (by decide) (by decide)
      · right
        exact rec7021 12 10 (by decide) (by decide)
      · right
        exact rec7024 12 10 (by decide) (by decide)
      · right
        exact rec7027 12 10 (by decide) (by decide)
      · right
        exact rec7030 12 10 (by decide) (by decide)
      · right
        exact rec7033 12 10 (by decide) (by decide)
      · right
        exact rec7036 12 10 (by decide) (by decide)
      · right
        exact rec7039 12 10 (by decide) (by decide)
      · right
        exact rec7042 12 10 (by decide) (by decide)
      · right
        exact rec7045 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 140)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7048 12 10 (by decide) (by decide)
      · right
        exact rec7051 12 10 (by decide) (by decide)
      · right
        exact rec7054 12 10 (by decide) (by decide)
      · right
        exact rec7057 12 10 (by decide) (by decide)
      · right
        exact rec7062 12 10 (by decide) (by decide)
      · right
        exact rec7065 12 10 (by decide) (by decide)
      · right
        exact rec7069 12 10 (by decide) (by decide)
      · right
        exact rec7074 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 141)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 142)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7077 12 10 (by decide) (by decide)
      · right
        exact rec7080 12 10 (by decide) (by decide)
      · right
        exact rec7083 12 10 (by decide) (by decide)
      · right
        exact rec7086 12 10 (by decide) (by decide)
      · right
        exact rec7089 12 10 (by decide) (by decide)
      · right
        exact rec7092 12 10 (by decide) (by decide)
      · right
        exact rec7095 12 10 (by decide) (by decide)
      · right
        exact rec7098 12 10 (by decide) (by decide)
      · right
        exact rec7101 12 10 (by decide) (by decide)
      · right
        exact rec7104 12 10 (by decide) (by decide)
      · right
        exact rec7107 12 10 (by decide) (by decide)
      · right
        exact rec7110 12 10 (by decide) (by decide)
      · right
        exact rec7113 12 10 (by decide) (by decide)
      · right
        exact rec7116 12 10 (by decide) (by decide)
      · right
        exact rec7119 12 10 (by decide) (by decide)
      · right
        exact rec7122 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 143)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7125 12 10 (by decide) (by decide)
      · right
        exact rec7128 12 10 (by decide) (by decide)
      · right
        exact rec7131 12 10 (by decide) (by decide)
      · right
        exact rec7134 12 10 (by decide) (by decide)
      · right
        exact rec7137 12 10 (by decide) (by decide)
      · right
        exact rec7140 12 10 (by decide) (by decide)
      · right
        exact rec7143 12 10 (by decide) (by decide)
      · right
        exact rec7146 12 10 (by decide) (by decide)
      · right
        exact rec7149 12 10 (by decide) (by decide)
      · right
        exact rec7152 12 10 (by decide) (by decide)
      · right
        exact rec7155 12 10 (by decide) (by decide)
      · right
        exact rec7158 12 10 (by decide) (by decide)
      · right
        exact rec7161 12 10 (by decide) (by decide)
      · right
        exact rec7164 12 10 (by decide) (by decide)
      · right
        exact rec7167 12 10 (by decide) (by decide)
      · right
        exact rec7170 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 144)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7173 12 10 (by decide) (by decide)
      · right
        exact rec7176 12 10 (by decide) (by decide)
      · right
        exact rec7179 12 10 (by decide) (by decide)
      · right
        exact rec7182 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 145)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7185 12 10 (by decide) (by decide)
      · right
        exact rec7190 12 10 (by decide) (by decide)
      · right
        exact rec7192 12 10 (by decide) (by decide)
      · right
        exact rec7195 12 10 (by decide) (by decide)
      · right
        exact rec7199 12 10 (by decide) (by decide)
      · right
        exact rec7202 12 10 (by decide) (by decide)
      · right
        exact rec7205 12 10 (by decide) (by decide)
      · right
        exact rec7208 12 10 (by decide) (by decide)
      · right
        exact rec7211 12 10 (by decide) (by decide)
      · right
        exact rec7214 12 10 (by decide) (by decide)
      · right
        exact rec7217 12 10 (by decide) (by decide)
      · right
        exact rec7220 12 10 (by decide) (by decide)
      · right
        exact rec7223 12 10 (by decide) (by decide)
      · right
        exact rec7226 12 10 (by decide) (by decide)
      · right
        exact rec7229 12 10 (by decide) (by decide)
      · right
        exact rec7232 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 146)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7235 12 10 (by decide) (by decide)
      · right
        exact rec7239 12 10 (by decide) (by decide)
      · right
        exact rec7243 12 10 (by decide) (by decide)
      · right
        exact rec7246 12 10 (by decide) (by decide)
      · right
        exact rec7250 12 10 (by decide) (by decide)
      · right
        exact rec7253 12 10 (by decide) (by decide)
      · right
        exact rec7256 12 10 (by decide) (by decide)
      · right
        exact rec7259 12 10 (by decide) (by decide)
      · right
        exact rec7262 12 10 (by decide) (by decide)
      · right
        exact rec7265 12 10 (by decide) (by decide)
      · right
        exact rec7268 12 10 (by decide) (by decide)
      · right
        exact rec7271 12 10 (by decide) (by decide)
      · right
        exact rec7274 12 10 (by decide) (by decide)
      · right
        exact rec7277 12 10 (by decide) (by decide)
      · right
        exact rec7280 12 10 (by decide) (by decide)
      · right
        exact rec7283 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 147)).length = 20 := by decide +kernel
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
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 148)).length = 20 := by decide +kernel
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
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 149)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 150)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7286 12 10 (by decide) (by decide)
      · right
        exact rec7289 12 10 (by decide) (by decide)
      · right
        exact rec7292 12 10 (by decide) (by decide)
      · right
        exact rec7295 12 10 (by decide) (by decide)
      · right
        exact rec7298 12 10 (by decide) (by decide)
      · right
        exact rec7301 12 10 (by decide) (by decide)
      · right
        exact rec7304 12 10 (by decide) (by decide)
      · right
        exact rec7307 12 10 (by decide) (by decide)
      · right
        exact rec7310 12 10 (by decide) (by decide)
      · right
        exact rec7313 12 10 (by decide) (by decide)
      · right
        exact rec7316 12 10 (by decide) (by decide)
      · right
        exact rec7319 12 10 (by decide) (by decide)
      · right
        exact rec7322 12 10 (by decide) (by decide)
      · right
        exact rec7325 12 10 (by decide) (by decide)
      · right
        exact rec7328 12 10 (by decide) (by decide)
      · right
        exact rec7331 12 10 (by decide) (by decide)
      · right
        exact rec7334 12 10 (by decide) (by decide)
      · right
        exact rec7337 12 10 (by decide) (by decide)
      · right
        exact rec7340 12 10 (by decide) (by decide)
      · right
        exact rec7343 12 10 (by decide) (by decide)
      · right
        exact rec7346 12 10 (by decide) (by decide)
      · right
        exact rec7349 12 10 (by decide) (by decide)
      · right
        exact rec7352 12 10 (by decide) (by decide)
      · right
        exact rec7355 12 10 (by decide) (by decide)
      · right
        exact rec7358 12 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 624)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 152)).length = 10 := by decide +kernel
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
    exact rec5595 12 11 (by decide) (by decide)
  · left
    exact rec5591 12 12 (by decide) (by decide)
  · left
    exact rec5593 12 13 (by decide) (by decide)
  · left
    exact rec5597 12 14 (by decide) (by decide)
  · left
    exact rec5595 12 15 (by decide) (by decide)
end Section14Coverage_12_4_p0_16

#print axioms solution
