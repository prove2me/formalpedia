-- Prove2me | solution 1 for Freiman.section14_s0016_coverage0006_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T22:24:19.150462+00:00
-- url     : https://prove2.me/submissions/4ce98f8f-5cb0-48af-8ee4-e49dd65d2aa6

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
namespace Section14Coverage_16_6_p0_16
private theorem rec12950 (si parent : ℕ) (hs : si ∈ ([2, 4, 6, 8, 10, 14, 16] : List ℕ)) (hp : parent ∈ ([0, 4] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[2,4,6,8,10,14,16],[0,4],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[502]? = some (⟨245,(-1),[2,4,6,8,10,14,16],[0,4],882⟩) from rfl))
private theorem rec12955 (si parent : ℕ) (hs : si ∈ ([4, 8, 10, 16] : List ℕ)) (hp : parent ∈ ([8, 12] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[4,8,10,16],[8,12],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[507]? = some (⟨245,(-1),[4,8,10,16],[8,12],882⟩) from rfl))
private theorem rec12956 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([1, 5, 9, 13] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[4,8,16],[1,5,9,13],883⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[508]? = some (⟨245,(-1),[4,8,16],[1,5,9,13],883⟩) from rfl))
private theorem rec12957 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[4,8,16],[2],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[509]? = some (⟨245,(-1),[4,8,16],[2],884⟩) from rfl))
private theorem rec12958 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([7, 11, 15] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[4,8,16],[7,11,15],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[510]? = some (⟨245,(-1),[4,8,16],[7,11,15],886⟩) from rfl))
private theorem rec12959 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[4,8,16],[6],887⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[511]? = some (⟨245,(-1),[4,8,16],[6],887⟩) from rfl))
private theorem rec12960 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[4,16],[3],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[512]? = some (⟨245,(-1),[4,16],[3],884⟩) from rfl))
private theorem rec12961 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[4,16],[14],909⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[513]? = some (⟨245,(-1),[4,16],[14],909⟩) from rfl))
private theorem rec13038 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(0),[4,8,16],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[590]? = some (⟨249,(0),[4,8,16],[10],10⟩) from rfl))
private theorem rec13041 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(1),[4,8,16],[10],11⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[593]? = some (⟨249,(1),[4,8,16],[10],11⟩) from rfl))
private theorem rec13043 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(2),[4,8,16],[10],888⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[595]? = some (⟨249,(2),[4,8,16],[10],888⟩) from rfl))
private theorem rec13045 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(3),[4,8,16],[10],889⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[597]? = some (⟨249,(3),[4,8,16],[10],889⟩) from rfl))
private theorem rec13047 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(4),[4,8,16],[10],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[599]? = some (⟨249,(4),[4,8,16],[10],890⟩) from rfl))
private theorem rec13049 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(5),[4,8,16],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[601]? = some (⟨249,(5),[4,8,16],[10],10⟩) from rfl))
private theorem rec13052 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(6),[4,8,16],[10],11⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[604]? = some (⟨249,(6),[4,8,16],[10],11⟩) from rfl))
private theorem rec13054 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(7),[4,8,16],[10],888⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[606]? = some (⟨249,(7),[4,8,16],[10],888⟩) from rfl))
private theorem rec13056 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(8),[4,8,16],[10],889⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[608]? = some (⟨249,(8),[4,8,16],[10],889⟩) from rfl))
private theorem rec13058 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(9),[4,8,16],[10],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[610]? = some (⟨249,(9),[4,8,16],[10],890⟩) from rfl))
private theorem rec13060 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(10),[4,8,16],[10],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[612]? = some (⟨249,(10),[4,8,16],[10],18⟩) from rfl))
private theorem rec13063 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(11),[4,8,16],[10],19⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[615]? = some (⟨249,(11),[4,8,16],[10],19⟩) from rfl))
private theorem rec13065 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(12),[4,8,16],[10],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[617]? = some (⟨249,(12),[4,8,16],[10],891⟩) from rfl))
private theorem rec13067 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(13),[4,8,16],[10],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[619]? = some (⟨249,(13),[4,8,16],[10],891⟩) from rfl))
private theorem rec13069 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(14),[4,8,16],[10],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[621]? = some (⟨249,(14),[4,8,16],[10],890⟩) from rfl))
private theorem rec13071 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(15),[4,8,16],[10],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[623]? = some (⟨249,(15),[4,8,16],[10],21⟩) from rfl))
private theorem rec13074 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(16),[4,8,16],[10],22⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[626]? = some (⟨249,(16),[4,8,16],[10],22⟩) from rfl))
private theorem rec13076 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(17),[4,8,16],[10],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[628]? = some (⟨249,(17),[4,8,16],[10],892⟩) from rfl))
private theorem rec13078 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(18),[4,8,16],[10],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[630]? = some (⟨249,(18),[4,8,16],[10],892⟩) from rfl))
private theorem rec13080 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(19),[4,8,16],[10],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[632]? = some (⟨249,(19),[4,8,16],[10],892⟩) from rfl))
private theorem rec13082 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(20),[4,8,16],[10],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[634]? = some (⟨249,(20),[4,8,16],[10],24⟩) from rfl))
private theorem rec13085 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(21),[4,8,16],[10],25⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[637]? = some (⟨249,(21),[4,8,16],[10],25⟩) from rfl))
private theorem rec13087 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(22),[4,8,16],[10],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[639]? = some (⟨249,(22),[4,8,16],[10],893⟩) from rfl))
private theorem rec13089 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(23),[4,8,16],[10],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[641]? = some (⟨249,(23),[4,8,16],[10],893⟩) from rfl))
private theorem rec13091 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 249 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(24),[4,8,16],[10],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[643]? = some (⟨249,(24),[4,8,16],[10],893⟩) from rfl))
private theorem rec13093 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(0),[4,8,16],[10],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[645]? = some (⟨253,(0),[4,8,16],[10],884⟩) from rfl))
private theorem rec13097 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(1),[4,8,16],[10],894⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[649]? = some (⟨253,(1),[4,8,16],[10],894⟩) from rfl))
private theorem rec13101 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(2),[4,8,16],[10],895⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[653]? = some (⟨253,(2),[4,8,16],[10],895⟩) from rfl))
private theorem rec13105 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(3),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[657]? = some (⟨253,(3),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec13108 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(4),[4,8,12,16],[10],30⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[660]? = some (⟨253,(4),[4,8,12,16],[10],30⟩) from rfl))
private theorem rec13111 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(5),[4,8,16],[10],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[663]? = some (⟨253,(5),[4,8,16],[10],884⟩) from rfl))
private theorem rec13115 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(6),[4,8,16],[10],894⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[667]? = some (⟨253,(6),[4,8,16],[10],894⟩) from rfl))
private theorem rec13119 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(7),[4,16],[10],896⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[671]? = some (⟨253,(7),[4,16],[10],896⟩) from rfl))
private theorem rec13124 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(8),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[676]? = some (⟨253,(8),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec13127 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(9),[4,8,12,16],[10],32⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[679]? = some (⟨253,(9),[4,8,12,16],[10],32⟩) from rfl))
private theorem rec13130 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(10),[4,8,12,16],[10],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[682]? = some (⟨253,(10),[4,8,12,16],[10],84⟩) from rfl))
private theorem rec13133 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(11),[4,8,12,16],[10],897⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[685]? = some (⟨253,(11),[4,8,12,16],[10],897⟩) from rfl))
private theorem rec13136 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(12),[4,8,12,16],[10],898⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[688]? = some (⟨253,(12),[4,8,12,16],[10],898⟩) from rfl))
private theorem rec13139 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(13),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[691]? = some (⟨253,(13),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec13142 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(14),[4,8,12,16],[10],34⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[694]? = some (⟨253,(14),[4,8,12,16],[10],34⟩) from rfl))
private theorem rec13145 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(15),[4,8,12,16],[10],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[697]? = some (⟨253,(15),[4,8,12,16],[10],35⟩) from rfl))
private theorem rec13148 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(16),[4,8,12,16],[10],36⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[700]? = some (⟨253,(16),[4,8,12,16],[10],36⟩) from rfl))
private theorem rec13151 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(17),[4,8,12,16],[10],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[703]? = some (⟨253,(17),[4,8,12,16],[10],37⟩) from rfl))
private theorem rec13154 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(18),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[706]? = some (⟨253,(18),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec13157 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(19),[4,8,12,16],[10],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[709]? = some (⟨253,(19),[4,8,12,16],[10],37⟩) from rfl))
private theorem rec13160 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(20),[4,8,12,16],[10],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[712]? = some (⟨253,(20),[4,8,12,16],[10],38⟩) from rfl))
private theorem rec13163 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(21),[4,8,12,16],[10],39⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[715]? = some (⟨253,(21),[4,8,12,16],[10],39⟩) from rfl))
private theorem rec13166 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(22),[4,8,12,16],[10],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[718]? = some (⟨253,(22),[4,8,12,16],[10],40⟩) from rfl))
private theorem rec13169 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(23),[4,8,12,16],[10],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[721]? = some (⟨253,(23),[4,8,12,16],[10],29⟩) from rfl))
private theorem rec13172 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(24),[4,8,12,16],[10],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[724]? = some (⟨253,(24),[4,8,12,16],[10],40⟩) from rfl))
private theorem rec16184 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(0),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1263]? = some (⟨527,(0),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16185 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(1),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1264]? = some (⟨527,(1),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16186 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(2),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1265]? = some (⟨527,(2),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16187 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(3),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1266]? = some (⟨527,(3),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16188 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(4),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1267]? = some (⟨527,(4),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16189 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(5),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1268]? = some (⟨527,(5),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16190 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(6),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1269]? = some (⟨527,(6),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16191 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(7),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1270]? = some (⟨527,(7),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16192 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(8),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1271]? = some (⟨527,(8),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16193 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 527 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨527,(9),[4,8,12,16],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1272]? = some (⟨527,(9),[4,8,12,16],[10],3⟩) from rfl))
private theorem rec16579 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(0),[16],[10],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[371]? = some (⟨643,(0),[16],[10],1729⟩) from rfl))
private theorem rec16581 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(1),[16],[10],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[373]? = some (⟨643,(1),[16],[10],1729⟩) from rfl))
private theorem rec16583 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(2),[16],[10],1730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[375]? = some (⟨643,(2),[16],[10],1730⟩) from rfl))
private theorem rec16585 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(3),[16],[10],1730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[377]? = some (⟨643,(3),[16],[10],1730⟩) from rfl))
private theorem rec16587 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(4),[16],[10],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[379]? = some (⟨643,(4),[16],[10],1729⟩) from rfl))
private theorem rec16589 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(5),[16],[10],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[381]? = some (⟨643,(5),[16],[10],1729⟩) from rfl))
private theorem rec16591 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(6),[16],[10],1731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[383]? = some (⟨643,(6),[16],[10],1731⟩) from rfl))
private theorem rec16593 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(7),[16],[10],1731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[385]? = some (⟨643,(7),[16],[10],1731⟩) from rfl))
private theorem rec16595 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(8),[16],[10],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[387]? = some (⟨643,(8),[16],[10],905⟩) from rfl))
private theorem rec16597 (si parent : ℕ) (hs : si ∈ ([16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 643 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(9),[16],[10],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[389]? = some (⟨643,(9),[16],[10],905⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 16).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 16)).drop 0).take 16, section14Recorded section14Catalog 16 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 16 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 16).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(526,⟨([1],[]),true,([1],[]),false,false,[]⟩),(527,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(528,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(654,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(530,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec12950 16 0 (by decide) (by decide)
  · left
    exact rec12956 16 1 (by decide) (by decide)
  · left
    exact rec12957 16 2 (by decide) (by decide)
  · left
    exact rec12960 16 3 (by decide) (by decide)
  · left
    exact rec12950 16 4 (by decide) (by decide)
  · left
    exact rec12956 16 5 (by decide) (by decide)
  · left
    exact rec12959 16 6 (by decide) (by decide)
  · left
    exact rec12958 16 7 (by decide) (by decide)
  · left
    exact rec12955 16 8 (by decide) (by decide)
  · left
    exact rec12956 16 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(526,⟨([1],[]),true,([1],[]),false,false,[]⟩),(527,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(528,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(654,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(530,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 526)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 527)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16184 16 10 (by decide) (by decide)
      · right
        exact rec16185 16 10 (by decide) (by decide)
      · right
        exact rec16186 16 10 (by decide) (by decide)
      · right
        exact rec16187 16 10 (by decide) (by decide)
      · right
        exact rec16188 16 10 (by decide) (by decide)
      · right
        exact rec16189 16 10 (by decide) (by decide)
      · right
        exact rec16190 16 10 (by decide) (by decide)
      · right
        exact rec16191 16 10 (by decide) (by decide)
      · right
        exact rec16192 16 10 (by decide) (by decide)
      · right
        exact rec16193 16 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 528)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 249)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13038 16 10 (by decide) (by decide)
      · right
        exact rec13041 16 10 (by decide) (by decide)
      · right
        exact rec13043 16 10 (by decide) (by decide)
      · right
        exact rec13045 16 10 (by decide) (by decide)
      · right
        exact rec13047 16 10 (by decide) (by decide)
      · right
        exact rec13049 16 10 (by decide) (by decide)
      · right
        exact rec13052 16 10 (by decide) (by decide)
      · right
        exact rec13054 16 10 (by decide) (by decide)
      · right
        exact rec13056 16 10 (by decide) (by decide)
      · right
        exact rec13058 16 10 (by decide) (by decide)
      · right
        exact rec13060 16 10 (by decide) (by decide)
      · right
        exact rec13063 16 10 (by decide) (by decide)
      · right
        exact rec13065 16 10 (by decide) (by decide)
      · right
        exact rec13067 16 10 (by decide) (by decide)
      · right
        exact rec13069 16 10 (by decide) (by decide)
      · right
        exact rec13071 16 10 (by decide) (by decide)
      · right
        exact rec13074 16 10 (by decide) (by decide)
      · right
        exact rec13076 16 10 (by decide) (by decide)
      · right
        exact rec13078 16 10 (by decide) (by decide)
      · right
        exact rec13080 16 10 (by decide) (by decide)
      · right
        exact rec13082 16 10 (by decide) (by decide)
      · right
        exact rec13085 16 10 (by decide) (by decide)
      · right
        exact rec13087 16 10 (by decide) (by decide)
      · right
        exact rec13089 16 10 (by decide) (by decide)
      · right
        exact rec13091 16 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 250)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 641)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 252)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 253)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13093 16 10 (by decide) (by decide)
      · right
        exact rec13097 16 10 (by decide) (by decide)
      · right
        exact rec13101 16 10 (by decide) (by decide)
      · right
        exact rec13105 16 10 (by decide) (by decide)
      · right
        exact rec13108 16 10 (by decide) (by decide)
      · right
        exact rec13111 16 10 (by decide) (by decide)
      · right
        exact rec13115 16 10 (by decide) (by decide)
      · right
        exact rec13119 16 10 (by decide) (by decide)
      · right
        exact rec13124 16 10 (by decide) (by decide)
      · right
        exact rec13127 16 10 (by decide) (by decide)
      · right
        exact rec13130 16 10 (by decide) (by decide)
      · right
        exact rec13133 16 10 (by decide) (by decide)
      · right
        exact rec13136 16 10 (by decide) (by decide)
      · right
        exact rec13139 16 10 (by decide) (by decide)
      · right
        exact rec13142 16 10 (by decide) (by decide)
      · right
        exact rec13145 16 10 (by decide) (by decide)
      · right
        exact rec13148 16 10 (by decide) (by decide)
      · right
        exact rec13151 16 10 (by decide) (by decide)
      · right
        exact rec13154 16 10 (by decide) (by decide)
      · right
        exact rec13157 16 10 (by decide) (by decide)
      · right
        exact rec13160 16 10 (by decide) (by decide)
      · right
        exact rec13163 16 10 (by decide) (by decide)
      · right
        exact rec13166 16 10 (by decide) (by decide)
      · right
        exact rec13169 16 10 (by decide) (by decide)
      · right
        exact rec13172 16 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 642)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 643)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16579 16 10 (by decide) (by decide)
      · right
        exact rec16581 16 10 (by decide) (by decide)
      · right
        exact rec16583 16 10 (by decide) (by decide)
      · right
        exact rec16585 16 10 (by decide) (by decide)
      · right
        exact rec16587 16 10 (by decide) (by decide)
      · right
        exact rec16589 16 10 (by decide) (by decide)
      · right
        exact rec16591 16 10 (by decide) (by decide)
      · right
        exact rec16593 16 10 (by decide) (by decide)
      · right
        exact rec16595 16 10 (by decide) (by decide)
      · right
        exact rec16597 16 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 654)).length = 1 := by decide +kernel
      have hjj : j < 1 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 257)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 530)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 645)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec12958 16 11 (by decide) (by decide)
  · left
    exact rec12955 16 12 (by decide) (by decide)
  · left
    exact rec12956 16 13 (by decide) (by decide)
  · left
    exact rec12961 16 14 (by decide) (by decide)
  · left
    exact rec12958 16 15 (by decide) (by decide)
end Section14Coverage_16_6_p0_16

#print axioms solution
