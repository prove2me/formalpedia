-- Prove2me | solution 1 for Freiman.section14_s0008_coverage0006_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:35:44.91073+00:00
-- url     : https://prove2.me/submissions/636098cf-c82d-434d-913f-b4af19910726

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
namespace Section14Coverage_8_6_p0_16
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
private theorem rec12964 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[8],[3],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[516]? = some (⟨245,(-1),[8],[3],886⟩) from rfl))
private theorem rec12965 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[8,12],[14],1648⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[517]? = some (⟨245,(-1),[8,12],[14],1648⟩) from rfl))
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
private theorem rec13120 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 253 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(7),[8,12],[10],1647⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[672]? = some (⟨253,(7),[8,12],[10],1647⟩) from rfl))
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
private theorem rec13175 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(0),[4,8],[10],899⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[727]? = some (⟨255,(0),[4,8],[10],899⟩) from rfl))
private theorem rec13177 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(1),[4,8],[10],899⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[729]? = some (⟨255,(1),[4,8],[10],899⟩) from rfl))
private theorem rec13179 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(2),[4,8],[10],900⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[731]? = some (⟨255,(2),[4,8],[10],900⟩) from rfl))
private theorem rec13181 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(3),[4,8],[10],901⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[733]? = some (⟨255,(3),[4,8],[10],901⟩) from rfl))
private theorem rec13183 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(4),[4,8],[10],902⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[735]? = some (⟨255,(4),[4,8],[10],902⟩) from rfl))
private theorem rec13185 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(5),[4,8],[10],903⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[737]? = some (⟨255,(5),[4,8],[10],903⟩) from rfl))
private theorem rec13187 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(6),[4,8],[10],903⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[739]? = some (⟨255,(6),[4,8],[10],903⟩) from rfl))
private theorem rec13189 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(7),[4,8],[10],900⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[741]? = some (⟨255,(7),[4,8],[10],900⟩) from rfl))
private theorem rec13191 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(8),[4,8],[10],901⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[743]? = some (⟨255,(8),[4,8],[10],901⟩) from rfl))
private theorem rec13193 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(9),[4,8],[10],902⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[745]? = some (⟨255,(9),[4,8],[10],902⟩) from rfl))
private theorem rec13195 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(10),[4,8],[10],899⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[747]? = some (⟨255,(10),[4,8],[10],899⟩) from rfl))
private theorem rec13197 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(11),[4,8],[10],899⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[749]? = some (⟨255,(11),[4,8],[10],899⟩) from rfl))
private theorem rec13199 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(12),[4,8],[10],900⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[751]? = some (⟨255,(12),[4,8],[10],900⟩) from rfl))
private theorem rec13201 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(13),[4,8],[10],901⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[753]? = some (⟨255,(13),[4,8],[10],901⟩) from rfl))
private theorem rec13203 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(14),[4,8],[10],902⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[755]? = some (⟨255,(14),[4,8],[10],902⟩) from rfl))
private theorem rec13205 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(15),[4,8],[10],904⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[757]? = some (⟨255,(15),[4,8],[10],904⟩) from rfl))
private theorem rec13207 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(16),[4,8],[10],904⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[759]? = some (⟨255,(16),[4,8],[10],904⟩) from rfl))
private theorem rec13209 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(17),[4,8],[10],900⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[761]? = some (⟨255,(17),[4,8],[10],900⟩) from rfl))
private theorem rec13211 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(18),[4,8],[10],901⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[763]? = some (⟨255,(18),[4,8],[10],901⟩) from rfl))
private theorem rec13213 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(19),[4,8],[10],902⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[765]? = some (⟨255,(19),[4,8],[10],902⟩) from rfl))
private theorem rec13215 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(20),[4,8],[10],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[767]? = some (⟨255,(20),[4,8],[10],905⟩) from rfl))
private theorem rec13217 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(21),[4,8],[10],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[769]? = some (⟨255,(21),[4,8],[10],905⟩) from rfl))
private theorem rec13219 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(22),[4,8],[10],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[771]? = some (⟨255,(22),[4,8],[10],905⟩) from rfl))
private theorem rec13221 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(23),[4,8],[10],901⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[773]? = some (⟨255,(23),[4,8],[10],901⟩) from rfl))
private theorem rec13223 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 255 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨255,(24),[4,8],[10],902⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[775]? = some (⟨255,(24),[4,8],[10],902⟩) from rfl))
private theorem rec13239 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 259 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨259,(1),[4,8,12],[10],906⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[791]? = some (⟨259,(1),[4,8,12],[10],906⟩) from rfl))
private theorem rec13242 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 259 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨259,(3),[4,8,12],[10],907⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[794]? = some (⟨259,(3),[4,8,12],[10],907⟩) from rfl))
private theorem rec13247 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 259 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨259,(5),[8,12],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[799]? = some (⟨259,(5),[8,12],[10],143⟩) from rfl))
private theorem rec13252 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 259 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨259,(7),[8,12],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[804]? = some (⟨259,(7),[8,12],[10],143⟩) from rfl))
private theorem rec13258 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 259 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨259,(11),[8],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[810]? = some (⟨259,(11),[8],[10],143⟩) from rfl))
private theorem rec13263 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 259 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨259,(13),[8,12],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[815]? = some (⟨259,(13),[8,12],[10],143⟩) from rfl))
private theorem rec13268 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 259 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨259,(15),[4,8],[10],53⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[820]? = some (⟨259,(15),[4,8],[10],53⟩) from rfl))
private theorem rec13274 (si parent : ℕ) (hs : si ∈ ([8] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 259 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨259,(17),[8],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[826]? = some (⟨259,(17),[8],[10],143⟩) from rfl))
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
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 8).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 8)).drop 0).take 16, section14Recorded section14Catalog 8 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 8 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 8).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(526,⟨([1],[]),true,([1],[]),false,false,[]⟩),(527,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(528,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(251,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(254,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(255,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(529,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(530,⟨([1],[]),true,([],[]),true,false,[]⟩),(259,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec12950 8 0 (by decide) (by decide)
  · left
    exact rec12956 8 1 (by decide) (by decide)
  · left
    exact rec12957 8 2 (by decide) (by decide)
  · left
    exact rec12964 8 3 (by decide) (by decide)
  · left
    exact rec12950 8 4 (by decide) (by decide)
  · left
    exact rec12956 8 5 (by decide) (by decide)
  · left
    exact rec12959 8 6 (by decide) (by decide)
  · left
    exact rec12958 8 7 (by decide) (by decide)
  · left
    exact rec12955 8 8 (by decide) (by decide)
  · left
    exact rec12956 8 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(526,⟨([1],[]),true,([1],[]),false,false,[]⟩),(527,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(528,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(251,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(254,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(255,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(529,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(530,⟨([1],[]),true,([],[]),true,false,[]⟩),(259,⟨([],[]),false,([],[1]),false,false,[]⟩)] at hgs
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
        exact rec16184 8 10 (by decide) (by decide)
      · right
        exact rec16185 8 10 (by decide) (by decide)
      · right
        exact rec16186 8 10 (by decide) (by decide)
      · right
        exact rec16187 8 10 (by decide) (by decide)
      · right
        exact rec16188 8 10 (by decide) (by decide)
      · right
        exact rec16189 8 10 (by decide) (by decide)
      · right
        exact rec16190 8 10 (by decide) (by decide)
      · right
        exact rec16191 8 10 (by decide) (by decide)
      · right
        exact rec16192 8 10 (by decide) (by decide)
      · right
        exact rec16193 8 10 (by decide) (by decide)
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
        exact rec13038 8 10 (by decide) (by decide)
      · right
        exact rec13041 8 10 (by decide) (by decide)
      · right
        exact rec13043 8 10 (by decide) (by decide)
      · right
        exact rec13045 8 10 (by decide) (by decide)
      · right
        exact rec13047 8 10 (by decide) (by decide)
      · right
        exact rec13049 8 10 (by decide) (by decide)
      · right
        exact rec13052 8 10 (by decide) (by decide)
      · right
        exact rec13054 8 10 (by decide) (by decide)
      · right
        exact rec13056 8 10 (by decide) (by decide)
      · right
        exact rec13058 8 10 (by decide) (by decide)
      · right
        exact rec13060 8 10 (by decide) (by decide)
      · right
        exact rec13063 8 10 (by decide) (by decide)
      · right
        exact rec13065 8 10 (by decide) (by decide)
      · right
        exact rec13067 8 10 (by decide) (by decide)
      · right
        exact rec13069 8 10 (by decide) (by decide)
      · right
        exact rec13071 8 10 (by decide) (by decide)
      · right
        exact rec13074 8 10 (by decide) (by decide)
      · right
        exact rec13076 8 10 (by decide) (by decide)
      · right
        exact rec13078 8 10 (by decide) (by decide)
      · right
        exact rec13080 8 10 (by decide) (by decide)
      · right
        exact rec13082 8 10 (by decide) (by decide)
      · right
        exact rec13085 8 10 (by decide) (by decide)
      · right
        exact rec13087 8 10 (by decide) (by decide)
      · right
        exact rec13089 8 10 (by decide) (by decide)
      · right
        exact rec13091 8 10 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 251)).length = 16 := by decide +kernel
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
        exact rec13093 8 10 (by decide) (by decide)
      · right
        exact rec13097 8 10 (by decide) (by decide)
      · right
        exact rec13101 8 10 (by decide) (by decide)
      · right
        exact rec13105 8 10 (by decide) (by decide)
      · right
        exact rec13108 8 10 (by decide) (by decide)
      · right
        exact rec13111 8 10 (by decide) (by decide)
      · right
        exact rec13115 8 10 (by decide) (by decide)
      · right
        exact rec13120 8 10 (by decide) (by decide)
      · right
        exact rec13124 8 10 (by decide) (by decide)
      · right
        exact rec13127 8 10 (by decide) (by decide)
      · right
        exact rec13130 8 10 (by decide) (by decide)
      · right
        exact rec13133 8 10 (by decide) (by decide)
      · right
        exact rec13136 8 10 (by decide) (by decide)
      · right
        exact rec13139 8 10 (by decide) (by decide)
      · right
        exact rec13142 8 10 (by decide) (by decide)
      · right
        exact rec13145 8 10 (by decide) (by decide)
      · right
        exact rec13148 8 10 (by decide) (by decide)
      · right
        exact rec13151 8 10 (by decide) (by decide)
      · right
        exact rec13154 8 10 (by decide) (by decide)
      · right
        exact rec13157 8 10 (by decide) (by decide)
      · right
        exact rec13160 8 10 (by decide) (by decide)
      · right
        exact rec13163 8 10 (by decide) (by decide)
      · right
        exact rec13166 8 10 (by decide) (by decide)
      · right
        exact rec13169 8 10 (by decide) (by decide)
      · right
        exact rec13172 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 254)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 255)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13175 8 10 (by decide) (by decide)
      · right
        exact rec13177 8 10 (by decide) (by decide)
      · right
        exact rec13179 8 10 (by decide) (by decide)
      · right
        exact rec13181 8 10 (by decide) (by decide)
      · right
        exact rec13183 8 10 (by decide) (by decide)
      · right
        exact rec13185 8 10 (by decide) (by decide)
      · right
        exact rec13187 8 10 (by decide) (by decide)
      · right
        exact rec13189 8 10 (by decide) (by decide)
      · right
        exact rec13191 8 10 (by decide) (by decide)
      · right
        exact rec13193 8 10 (by decide) (by decide)
      · right
        exact rec13195 8 10 (by decide) (by decide)
      · right
        exact rec13197 8 10 (by decide) (by decide)
      · right
        exact rec13199 8 10 (by decide) (by decide)
      · right
        exact rec13201 8 10 (by decide) (by decide)
      · right
        exact rec13203 8 10 (by decide) (by decide)
      · right
        exact rec13205 8 10 (by decide) (by decide)
      · right
        exact rec13207 8 10 (by decide) (by decide)
      · right
        exact rec13209 8 10 (by decide) (by decide)
      · right
        exact rec13211 8 10 (by decide) (by decide)
      · right
        exact rec13213 8 10 (by decide) (by decide)
      · right
        exact rec13215 8 10 (by decide) (by decide)
      · right
        exact rec13217 8 10 (by decide) (by decide)
      · right
        exact rec13219 8 10 (by decide) (by decide)
      · right
        exact rec13221 8 10 (by decide) (by decide)
      · right
        exact rec13223 8 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 529)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 259)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · right
        exact rec13239 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13242 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13247 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13252 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · right
        exact rec13258 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13263 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13268 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13274 8 10 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec12958 8 11 (by decide) (by decide)
  · left
    exact rec12955 8 12 (by decide) (by decide)
  · left
    exact rec12956 8 13 (by decide) (by decide)
  · left
    exact rec12965 8 14 (by decide) (by decide)
  · left
    exact rec12958 8 15 (by decide) (by decide)
end Section14Coverage_8_6_p0_16

#print axioms solution
