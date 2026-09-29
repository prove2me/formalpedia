-- Prove2me | solution 1 for Freiman.section14_s0004_coverage0003_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T01:36:29.859417+00:00
-- url     : https://prove2.me/submissions/76e25a59-0c7c-49ee-99cd-d995f5de44e6

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
namespace Section14Coverage_4_3_p0_16
private theorem rec4527 (si parent : ℕ) (hs : si ∈ ([2, 4, 6, 8, 10, 12, 14, 16] : List ℕ)) (hp : parent ∈ ([0, 4] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[2,4,6,8,10,12,14,16],[0,4],342⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[378]? = some (⟨60,(-1),[2,4,6,8,10,12,14,16],[0,4],342⟩) from rfl))
private theorem rec4538 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[389]? = some (⟨60,(-1),[3,4,7,8,12,15,16],[5],343⟩) from rfl))
private theorem rec4549 (si parent : ℕ) (hs : si ∈ ([4, 8, 10, 12, 16] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,8,10,12,16],[8],69⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[400]? = some (⟨60,(-1),[4,8,10,12,16],[8],69⟩) from rfl))
private theorem rec4550 (si parent : ℕ) (hs : si ∈ ([4, 8, 11, 12, 16] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,8,11,12,16],[1],343⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[401]? = some (⟨60,(-1),[4,8,11,12,16],[1],343⟩) from rfl))
private theorem rec4551 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,8,12],[3],345⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[402]? = some (⟨60,(-1),[4,8,12],[3],345⟩) from rfl))
private theorem rec4552 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,8,12,16],[9],70⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[403]? = some (⟨60,(-1),[4,8,12,16],[9],70⟩) from rfl))
private theorem rec4553 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,8,12,16],[11],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[404]? = some (⟨60,(-1),[4,8,12,16],[11],207⟩) from rfl))
private theorem rec4554 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,8,12,16],[2],344⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[405]? = some (⟨60,(-1),[4,8,12,16],[2],344⟩) from rfl))
private theorem rec4555 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([7] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,8,12,16],[7],345⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[406]? = some (⟨60,(-1),[4,8,12,16],[7],345⟩) from rfl))
private theorem rec4556 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,8,12,16],[10],366⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[407]? = some (⟨60,(-1),[4,8,12,16],[10],366⟩) from rfl))
private theorem rec4557 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([12] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,16],[12],342⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[408]? = some (⟨60,(-1),[4,16],[12],342⟩) from rfl))
private theorem rec4558 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([13] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,16],[13],343⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[409]? = some (⟨60,(-1),[4,16],[13],343⟩) from rfl))
private theorem rec4559 (si parent : ℕ) (hs : si ∈ ([4, 16] : List ℕ)) (hp : parent ∈ ([15] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[4,16],[15],345⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[410]? = some (⟨60,(-1),[4,16],[15],345⟩) from rfl))
private theorem rec4712 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(0),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[563]? = some (⟨64,(0),[4,8],[6],3⟩) from rfl))
private theorem rec4713 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(0),[4,8,16],[14],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[564]? = some (⟨64,(0),[4,8,16],[14],368⟩) from rfl))
private theorem rec4718 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(1),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[569]? = some (⟨64,(1),[4,8],[6],3⟩) from rfl))
private theorem rec4719 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(1),[4,8,16],[14],369⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[570]? = some (⟨64,(1),[4,8,16],[14],369⟩) from rfl))
private theorem rec4724 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(2),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[575]? = some (⟨64,(2),[4,8],[6],3⟩) from rfl))
private theorem rec4725 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(2),[4,8,16],[14],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[576]? = some (⟨64,(2),[4,8,16],[14],368⟩) from rfl))
private theorem rec4730 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(3),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[581]? = some (⟨64,(3),[4,8],[6],3⟩) from rfl))
private theorem rec4731 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(3),[4,8,16],[14],370⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[582]? = some (⟨64,(3),[4,8,16],[14],370⟩) from rfl))
private theorem rec4736 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(4),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[587]? = some (⟨64,(4),[4,8],[6],3⟩) from rfl))
private theorem rec4737 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(4),[4,8,16],[14],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[588]? = some (⟨64,(4),[4,8,16],[14],371⟩) from rfl))
private theorem rec4742 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(5),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[593]? = some (⟨64,(5),[4,8],[6],3⟩) from rfl))
private theorem rec4743 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(5),[4,8,16],[14],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[594]? = some (⟨64,(5),[4,8,16],[14],368⟩) from rfl))
private theorem rec4748 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(6),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[599]? = some (⟨64,(6),[4,8],[6],3⟩) from rfl))
private theorem rec4749 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(6),[4,8,16],[14],369⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[600]? = some (⟨64,(6),[4,8,16],[14],369⟩) from rfl))
private theorem rec4754 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(7),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[605]? = some (⟨64,(7),[4,8],[6],3⟩) from rfl))
private theorem rec4755 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(7),[4,8,16],[14],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[606]? = some (⟨64,(7),[4,8,16],[14],368⟩) from rfl))
private theorem rec4760 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(8),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[611]? = some (⟨64,(8),[4,8],[6],3⟩) from rfl))
private theorem rec4761 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(8),[4,8,16],[14],370⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[612]? = some (⟨64,(8),[4,8,16],[14],370⟩) from rfl))
private theorem rec4766 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(9),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[617]? = some (⟨64,(9),[4,8],[6],3⟩) from rfl))
private theorem rec4767 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(9),[4,8,16],[14],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[618]? = some (⟨64,(9),[4,8,16],[14],371⟩) from rfl))
private theorem rec4772 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(10),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[623]? = some (⟨64,(10),[4,8],[6],3⟩) from rfl))
private theorem rec4773 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(10),[4,8,16],[14],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[624]? = some (⟨64,(10),[4,8,16],[14],372⟩) from rfl))
private theorem rec4778 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(11),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[629]? = some (⟨64,(11),[4,8],[6],3⟩) from rfl))
private theorem rec4779 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(11),[4,8,16],[14],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[630]? = some (⟨64,(11),[4,8,16],[14],372⟩) from rfl))
private theorem rec4784 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(12),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[635]? = some (⟨64,(12),[4,8],[6],3⟩) from rfl))
private theorem rec4785 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(12),[4,8,16],[14],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[636]? = some (⟨64,(12),[4,8,16],[14],372⟩) from rfl))
private theorem rec4790 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(13),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[641]? = some (⟨64,(13),[4,8],[6],3⟩) from rfl))
private theorem rec4791 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(13),[4,8,16],[14],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[642]? = some (⟨64,(13),[4,8,16],[14],372⟩) from rfl))
private theorem rec4796 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(14),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[647]? = some (⟨64,(14),[4,8],[6],3⟩) from rfl))
private theorem rec4797 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(14),[4,8,16],[14],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[648]? = some (⟨64,(14),[4,8,16],[14],371⟩) from rfl))
private theorem rec4802 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(15),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[653]? = some (⟨64,(15),[4,8],[6],3⟩) from rfl))
private theorem rec4803 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(15),[4,8,16],[14],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[654]? = some (⟨64,(15),[4,8,16],[14],373⟩) from rfl))
private theorem rec4808 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(16),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[659]? = some (⟨64,(16),[4,8],[6],3⟩) from rfl))
private theorem rec4809 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(16),[4,8,16],[14],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[660]? = some (⟨64,(16),[4,8,16],[14],373⟩) from rfl))
private theorem rec4814 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(17),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[665]? = some (⟨64,(17),[4,8],[6],3⟩) from rfl))
private theorem rec4815 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(17),[4,8,16],[14],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[666]? = some (⟨64,(17),[4,8,16],[14],373⟩) from rfl))
private theorem rec4820 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(18),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[671]? = some (⟨64,(18),[4,8],[6],3⟩) from rfl))
private theorem rec4821 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(18),[4,8,16],[14],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[672]? = some (⟨64,(18),[4,8,16],[14],373⟩) from rfl))
private theorem rec4826 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(19),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[677]? = some (⟨64,(19),[4,8],[6],3⟩) from rfl))
private theorem rec4827 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(19),[4,8,16],[14],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[678]? = some (⟨64,(19),[4,8,16],[14],373⟩) from rfl))
private theorem rec4832 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(20),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[683]? = some (⟨64,(20),[4,8],[6],3⟩) from rfl))
private theorem rec4833 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(20),[4,8,16],[14],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[684]? = some (⟨64,(20),[4,8,16],[14],374⟩) from rfl))
private theorem rec4838 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(21),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[689]? = some (⟨64,(21),[4,8],[6],3⟩) from rfl))
private theorem rec4839 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(21),[4,8,16],[14],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[690]? = some (⟨64,(21),[4,8,16],[14],374⟩) from rfl))
private theorem rec4844 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(22),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[695]? = some (⟨64,(22),[4,8],[6],3⟩) from rfl))
private theorem rec4845 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(22),[4,8,16],[14],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[696]? = some (⟨64,(22),[4,8,16],[14],374⟩) from rfl))
private theorem rec4850 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(23),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[701]? = some (⟨64,(23),[4,8],[6],3⟩) from rfl))
private theorem rec4851 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(23),[4,8,16],[14],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[702]? = some (⟨64,(23),[4,8,16],[14],374⟩) from rfl))
private theorem rec4856 (si parent : ℕ) (hs : si ∈ ([4, 8] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 64 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(24),[4,8],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[707]? = some (⟨64,(24),[4,8],[6],3⟩) from rfl))
private theorem rec4857 (si parent : ℕ) (hs : si ∈ ([4, 8, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 64 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(24),[4,8,16],[14],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[708]? = some (⟨64,(24),[4,8,16],[14],374⟩) from rfl))
private theorem rec4937 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(0),[4,8,12],[6],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[788]? = some (⟨69,(0),[4,8,12],[6],189⟩) from rfl))
private theorem rec4938 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(0),[4,8,12,16],[14],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[789]? = some (⟨69,(0),[4,8,12,16],[14],189⟩) from rfl))
private theorem rec4945 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(1),[4],[6],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[796]? = some (⟨69,(1),[4],[6],190⟩) from rfl))
private theorem rec4946 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(1),[4,8,12,16],[14],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[797]? = some (⟨69,(1),[4,8,12,16],[14],260⟩) from rfl))
private theorem rec4955 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[4,8,12],[6],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[806]? = some (⟨69,(2),[4,8,12],[6],191⟩) from rfl))
private theorem rec4956 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[4,8,12,16],[14],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[807]? = some (⟨69,(2),[4,8,12,16],[14],375⟩) from rfl))
private theorem rec4967 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[4,8,12],[6],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[818]? = some (⟨69,(3),[4,8,12],[6],192⟩) from rfl))
private theorem rec4968 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[4,8,12,16],[14],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[819]? = some (⟨69,(3),[4,8,12,16],[14],376⟩) from rfl))
private theorem rec4979 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[4,8,12],[6],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[830]? = some (⟨69,(4),[4,8,12],[6],193⟩) from rfl))
private theorem rec4980 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[4,8,12,16],[14],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[831]? = some (⟨69,(4),[4,8,12,16],[14],377⟩) from rfl))
private theorem rec4990 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(5),[4,8,12],[6],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[841]? = some (⟨69,(5),[4,8,12],[6],189⟩) from rfl))
private theorem rec4991 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(5),[4,8,12,16],[14],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[842]? = some (⟨69,(5),[4,8,12,16],[14],189⟩) from rfl))
private theorem rec4998 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(6),[4],[6],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[849]? = some (⟨69,(6),[4],[6],190⟩) from rfl))
private theorem rec4999 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(6),[4,8,12,16],[14],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[850]? = some (⟨69,(6),[4,8,12,16],[14],260⟩) from rfl))
private theorem rec5007 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[4,8,12],[6],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[858]? = some (⟨69,(7),[4,8,12],[6],191⟩) from rfl))
private theorem rec5008 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[4,8,12,16],[14],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[859]? = some (⟨69,(7),[4,8,12,16],[14],375⟩) from rfl))
private theorem rec5017 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[4,8,12],[6],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[868]? = some (⟨69,(8),[4,8,12],[6],192⟩) from rfl))
private theorem rec5018 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[4,8,12,16],[14],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[869]? = some (⟨69,(8),[4,8,12,16],[14],376⟩) from rfl))
private theorem rec5027 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[4,8,12],[6],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[878]? = some (⟨69,(9),[4,8,12],[6],193⟩) from rfl))
private theorem rec5028 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[4,8,12,16],[14],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[879]? = some (⟨69,(9),[4,8,12,16],[14],377⟩) from rfl))
private theorem rec5037 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(10),[4,8,12],[6],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[888]? = some (⟨69,(10),[4,8,12],[6],194⟩) from rfl))
private theorem rec5038 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(10),[4,8,12,16],[14],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[889]? = some (⟨69,(10),[4,8,12,16],[14],194⟩) from rfl))
private theorem rec5045 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(11),[4],[6],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[896]? = some (⟨69,(11),[4],[6],195⟩) from rfl))
private theorem rec5046 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(11),[4,8,12,16],[14],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[897]? = some (⟨69,(11),[4,8,12,16],[14],267⟩) from rfl))
private theorem rec5054 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[4,8,12],[6],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[905]? = some (⟨69,(12),[4,8,12],[6],195⟩) from rfl))
private theorem rec5055 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[4,8,12,16],[14],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[906]? = some (⟨69,(12),[4,8,12,16],[14],378⟩) from rfl))
private theorem rec5064 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[4,8,12],[6],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[915]? = some (⟨69,(13),[4,8,12],[6],195⟩) from rfl))
private theorem rec5065 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[4,8,12,16],[14],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[916]? = some (⟨69,(13),[4,8,12,16],[14],378⟩) from rfl))
private theorem rec5074 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[4,8,12],[6],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[925]? = some (⟨69,(14),[4,8,12],[6],193⟩) from rfl))
private theorem rec5075 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[4,8,12,16],[14],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[926]? = some (⟨69,(14),[4,8,12,16],[14],377⟩) from rfl))
private theorem rec5084 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(15),[4,8,12],[6],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[935]? = some (⟨69,(15),[4,8,12],[6],196⟩) from rfl))
private theorem rec5085 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(15),[4,8,12,16],[14],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[936]? = some (⟨69,(15),[4,8,12,16],[14],196⟩) from rfl))
private theorem rec5092 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(16),[4],[6],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[943]? = some (⟨69,(16),[4],[6],197⟩) from rfl))
private theorem rec5093 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(16),[4,8,12,16],[14],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[944]? = some (⟨69,(16),[4,8,12,16],[14],269⟩) from rfl))
private theorem rec5101 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[4,8,12],[6],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[952]? = some (⟨69,(17),[4,8,12],[6],197⟩) from rfl))
private theorem rec5102 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[4,8,12,16],[14],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[953]? = some (⟨69,(17),[4,8,12,16],[14],379⟩) from rfl))
private theorem rec5111 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[4,8,12],[6],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[962]? = some (⟨69,(18),[4,8,12],[6],197⟩) from rfl))
private theorem rec5112 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[4,8,12,16],[14],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[963]? = some (⟨69,(18),[4,8,12,16],[14],379⟩) from rfl))
private theorem rec5121 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[4,8,12],[6],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[972]? = some (⟨69,(19),[4,8,12],[6],197⟩) from rfl))
private theorem rec5122 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[4,8,12,16],[14],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[973]? = some (⟨69,(19),[4,8,12,16],[14],379⟩) from rfl))
private theorem rec5131 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(20),[4,8,12],[6],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[982]? = some (⟨69,(20),[4,8,12],[6],198⟩) from rfl))
private theorem rec5132 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(20),[4,8,12,16],[14],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[983]? = some (⟨69,(20),[4,8,12,16],[14],198⟩) from rfl))
private theorem rec5139 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(21),[4],[6],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[990]? = some (⟨69,(21),[4],[6],199⟩) from rfl))
private theorem rec5140 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(21),[4,8,12,16],[14],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[991]? = some (⟨69,(21),[4,8,12,16],[14],271⟩) from rfl))
private theorem rec5148 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[4,8,12],[6],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[999]? = some (⟨69,(22),[4,8,12],[6],199⟩) from rfl))
private theorem rec5149 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[4,8,12,16],[14],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1000]? = some (⟨69,(22),[4,8,12,16],[14],380⟩) from rfl))
private theorem rec5158 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[4,8,12],[6],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1009]? = some (⟨69,(23),[4,8,12],[6],199⟩) from rfl))
private theorem rec5159 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[4,8,12,16],[14],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1010]? = some (⟨69,(23),[4,8,12,16],[14],380⟩) from rfl))
private theorem rec5168 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[4,8,12],[6],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1019]? = some (⟨69,(24),[4,8,12],[6],199⟩) from rfl))
private theorem rec5169 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[4,8,12,16],[14],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1020]? = some (⟨69,(24),[4,8,12,16],[14],380⟩) from rfl))
private theorem rec5176 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(0),[4],[14],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1027]? = some (⟨72,(0),[4],[14],354⟩) from rfl))
private theorem rec5177 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(0),[4,8,12],[6],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1028]? = some (⟨72,(0),[4,8,12],[6],354⟩) from rfl))
private theorem rec5184 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(1),[4],[14],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1035]? = some (⟨72,(1),[4],[14],355⟩) from rfl))
private theorem rec5185 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(1),[4,8,12],[6],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1036]? = some (⟨72,(1),[4,8,12],[6],355⟩) from rfl))
private theorem rec5192 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(2),[4],[14],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1043]? = some (⟨72,(2),[4],[14],356⟩) from rfl))
private theorem rec5193 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(2),[4,8,12],[6],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1044]? = some (⟨72,(2),[4,8,12],[6],356⟩) from rfl))
private theorem rec5200 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(3),[4],[14],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1051]? = some (⟨72,(3),[4],[14],357⟩) from rfl))
private theorem rec5201 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(3),[4,8,12],[6],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1052]? = some (⟨72,(3),[4,8,12],[6],357⟩) from rfl))
private theorem rec5208 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(4),[4],[14],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1059]? = some (⟨72,(4),[4],[14],354⟩) from rfl))
private theorem rec5209 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(4),[4,8,12],[6],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1060]? = some (⟨72,(4),[4,8,12],[6],354⟩) from rfl))
private theorem rec5216 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(5),[4],[14],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1067]? = some (⟨72,(5),[4],[14],355⟩) from rfl))
private theorem rec5217 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(5),[4,8,12],[6],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1068]? = some (⟨72,(5),[4,8,12],[6],355⟩) from rfl))
private theorem rec5224 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(6),[4],[14],358⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1075]? = some (⟨72,(6),[4],[14],358⟩) from rfl))
private theorem rec5225 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(6),[4,8,12],[6],358⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1076]? = some (⟨72,(6),[4,8,12],[6],358⟩) from rfl))
private theorem rec5232 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(7),[4],[14],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1083]? = some (⟨72,(7),[4],[14],357⟩) from rfl))
private theorem rec5233 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(7),[4,8,12],[6],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1084]? = some (⟨72,(7),[4,8,12],[6],357⟩) from rfl))
private theorem rec5240 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(8),[4],[14],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1091]? = some (⟨72,(8),[4],[14],354⟩) from rfl))
private theorem rec5241 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(8),[4,8,12],[6],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1092]? = some (⟨72,(8),[4,8,12],[6],354⟩) from rfl))
private theorem rec5248 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(9),[4],[14],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1099]? = some (⟨72,(9),[4],[14],355⟩) from rfl))
private theorem rec5249 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(9),[4,8,12],[6],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1100]? = some (⟨72,(9),[4,8,12],[6],355⟩) from rfl))
private theorem rec5256 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(10),[4],[14],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1107]? = some (⟨72,(10),[4],[14],356⟩) from rfl))
private theorem rec5257 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(10),[4,8,12],[6],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1108]? = some (⟨72,(10),[4,8,12],[6],356⟩) from rfl))
private theorem rec5264 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(11),[4],[14],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1115]? = some (⟨72,(11),[4],[14],357⟩) from rfl))
private theorem rec5265 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(11),[4,8,12],[6],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1116]? = some (⟨72,(11),[4,8,12],[6],357⟩) from rfl))
private theorem rec5272 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(12),[4],[14],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1123]? = some (⟨72,(12),[4],[14],354⟩) from rfl))
private theorem rec5273 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(12),[4,8,12],[6],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1124]? = some (⟨72,(12),[4,8,12],[6],354⟩) from rfl))
private theorem rec5280 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(13),[4],[14],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1131]? = some (⟨72,(13),[4],[14],355⟩) from rfl))
private theorem rec5281 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(13),[4,8,12],[6],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1132]? = some (⟨72,(13),[4,8,12],[6],355⟩) from rfl))
private theorem rec5288 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(14),[4],[14],359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1139]? = some (⟨72,(14),[4],[14],359⟩) from rfl))
private theorem rec5289 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(14),[4,8,12],[6],359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1140]? = some (⟨72,(14),[4,8,12],[6],359⟩) from rfl))
private theorem rec5296 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 72 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(15),[4],[14],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1147]? = some (⟨72,(15),[4],[14],357⟩) from rfl))
private theorem rec5297 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 72 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(15),[4,8,12],[6],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1148]? = some (⟨72,(15),[4,8,12],[6],357⟩) from rfl))
private theorem rec5306 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[4,8,12],[6],360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1157]? = some (⟨75,(0),[4,8,12],[6],360⟩) from rfl))
private theorem rec5307 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[4,8,12],[14],381⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1158]? = some (⟨75,(0),[4,8,12],[14],381⟩) from rfl))
private theorem rec5316 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[4,8,12],[6],361⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1167]? = some (⟨75,(1),[4,8,12],[6],361⟩) from rfl))
private theorem rec5317 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[4,8,12],[14],382⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1168]? = some (⟨75,(1),[4,8,12],[14],382⟩) from rfl))
private theorem rec5326 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[4,8,12],[6],362⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1177]? = some (⟨75,(2),[4,8,12],[6],362⟩) from rfl))
private theorem rec5327 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[4,8,12],[14],383⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1178]? = some (⟨75,(2),[4,8,12],[14],383⟩) from rfl))
private theorem rec5336 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[4,8,12],[6],363⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1187]? = some (⟨75,(3),[4,8,12],[6],363⟩) from rfl))
private theorem rec5337 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[4,8,12],[14],384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1188]? = some (⟨75,(3),[4,8,12],[14],384⟩) from rfl))
private theorem rec5439 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(0),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[64]? = some (⟨79,(0),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5442 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(1),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[67]? = some (⟨79,(1),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5446 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(2),[4],[14],364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[71]? = some (⟨79,(2),[4],[14],364⟩) from rfl))
private theorem rec5447 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 79 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(2),[4,8,12],[6],364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[72]? = some (⟨79,(2),[4,8,12],[6],364⟩) from rfl))
private theorem rec5453 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(3),[4,8,12],[6,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[78]? = some (⟨79,(3),[4,8,12],[6,14],101⟩) from rfl))
private theorem rec5456 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(4),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[81]? = some (⟨79,(4),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5459 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(5),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[84]? = some (⟨79,(5),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5463 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(6),[4],[14],365⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[88]? = some (⟨79,(6),[4],[14],365⟩) from rfl))
private theorem rec5464 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 79 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(6),[4,8,12],[6],365⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[89]? = some (⟨79,(6),[4,8,12],[6],365⟩) from rfl))
private theorem rec5470 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(7),[4,8,12],[6,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[95]? = some (⟨79,(7),[4,8,12],[6,14],101⟩) from rfl))
private theorem rec5473 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(8),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[98]? = some (⟨79,(8),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5476 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(9),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[101]? = some (⟨79,(9),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5479 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(10),[4,8,12],[6,14],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[104]? = some (⟨79,(10),[4,8,12],[6,14],339⟩) from rfl))
private theorem rec5484 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(11),[4,8,12],[6,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[109]? = some (⟨79,(11),[4,8,12],[6,14],101⟩) from rfl))
private theorem rec5487 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(12),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[112]? = some (⟨79,(12),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5490 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(13),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[115]? = some (⟨79,(13),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5493 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(14),[4,8,12],[6,14],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[118]? = some (⟨79,(14),[4,8,12],[6,14],286⟩) from rfl))
private theorem rec5496 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(15),[4,8,12],[6,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[121]? = some (⟨79,(15),[4,8,12],[6,14],101⟩) from rfl))
private theorem rec5499 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(16),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[124]? = some (⟨79,(16),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5502 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(17),[4,8,12],[6,14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[127]? = some (⟨79,(17),[4,8,12],[6,14],2⟩) from rfl))
private theorem rec5505 (si parent : ℕ) (hs : si ∈ ([4] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 79 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(18),[4],[6],204⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[130]? = some (⟨79,(18),[4],[6],204⟩) from rfl))
private theorem rec5506 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(18),[4,8,12],[14],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[131]? = some (⟨79,(18),[4,8,12],[14],287⟩) from rfl))
private theorem rec5510 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6, 14] : List ℕ)) : section14Recorded section14Catalog si parent 79 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(19),[4,8,12],[6,14],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[135]? = some (⟨79,(19),[4,8,12],[6,14],101⟩) from rfl))
private theorem rec16116 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(0),[4,8,12],[6],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1195]? = some (⟨507,(0),[4,8,12],[6],349⟩) from rfl))
private theorem rec16117 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(0),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1196]? = some (⟨507,(0),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16118 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(1),[4,8,12],[6],1267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1197]? = some (⟨507,(1),[4,8,12],[6],1267⟩) from rfl))
private theorem rec16119 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(1),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1198]? = some (⟨507,(1),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16120 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(2),[4,8,12],[6],1268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1199]? = some (⟨507,(2),[4,8,12],[6],1268⟩) from rfl))
private theorem rec16121 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(2),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1200]? = some (⟨507,(2),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16122 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(3),[4,8,12],[6],1267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1201]? = some (⟨507,(3),[4,8,12],[6],1267⟩) from rfl))
private theorem rec16123 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(3),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1202]? = some (⟨507,(3),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16124 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(4),[4,8,12],[6],1269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1203]? = some (⟨507,(4),[4,8,12],[6],1269⟩) from rfl))
private theorem rec16125 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(4),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1204]? = some (⟨507,(4),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16126 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(5),[4,8,12],[6],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1205]? = some (⟨507,(5),[4,8,12],[6],349⟩) from rfl))
private theorem rec16127 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(5),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1206]? = some (⟨507,(5),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16128 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(6),[4,8,12],[6],1267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1207]? = some (⟨507,(6),[4,8,12],[6],1267⟩) from rfl))
private theorem rec16129 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(6),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1208]? = some (⟨507,(6),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16130 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(7),[4,8,12],[6],1268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1209]? = some (⟨507,(7),[4,8,12],[6],1268⟩) from rfl))
private theorem rec16131 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(7),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1210]? = some (⟨507,(7),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16132 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(8),[4,8,12],[6],1267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1211]? = some (⟨507,(8),[4,8,12],[6],1267⟩) from rfl))
private theorem rec16133 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(8),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1212]? = some (⟨507,(8),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16134 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 507 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(9),[4,8,12],[6],1269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1213]? = some (⟨507,(9),[4,8,12],[6],1269⟩) from rfl))
private theorem rec16135 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 507 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨507,(9),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1214]? = some (⟨507,(9),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16136 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(0),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1215]? = some (⟨510,(0),[4,8,12],[6],2⟩) from rfl))
private theorem rec16137 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(0),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1216]? = some (⟨510,(0),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16138 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(1),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1217]? = some (⟨510,(1),[4,8,12],[6],2⟩) from rfl))
private theorem rec16139 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(1),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1218]? = some (⟨510,(1),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16140 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(2),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1219]? = some (⟨510,(2),[4,8,12],[6],2⟩) from rfl))
private theorem rec16141 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(2),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1220]? = some (⟨510,(2),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16142 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(3),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1221]? = some (⟨510,(3),[4,8,12],[6],2⟩) from rfl))
private theorem rec16143 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(3),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1222]? = some (⟨510,(3),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16144 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(4),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1223]? = some (⟨510,(4),[4,8,12],[6],2⟩) from rfl))
private theorem rec16145 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(4),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1224]? = some (⟨510,(4),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16146 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(5),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1225]? = some (⟨510,(5),[4,8,12],[6],2⟩) from rfl))
private theorem rec16147 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(5),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1226]? = some (⟨510,(5),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16148 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(6),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1227]? = some (⟨510,(6),[4,8,12],[6],2⟩) from rfl))
private theorem rec16149 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(6),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1228]? = some (⟨510,(6),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16150 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(7),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1229]? = some (⟨510,(7),[4,8,12],[6],2⟩) from rfl))
private theorem rec16151 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(7),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1230]? = some (⟨510,(7),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16152 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(8),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1231]? = some (⟨510,(8),[4,8,12],[6],2⟩) from rfl))
private theorem rec16153 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(8),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1232]? = some (⟨510,(8),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16154 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 510 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(9),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1233]? = some (⟨510,(9),[4,8,12],[6],2⟩) from rfl))
private theorem rec16155 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 510 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨510,(9),[4,8,12,16],[14],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1234]? = some (⟨510,(9),[4,8,12,16],[14],2⟩) from rfl))
private theorem rec16156 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 513 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨513,(0),[4,8,12],[6],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1235]? = some (⟨513,(0),[4,8,12],[6],98⟩) from rfl))
private theorem rec16157 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 513 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨513,(0),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1236]? = some (⟨513,(0),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16158 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 513 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨513,(1),[4,8,12],[6],1258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1237]? = some (⟨513,(1),[4,8,12],[6],1258⟩) from rfl))
private theorem rec16159 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 513 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨513,(1),[4,8,12,16],[14],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1238]? = some (⟨513,(1),[4,8,12,16],[14],3⟩) from rfl))
private theorem rec16160 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 513 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨513,(2),[4,8,12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1239]? = some (⟨513,(2),[4,8,12],[6],3⟩) from rfl))
private theorem rec16161 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 513 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨513,(2),[4,8,12,16],[14],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1240]? = some (⟨513,(2),[4,8,12,16],[14],29⟩) from rfl))
private theorem rec16162 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 513 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨513,(3),[4,8,12],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1241]? = some (⟨513,(3),[4,8,12],[6],3⟩) from rfl))
private theorem rec16163 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 513 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨513,(3),[4,8,12,16],[14],1264⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1242]? = some (⟨513,(3),[4,8,12,16],[14],1264⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 4).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 4)).drop 0).take 16, section14Recorded section14Catalog 4 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 4 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 4).plans.drop 3).take 1 = [⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(506,⟨([1],[]),true,([1],[]),false,false,[]⟩),(507,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(508,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(509,⟨([2],[]),true,([2],[]),false,false,[]⟩),(510,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(511,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(512,⟨([1],[]),true,([2],[]),false,false,[]⟩),(513,⟨([2],[]),true,([1],[]),false,false,[]⟩),(514,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(515,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec4527 4 0 (by decide) (by decide)
  · left
    exact rec4550 4 1 (by decide) (by decide)
  · left
    exact rec4554 4 2 (by decide) (by decide)
  · left
    exact rec4551 4 3 (by decide) (by decide)
  · left
    exact rec4527 4 4 (by decide) (by decide)
  · left
    exact rec4538 4 5 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(506,⟨([1],[]),true,([1],[]),false,false,[]⟩),(507,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(508,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(509,⟨([2],[]),true,([2],[]),false,false,[]⟩),(510,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(511,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(512,⟨([1],[]),true,([2],[]),false,false,[]⟩),(513,⟨([2],[]),true,([1],[]),false,false,[]⟩),(514,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(515,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 506)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 507)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16116 4 6 (by decide) (by decide)
      · right
        exact rec16118 4 6 (by decide) (by decide)
      · right
        exact rec16120 4 6 (by decide) (by decide)
      · right
        exact rec16122 4 6 (by decide) (by decide)
      · right
        exact rec16124 4 6 (by decide) (by decide)
      · right
        exact rec16126 4 6 (by decide) (by decide)
      · right
        exact rec16128 4 6 (by decide) (by decide)
      · right
        exact rec16130 4 6 (by decide) (by decide)
      · right
        exact rec16132 4 6 (by decide) (by decide)
      · right
        exact rec16134 4 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 508)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 64)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4712 4 6 (by decide) (by decide)
      · right
        exact rec4718 4 6 (by decide) (by decide)
      · right
        exact rec4724 4 6 (by decide) (by decide)
      · right
        exact rec4730 4 6 (by decide) (by decide)
      · right
        exact rec4736 4 6 (by decide) (by decide)
      · right
        exact rec4742 4 6 (by decide) (by decide)
      · right
        exact rec4748 4 6 (by decide) (by decide)
      · right
        exact rec4754 4 6 (by decide) (by decide)
      · right
        exact rec4760 4 6 (by decide) (by decide)
      · right
        exact rec4766 4 6 (by decide) (by decide)
      · right
        exact rec4772 4 6 (by decide) (by decide)
      · right
        exact rec4778 4 6 (by decide) (by decide)
      · right
        exact rec4784 4 6 (by decide) (by decide)
      · right
        exact rec4790 4 6 (by decide) (by decide)
      · right
        exact rec4796 4 6 (by decide) (by decide)
      · right
        exact rec4802 4 6 (by decide) (by decide)
      · right
        exact rec4808 4 6 (by decide) (by decide)
      · right
        exact rec4814 4 6 (by decide) (by decide)
      · right
        exact rec4820 4 6 (by decide) (by decide)
      · right
        exact rec4826 4 6 (by decide) (by decide)
      · right
        exact rec4832 4 6 (by decide) (by decide)
      · right
        exact rec4838 4 6 (by decide) (by decide)
      · right
        exact rec4844 4 6 (by decide) (by decide)
      · right
        exact rec4850 4 6 (by decide) (by decide)
      · right
        exact rec4856 4 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 65)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 509)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 510)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16136 4 6 (by decide) (by decide)
      · right
        exact rec16138 4 6 (by decide) (by decide)
      · right
        exact rec16140 4 6 (by decide) (by decide)
      · right
        exact rec16142 4 6 (by decide) (by decide)
      · right
        exact rec16144 4 6 (by decide) (by decide)
      · right
        exact rec16146 4 6 (by decide) (by decide)
      · right
        exact rec16148 4 6 (by decide) (by decide)
      · right
        exact rec16150 4 6 (by decide) (by decide)
      · right
        exact rec16152 4 6 (by decide) (by decide)
      · right
        exact rec16154 4 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 511)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 69)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4937 4 6 (by decide) (by decide)
      · right
        exact rec4945 4 6 (by decide) (by decide)
      · right
        exact rec4955 4 6 (by decide) (by decide)
      · right
        exact rec4967 4 6 (by decide) (by decide)
      · right
        exact rec4979 4 6 (by decide) (by decide)
      · right
        exact rec4990 4 6 (by decide) (by decide)
      · right
        exact rec4998 4 6 (by decide) (by decide)
      · right
        exact rec5007 4 6 (by decide) (by decide)
      · right
        exact rec5017 4 6 (by decide) (by decide)
      · right
        exact rec5027 4 6 (by decide) (by decide)
      · right
        exact rec5037 4 6 (by decide) (by decide)
      · right
        exact rec5045 4 6 (by decide) (by decide)
      · right
        exact rec5054 4 6 (by decide) (by decide)
      · right
        exact rec5064 4 6 (by decide) (by decide)
      · right
        exact rec5074 4 6 (by decide) (by decide)
      · right
        exact rec5084 4 6 (by decide) (by decide)
      · right
        exact rec5092 4 6 (by decide) (by decide)
      · right
        exact rec5101 4 6 (by decide) (by decide)
      · right
        exact rec5111 4 6 (by decide) (by decide)
      · right
        exact rec5121 4 6 (by decide) (by decide)
      · right
        exact rec5131 4 6 (by decide) (by decide)
      · right
        exact rec5139 4 6 (by decide) (by decide)
      · right
        exact rec5148 4 6 (by decide) (by decide)
      · right
        exact rec5158 4 6 (by decide) (by decide)
      · right
        exact rec5168 4 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 70)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 71)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 72)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5177 4 6 (by decide) (by decide)
      · right
        exact rec5185 4 6 (by decide) (by decide)
      · right
        exact rec5193 4 6 (by decide) (by decide)
      · right
        exact rec5201 4 6 (by decide) (by decide)
      · right
        exact rec5209 4 6 (by decide) (by decide)
      · right
        exact rec5217 4 6 (by decide) (by decide)
      · right
        exact rec5225 4 6 (by decide) (by decide)
      · right
        exact rec5233 4 6 (by decide) (by decide)
      · right
        exact rec5241 4 6 (by decide) (by decide)
      · right
        exact rec5249 4 6 (by decide) (by decide)
      · right
        exact rec5257 4 6 (by decide) (by decide)
      · right
        exact rec5265 4 6 (by decide) (by decide)
      · right
        exact rec5273 4 6 (by decide) (by decide)
      · right
        exact rec5281 4 6 (by decide) (by decide)
      · right
        exact rec5289 4 6 (by decide) (by decide)
      · right
        exact rec5297 4 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 73)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 74)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 75)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5306 4 6 (by decide) (by decide)
      · right
        exact rec5316 4 6 (by decide) (by decide)
      · right
        exact rec5326 4 6 (by decide) (by decide)
      · right
        exact rec5336 4 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 512)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 513)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16156 4 6 (by decide) (by decide)
      · right
        exact rec16158 4 6 (by decide) (by decide)
      · right
        exact rec16160 4 6 (by decide) (by decide)
      · right
        exact rec16162 4 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 514)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 79)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5439 4 6 (by decide) (by decide)
      · right
        exact rec5442 4 6 (by decide) (by decide)
      · right
        exact rec5447 4 6 (by decide) (by decide)
      · right
        exact rec5453 4 6 (by decide) (by decide)
      · right
        exact rec5456 4 6 (by decide) (by decide)
      · right
        exact rec5459 4 6 (by decide) (by decide)
      · right
        exact rec5464 4 6 (by decide) (by decide)
      · right
        exact rec5470 4 6 (by decide) (by decide)
      · right
        exact rec5473 4 6 (by decide) (by decide)
      · right
        exact rec5476 4 6 (by decide) (by decide)
      · right
        exact rec5479 4 6 (by decide) (by decide)
      · right
        exact rec5484 4 6 (by decide) (by decide)
      · right
        exact rec5487 4 6 (by decide) (by decide)
      · right
        exact rec5490 4 6 (by decide) (by decide)
      · right
        exact rec5493 4 6 (by decide) (by decide)
      · right
        exact rec5496 4 6 (by decide) (by decide)
      · right
        exact rec5499 4 6 (by decide) (by decide)
      · right
        exact rec5502 4 6 (by decide) (by decide)
      · right
        exact rec5505 4 6 (by decide) (by decide)
      · right
        exact rec5510 4 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 515)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 81)).length = 10 := by decide +kernel
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
    exact rec4555 4 7 (by decide) (by decide)
  · left
    exact rec4549 4 8 (by decide) (by decide)
  · left
    exact rec4552 4 9 (by decide) (by decide)
  · left
    exact rec4556 4 10 (by decide) (by decide)
  · left
    exact rec4553 4 11 (by decide) (by decide)
  · left
    exact rec4557 4 12 (by decide) (by decide)
  · left
    exact rec4558 4 13 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(506,⟨([1],[]),true,([1],[]),false,false,[]⟩),(507,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(508,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(509,⟨([2],[]),true,([2],[]),false,false,[]⟩),(510,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(511,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(512,⟨([1],[]),true,([2],[]),false,false,[]⟩),(513,⟨([2],[]),true,([1],[]),false,false,[]⟩),(514,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(515,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 506)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 507)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16117 4 14 (by decide) (by decide)
      · right
        exact rec16119 4 14 (by decide) (by decide)
      · right
        exact rec16121 4 14 (by decide) (by decide)
      · right
        exact rec16123 4 14 (by decide) (by decide)
      · right
        exact rec16125 4 14 (by decide) (by decide)
      · right
        exact rec16127 4 14 (by decide) (by decide)
      · right
        exact rec16129 4 14 (by decide) (by decide)
      · right
        exact rec16131 4 14 (by decide) (by decide)
      · right
        exact rec16133 4 14 (by decide) (by decide)
      · right
        exact rec16135 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 508)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 64)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4713 4 14 (by decide) (by decide)
      · right
        exact rec4719 4 14 (by decide) (by decide)
      · right
        exact rec4725 4 14 (by decide) (by decide)
      · right
        exact rec4731 4 14 (by decide) (by decide)
      · right
        exact rec4737 4 14 (by decide) (by decide)
      · right
        exact rec4743 4 14 (by decide) (by decide)
      · right
        exact rec4749 4 14 (by decide) (by decide)
      · right
        exact rec4755 4 14 (by decide) (by decide)
      · right
        exact rec4761 4 14 (by decide) (by decide)
      · right
        exact rec4767 4 14 (by decide) (by decide)
      · right
        exact rec4773 4 14 (by decide) (by decide)
      · right
        exact rec4779 4 14 (by decide) (by decide)
      · right
        exact rec4785 4 14 (by decide) (by decide)
      · right
        exact rec4791 4 14 (by decide) (by decide)
      · right
        exact rec4797 4 14 (by decide) (by decide)
      · right
        exact rec4803 4 14 (by decide) (by decide)
      · right
        exact rec4809 4 14 (by decide) (by decide)
      · right
        exact rec4815 4 14 (by decide) (by decide)
      · right
        exact rec4821 4 14 (by decide) (by decide)
      · right
        exact rec4827 4 14 (by decide) (by decide)
      · right
        exact rec4833 4 14 (by decide) (by decide)
      · right
        exact rec4839 4 14 (by decide) (by decide)
      · right
        exact rec4845 4 14 (by decide) (by decide)
      · right
        exact rec4851 4 14 (by decide) (by decide)
      · right
        exact rec4857 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 65)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 509)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 510)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16137 4 14 (by decide) (by decide)
      · right
        exact rec16139 4 14 (by decide) (by decide)
      · right
        exact rec16141 4 14 (by decide) (by decide)
      · right
        exact rec16143 4 14 (by decide) (by decide)
      · right
        exact rec16145 4 14 (by decide) (by decide)
      · right
        exact rec16147 4 14 (by decide) (by decide)
      · right
        exact rec16149 4 14 (by decide) (by decide)
      · right
        exact rec16151 4 14 (by decide) (by decide)
      · right
        exact rec16153 4 14 (by decide) (by decide)
      · right
        exact rec16155 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 511)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 69)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4938 4 14 (by decide) (by decide)
      · right
        exact rec4946 4 14 (by decide) (by decide)
      · right
        exact rec4956 4 14 (by decide) (by decide)
      · right
        exact rec4968 4 14 (by decide) (by decide)
      · right
        exact rec4980 4 14 (by decide) (by decide)
      · right
        exact rec4991 4 14 (by decide) (by decide)
      · right
        exact rec4999 4 14 (by decide) (by decide)
      · right
        exact rec5008 4 14 (by decide) (by decide)
      · right
        exact rec5018 4 14 (by decide) (by decide)
      · right
        exact rec5028 4 14 (by decide) (by decide)
      · right
        exact rec5038 4 14 (by decide) (by decide)
      · right
        exact rec5046 4 14 (by decide) (by decide)
      · right
        exact rec5055 4 14 (by decide) (by decide)
      · right
        exact rec5065 4 14 (by decide) (by decide)
      · right
        exact rec5075 4 14 (by decide) (by decide)
      · right
        exact rec5085 4 14 (by decide) (by decide)
      · right
        exact rec5093 4 14 (by decide) (by decide)
      · right
        exact rec5102 4 14 (by decide) (by decide)
      · right
        exact rec5112 4 14 (by decide) (by decide)
      · right
        exact rec5122 4 14 (by decide) (by decide)
      · right
        exact rec5132 4 14 (by decide) (by decide)
      · right
        exact rec5140 4 14 (by decide) (by decide)
      · right
        exact rec5149 4 14 (by decide) (by decide)
      · right
        exact rec5159 4 14 (by decide) (by decide)
      · right
        exact rec5169 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 70)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 71)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 72)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5176 4 14 (by decide) (by decide)
      · right
        exact rec5184 4 14 (by decide) (by decide)
      · right
        exact rec5192 4 14 (by decide) (by decide)
      · right
        exact rec5200 4 14 (by decide) (by decide)
      · right
        exact rec5208 4 14 (by decide) (by decide)
      · right
        exact rec5216 4 14 (by decide) (by decide)
      · right
        exact rec5224 4 14 (by decide) (by decide)
      · right
        exact rec5232 4 14 (by decide) (by decide)
      · right
        exact rec5240 4 14 (by decide) (by decide)
      · right
        exact rec5248 4 14 (by decide) (by decide)
      · right
        exact rec5256 4 14 (by decide) (by decide)
      · right
        exact rec5264 4 14 (by decide) (by decide)
      · right
        exact rec5272 4 14 (by decide) (by decide)
      · right
        exact rec5280 4 14 (by decide) (by decide)
      · right
        exact rec5288 4 14 (by decide) (by decide)
      · right
        exact rec5296 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 73)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 74)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 75)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5307 4 14 (by decide) (by decide)
      · right
        exact rec5317 4 14 (by decide) (by decide)
      · right
        exact rec5327 4 14 (by decide) (by decide)
      · right
        exact rec5337 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 512)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 513)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16157 4 14 (by decide) (by decide)
      · right
        exact rec16159 4 14 (by decide) (by decide)
      · right
        exact rec16161 4 14 (by decide) (by decide)
      · right
        exact rec16163 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 514)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 79)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5439 4 14 (by decide) (by decide)
      · right
        exact rec5442 4 14 (by decide) (by decide)
      · right
        exact rec5446 4 14 (by decide) (by decide)
      · right
        exact rec5453 4 14 (by decide) (by decide)
      · right
        exact rec5456 4 14 (by decide) (by decide)
      · right
        exact rec5459 4 14 (by decide) (by decide)
      · right
        exact rec5463 4 14 (by decide) (by decide)
      · right
        exact rec5470 4 14 (by decide) (by decide)
      · right
        exact rec5473 4 14 (by decide) (by decide)
      · right
        exact rec5476 4 14 (by decide) (by decide)
      · right
        exact rec5479 4 14 (by decide) (by decide)
      · right
        exact rec5484 4 14 (by decide) (by decide)
      · right
        exact rec5487 4 14 (by decide) (by decide)
      · right
        exact rec5490 4 14 (by decide) (by decide)
      · right
        exact rec5493 4 14 (by decide) (by decide)
      · right
        exact rec5496 4 14 (by decide) (by decide)
      · right
        exact rec5499 4 14 (by decide) (by decide)
      · right
        exact rec5502 4 14 (by decide) (by decide)
      · right
        exact rec5506 4 14 (by decide) (by decide)
      · right
        exact rec5510 4 14 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 515)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 81)).length = 10 := by decide +kernel
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
    exact rec4559 4 15 (by decide) (by decide)
end Section14Coverage_4_3_p0_16

#print axioms solution
