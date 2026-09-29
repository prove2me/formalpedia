-- Prove2me | solution 1 for Freiman.section14_s0012_coverage0001_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T03:41:44.325748+00:00
-- url     : https://prove2.me/submissions/ee21f252-2db6-43a1-8576-d55c11ff2587

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
namespace Section14Coverage_12_1_p0_16
private theorem rec415 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([5] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,4,7,8,12,15,16],[5],66⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[415]? = some (⟨16,(-1),[3,4,7,8,12,15,16],[5],66⟩) from rfl))
private theorem rec428 (si parent : ℕ) (hs : si ∈ ([4, 8, 10, 12, 16] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,10,12,16],[8],69⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[428]? = some (⟨16,(-1),[4,8,10,12,16],[8],69⟩) from rfl))
private theorem rec429 (si parent : ℕ) (hs : si ∈ ([4, 8, 10, 12, 16] : List ℕ)) (hp : parent ∈ ([12] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,10,12,16],[12],71⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[429]? = some (⟨16,(-1),[4,8,10,12,16],[12],71⟩) from rfl))
private theorem rec430 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[0],63⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[430]? = some (⟨16,(-1),[4,8,12,16],[0],63⟩) from rfl))
private theorem rec431 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[1],64⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[431]? = some (⟨16,(-1),[4,8,12,16],[1],64⟩) from rfl))
private theorem rec432 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([4] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[4],65⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[432]? = some (⟨16,(-1),[4,8,12,16],[4],65⟩) from rfl))
private theorem rec433 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[9],70⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[433]? = some (⟨16,(-1),[4,8,12,16],[9],70⟩) from rfl))
private theorem rec434 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([13] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[13],72⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[434]? = some (⟨16,(-1),[4,8,12,16],[13],72⟩) from rfl))
private theorem rec435 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[10],205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[435]? = some (⟨16,(-1),[4,8,12,16],[10],205⟩) from rfl))
private theorem rec436 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[11],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[436]? = some (⟨16,(-1),[4,8,12,16],[11],207⟩) from rfl))
private theorem rec437 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([15] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[15],239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[437]? = some (⟨16,(-1),[4,8,12,16],[15],239⟩) from rfl))
private theorem rec438 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([7] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[4,8,12,16],[7],1260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[438]? = some (⟨16,(-1),[4,8,12,16],[7],1260⟩) from rfl))
private theorem rec452 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([14] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[8,12],[14],1398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[452]? = some (⟨16,(-1),[8,12],[14],1398⟩) from rfl))
private theorem rec453 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[8,12],[3],1630⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[453]? = some (⟨16,(-1),[8,12],[3],1630⟩) from rfl))
private theorem rec1380 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[4,8,12,16],[6],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[211]? = some (⟨25,(0),[4,8,12,16],[6],189⟩) from rfl))
private theorem rec1388 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[12],[2],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[219]? = some (⟨25,(0),[12],[2],80⟩) from rfl))
private theorem rec1407 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[8,12],[6],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[238]? = some (⟨25,(1),[8,12],[6],216⟩) from rfl))
private theorem rec1412 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[12],[2],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[243]? = some (⟨25,(1),[12],[2],81⟩) from rfl))
private theorem rec1431 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[8,12],[6],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[262]? = some (⟨25,(2),[8,12],[6],217⟩) from rfl))
private theorem rec1436 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[12],[2],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[267]? = some (⟨25,(2),[12],[2],80⟩) from rfl))
private theorem rec1455 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[8,12],[6],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[286]? = some (⟨25,(3),[8,12],[6],218⟩) from rfl))
private theorem rec1460 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[12],[2],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[291]? = some (⟨25,(3),[12],[2],82⟩) from rfl))
private theorem rec1479 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[8,12],[6],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[310]? = some (⟨25,(4),[8,12],[6],219⟩) from rfl))
private theorem rec1484 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[12],[2],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[315]? = some (⟨25,(4),[12],[2],83⟩) from rfl))
private theorem rec1497 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[4,8,12,16],[6],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[328]? = some (⟨25,(5),[4,8,12,16],[6],189⟩) from rfl))
private theorem rec1505 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[12],[2],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[336]? = some (⟨25,(5),[12],[2],80⟩) from rfl))
private theorem rec1524 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[8,12],[6],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[355]? = some (⟨25,(6),[8,12],[6],216⟩) from rfl))
private theorem rec1529 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[12],[2],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[360]? = some (⟨25,(6),[12],[2],81⟩) from rfl))
private theorem rec1548 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[8,12],[6],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[379]? = some (⟨25,(7),[8,12],[6],217⟩) from rfl))
private theorem rec1553 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[12],[2],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[384]? = some (⟨25,(7),[12],[2],80⟩) from rfl))
private theorem rec1572 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[8,12],[6],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[403]? = some (⟨25,(8),[8,12],[6],218⟩) from rfl))
private theorem rec1577 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[12],[2],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[408]? = some (⟨25,(8),[12],[2],82⟩) from rfl))
private theorem rec1596 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[8,12],[6],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[427]? = some (⟨25,(9),[8,12],[6],219⟩) from rfl))
private theorem rec1601 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[12],[2],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[432]? = some (⟨25,(9),[12],[2],83⟩) from rfl))
private theorem rec1614 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[4,8,12,16],[6],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[445]? = some (⟨25,(10),[4,8,12,16],[6],194⟩) from rfl))
private theorem rec1622 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[12],[2],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[453]? = some (⟨25,(10),[12],[2],84⟩) from rfl))
private theorem rec1641 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[8,12],[6],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[472]? = some (⟨25,(11),[8,12],[6],220⟩) from rfl))
private theorem rec1646 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[12],[2],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[477]? = some (⟨25,(11),[12],[2],84⟩) from rfl))
private theorem rec1665 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[8,12],[6],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[496]? = some (⟨25,(12),[8,12],[6],220⟩) from rfl))
private theorem rec1670 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[12],[2],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[501]? = some (⟨25,(12),[12],[2],84⟩) from rfl))
private theorem rec1689 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[8,12],[6],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[520]? = some (⟨25,(13),[8,12],[6],220⟩) from rfl))
private theorem rec1694 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[12],[2],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[525]? = some (⟨25,(13),[12],[2],84⟩) from rfl))
private theorem rec1713 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[8,12],[6],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[544]? = some (⟨25,(14),[8,12],[6],219⟩) from rfl))
private theorem rec1718 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[12],[2],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[549]? = some (⟨25,(14),[12],[2],83⟩) from rfl))
private theorem rec1731 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[4,8,12,16],[6],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[562]? = some (⟨25,(15),[4,8,12,16],[6],196⟩) from rfl))
private theorem rec1739 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[12],[2],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[570]? = some (⟨25,(15),[12],[2],35⟩) from rfl))
private theorem rec1758 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[8,12],[6],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[589]? = some (⟨25,(16),[8,12],[6],221⟩) from rfl))
private theorem rec1763 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[12],[2],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[594]? = some (⟨25,(16),[12],[2],35⟩) from rfl))
private theorem rec1782 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[8,12],[6],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[613]? = some (⟨25,(17),[8,12],[6],221⟩) from rfl))
private theorem rec1787 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[12],[2],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[618]? = some (⟨25,(17),[12],[2],35⟩) from rfl))
private theorem rec1806 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[8,12],[6],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[637]? = some (⟨25,(18),[8,12],[6],221⟩) from rfl))
private theorem rec1811 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[12],[2],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[642]? = some (⟨25,(18),[12],[2],35⟩) from rfl))
private theorem rec1830 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[8,12],[6],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[661]? = some (⟨25,(19),[8,12],[6],221⟩) from rfl))
private theorem rec1835 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[12],[2],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[666]? = some (⟨25,(19),[12],[2],35⟩) from rfl))
private theorem rec1848 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[4,8,12,16],[6],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[679]? = some (⟨25,(20),[4,8,12,16],[6],198⟩) from rfl))
private theorem rec1856 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[12],[2],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[687]? = some (⟨25,(20),[12],[2],38⟩) from rfl))
private theorem rec1875 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[8,12],[6],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[706]? = some (⟨25,(21),[8,12],[6],222⟩) from rfl))
private theorem rec1880 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[12],[2],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[711]? = some (⟨25,(21),[12],[2],38⟩) from rfl))
private theorem rec1899 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[8,12],[6],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[730]? = some (⟨25,(22),[8,12],[6],222⟩) from rfl))
private theorem rec1904 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[12],[2],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[735]? = some (⟨25,(22),[12],[2],38⟩) from rfl))
private theorem rec1923 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[8,12],[6],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[754]? = some (⟨25,(23),[8,12],[6],222⟩) from rfl))
private theorem rec1928 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[12],[2],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[759]? = some (⟨25,(23),[12],[2],38⟩) from rfl))
private theorem rec1947 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[8,12],[6],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[778]? = some (⟨25,(24),[8,12],[6],222⟩) from rfl))
private theorem rec1952 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[12],[2],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[783]? = some (⟨25,(24),[12],[2],38⟩) from rfl))
private theorem rec2364 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[4,8,12],[6],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1195]? = some (⟨30,(0),[4,8,12],[6],152⟩) from rfl))
private theorem rec2368 (si parent : ℕ) (hs : si ∈ ([11, 12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[11,12],[2],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1199]? = some (⟨30,(0),[11,12],[2],152⟩) from rfl))
private theorem rec2378 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[4,8,12],[6],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1209]? = some (⟨30,(1),[4,8,12],[6],153⟩) from rfl))
private theorem rec2383 (si parent : ℕ) (hs : si ∈ ([11, 12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[11,12],[2],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1214]? = some (⟨30,(1),[11,12],[2],153⟩) from rfl))
private theorem rec2398 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[4,8,12],[6],200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1229]? = some (⟨30,(2),[4,8,12],[6],200⟩) from rfl))
private theorem rec2403 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[12],[2],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1234]? = some (⟨30,(2),[12],[2],92⟩) from rfl))
private theorem rec2422 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[8,12],[6],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1253]? = some (⟨30,(3),[8,12],[6],230⟩) from rfl))
private theorem rec2427 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[12],[2],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1258]? = some (⟨30,(3),[12],[2],93⟩) from rfl))
private theorem rec2446 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[8,12],[6],231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[3]? = some (⟨30,(4),[8,12],[6],231⟩) from rfl))
private theorem rec2451 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[12],[2],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[8]? = some (⟨30,(4),[12],[2],94⟩) from rfl))
private theorem rec2470 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[8,12],[6],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[27]? = some (⟨30,(5),[8,12],[6],230⟩) from rfl))
private theorem rec2475 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[12],[2],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[32]? = some (⟨30,(5),[12],[2],93⟩) from rfl))
private theorem rec2494 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[8,12],[6],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[51]? = some (⟨30,(6),[8,12],[6],232⟩) from rfl))
private theorem rec2499 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[12],[2],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[56]? = some (⟨30,(6),[12],[2],95⟩) from rfl))
private theorem rec2518 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[8,12],[6],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[75]? = some (⟨30,(7),[8,12],[6],232⟩) from rfl))
private theorem rec2523 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[12],[2],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[80]? = some (⟨30,(7),[12],[2],95⟩) from rfl))
private theorem rec2542 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[8,12],[6],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[99]? = some (⟨30,(8),[8,12],[6],233⟩) from rfl))
private theorem rec2547 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[12],[2],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[104]? = some (⟨30,(8),[12],[2],96⟩) from rfl))
private theorem rec2566 (si parent : ℕ) (hs : si ∈ ([8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[8,12],[6],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[123]? = some (⟨30,(9),[8,12],[6],233⟩) from rfl))
private theorem rec2571 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[12],[2],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[128]? = some (⟨30,(9),[12],[2],96⟩) from rfl))
private theorem rec15950 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(0),[4,8,12,16],[6],1250⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1029]? = some (⟨483,(0),[4,8,12,16],[6],1250⟩) from rfl))
private theorem rec15952 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(0),[12],[2],1702⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1031]? = some (⟨483,(0),[12],[2],1702⟩) from rfl))
private theorem rec15953 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(1),[4,8,12,16],[6],1251⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1032]? = some (⟨483,(1),[4,8,12,16],[6],1251⟩) from rfl))
private theorem rec15955 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(1),[12],[2],1703⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1034]? = some (⟨483,(1),[12],[2],1703⟩) from rfl))
private theorem rec15956 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(2),[4,8,12,16],[6],1252⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1035]? = some (⟨483,(2),[4,8,12,16],[6],1252⟩) from rfl))
private theorem rec15958 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(2),[12],[2],1704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1037]? = some (⟨483,(2),[12],[2],1704⟩) from rfl))
private theorem rec15959 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(3),[4,8,12,16],[6],1251⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1038]? = some (⟨483,(3),[4,8,12,16],[6],1251⟩) from rfl))
private theorem rec15961 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(3),[12],[2],1703⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1040]? = some (⟨483,(3),[12],[2],1703⟩) from rfl))
private theorem rec15962 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(4),[4,8,12,16],[6],1253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1041]? = some (⟨483,(4),[4,8,12,16],[6],1253⟩) from rfl))
private theorem rec15964 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(4),[12],[2],1705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1043]? = some (⟨483,(4),[12],[2],1705⟩) from rfl))
private theorem rec15965 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(5),[4,8,12,16],[6],1250⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1044]? = some (⟨483,(5),[4,8,12,16],[6],1250⟩) from rfl))
private theorem rec15967 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(5),[12],[2],1702⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1046]? = some (⟨483,(5),[12],[2],1702⟩) from rfl))
private theorem rec15968 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(6),[4,8,12,16],[6],1251⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1047]? = some (⟨483,(6),[4,8,12,16],[6],1251⟩) from rfl))
private theorem rec15970 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(6),[12],[2],1703⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1049]? = some (⟨483,(6),[12],[2],1703⟩) from rfl))
private theorem rec15971 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(7),[4,8,12,16],[6],1252⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1050]? = some (⟨483,(7),[4,8,12,16],[6],1252⟩) from rfl))
private theorem rec15973 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(7),[12],[2],1704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1052]? = some (⟨483,(7),[12],[2],1704⟩) from rfl))
private theorem rec15974 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(8),[4,8,12,16],[6],1251⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1053]? = some (⟨483,(8),[4,8,12,16],[6],1251⟩) from rfl))
private theorem rec15976 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(8),[12],[2],1703⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1055]? = some (⟨483,(8),[12],[2],1703⟩) from rfl))
private theorem rec15977 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 483 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(9),[4,8,12,16],[6],1253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1056]? = some (⟨483,(9),[4,8,12,16],[6],1253⟩) from rfl))
private theorem rec15979 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 483 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨483,(9),[12],[2],1705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1058]? = some (⟨483,(9),[12],[2],1705⟩) from rfl))
private theorem rec15980 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(0),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1059]? = some (⟨486,(0),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec15982 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(0),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1061]? = some (⟨486,(0),[12],[2],2⟩) from rfl))
private theorem rec15983 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(1),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1062]? = some (⟨486,(1),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec15985 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(1),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1064]? = some (⟨486,(1),[12],[2],2⟩) from rfl))
private theorem rec15986 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(2),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1065]? = some (⟨486,(2),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec15988 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(2),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1067]? = some (⟨486,(2),[12],[2],2⟩) from rfl))
private theorem rec15989 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(3),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1068]? = some (⟨486,(3),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec15991 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(3),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1070]? = some (⟨486,(3),[12],[2],2⟩) from rfl))
private theorem rec15992 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(4),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1071]? = some (⟨486,(4),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec15994 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(4),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1073]? = some (⟨486,(4),[12],[2],2⟩) from rfl))
private theorem rec15995 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(5),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1074]? = some (⟨486,(5),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec15997 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(5),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1076]? = some (⟨486,(5),[12],[2],2⟩) from rfl))
private theorem rec15998 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(6),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1077]? = some (⟨486,(6),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec16000 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(6),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1079]? = some (⟨486,(6),[12],[2],2⟩) from rfl))
private theorem rec16001 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(7),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1080]? = some (⟨486,(7),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec16003 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(7),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1082]? = some (⟨486,(7),[12],[2],2⟩) from rfl))
private theorem rec16004 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(8),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1083]? = some (⟨486,(8),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec16006 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(8),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1085]? = some (⟨486,(8),[12],[2],2⟩) from rfl))
private theorem rec16007 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 486 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(9),[4,8,12,16],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1086]? = some (⟨486,(9),[4,8,12,16],[6],2⟩) from rfl))
private theorem rec16009 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 486 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨486,(9),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1088]? = some (⟨486,(9),[12],[2],2⟩) from rfl))
private theorem rec16011 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(0),[4,8,12],[6],1254⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1090]? = some (⟨489,(0),[4,8,12],[6],1254⟩) from rfl))
private theorem rec16012 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(0),[12],[2],1706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1091]? = some (⟨489,(0),[12],[2],1706⟩) from rfl))
private theorem rec16014 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(1),[4,8,12],[6],1255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1093]? = some (⟨489,(1),[4,8,12],[6],1255⟩) from rfl))
private theorem rec16015 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(1),[12],[2],1707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1094]? = some (⟨489,(1),[12],[2],1707⟩) from rfl))
private theorem rec16017 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(2),[4,8,12],[6],1256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1096]? = some (⟨489,(2),[4,8,12],[6],1256⟩) from rfl))
private theorem rec16018 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(2),[12],[2],1708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1097]? = some (⟨489,(2),[12],[2],1708⟩) from rfl))
private theorem rec16020 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(3),[4,8,12],[6],1255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1099]? = some (⟨489,(3),[4,8,12],[6],1255⟩) from rfl))
private theorem rec16021 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(3),[12],[2],1707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1100]? = some (⟨489,(3),[12],[2],1707⟩) from rfl))
private theorem rec16023 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(4),[4,8,12],[6],1257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1102]? = some (⟨489,(4),[4,8,12],[6],1257⟩) from rfl))
private theorem rec16024 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(4),[12],[2],1709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1103]? = some (⟨489,(4),[12],[2],1709⟩) from rfl))
private theorem rec16026 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(5),[4,8,12],[6],1254⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1105]? = some (⟨489,(5),[4,8,12],[6],1254⟩) from rfl))
private theorem rec16027 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(5),[12],[2],1706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1106]? = some (⟨489,(5),[12],[2],1706⟩) from rfl))
private theorem rec16029 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(6),[4,8,12],[6],1255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1108]? = some (⟨489,(6),[4,8,12],[6],1255⟩) from rfl))
private theorem rec16030 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(6),[12],[2],1707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1109]? = some (⟨489,(6),[12],[2],1707⟩) from rfl))
private theorem rec16032 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(7),[4,8,12],[6],1256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1111]? = some (⟨489,(7),[4,8,12],[6],1256⟩) from rfl))
private theorem rec16033 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(7),[12],[2],1708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1112]? = some (⟨489,(7),[12],[2],1708⟩) from rfl))
private theorem rec16035 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(8),[4,8,12],[6],1255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1114]? = some (⟨489,(8),[4,8,12],[6],1255⟩) from rfl))
private theorem rec16036 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(8),[12],[2],1707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1115]? = some (⟨489,(8),[12],[2],1707⟩) from rfl))
private theorem rec16038 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 489 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(9),[4,8,12],[6],1257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1117]? = some (⟨489,(9),[4,8,12],[6],1257⟩) from rfl))
private theorem rec16039 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 489 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨489,(9),[12],[2],1709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1118]? = some (⟨489,(9),[12],[2],1709⟩) from rfl))
private theorem rec16040 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 492 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨492,(0),[4,8,12,16],[6],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1119]? = some (⟨492,(0),[4,8,12,16],[6],98⟩) from rfl))
private theorem rec16042 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 492 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨492,(0),[12],[2],1266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1121]? = some (⟨492,(0),[12],[2],1266⟩) from rfl))
private theorem rec16043 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 492 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨492,(1),[4,8,12,16],[6],1258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1122]? = some (⟨492,(1),[4,8,12,16],[6],1258⟩) from rfl))
private theorem rec16045 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 492 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨492,(1),[12],[2],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1124]? = some (⟨492,(1),[12],[2],98⟩) from rfl))
private theorem rec16046 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 492 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨492,(2),[4,8,12,16],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1125]? = some (⟨492,(2),[4,8,12,16],[6],3⟩) from rfl))
private theorem rec16048 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 492 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨492,(2),[12],[2],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1127]? = some (⟨492,(2),[12],[2],3⟩) from rfl))
private theorem rec16049 (si parent : ℕ) (hs : si ∈ ([4, 8, 12, 16] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 492 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨492,(3),[4,8,12,16],[6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1128]? = some (⟨492,(3),[4,8,12,16],[6],3⟩) from rfl))
private theorem rec16051 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 492 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨492,(3),[12],[2],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1130]? = some (⟨492,(3),[12],[2],3⟩) from rfl))
private theorem rec16053 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 494 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨494,(0),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1132]? = some (⟨494,(0),[4,8,12],[6],2⟩) from rfl))
private theorem rec16054 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 494 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨494,(0),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1133]? = some (⟨494,(0),[12],[2],2⟩) from rfl))
private theorem rec16056 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 494 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨494,(1),[4,8,12],[6],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1135]? = some (⟨494,(1),[4,8,12],[6],2⟩) from rfl))
private theorem rec16057 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 494 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨494,(1),[12],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1136]? = some (⟨494,(1),[12],[2],2⟩) from rfl))
private theorem rec16059 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 494 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨494,(2),[4,8,12],[6],1259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1138]? = some (⟨494,(2),[4,8,12],[6],1259⟩) from rfl))
private theorem rec16060 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 494 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨494,(2),[12],[2],1710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1139]? = some (⟨494,(2),[12],[2],1710⟩) from rfl))
private theorem rec16062 (si parent : ℕ) (hs : si ∈ ([4, 8, 12] : List ℕ)) (hp : parent ∈ ([6] : List ℕ)) : section14Recorded section14Catalog si parent 494 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨494,(3),[4,8,12],[6],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1141]? = some (⟨494,(3),[4,8,12],[6],101⟩) from rfl))
private theorem rec16063 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 494 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨494,(3),[12],[2],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1142]? = some (⟨494,(3),[12],[2],101⟩) from rfl))
private theorem rec16266 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(0),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[58]? = some (⟨547,(0),[12],[2,6],3⟩) from rfl))
private theorem rec16269 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(1),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[61]? = some (⟨547,(1),[12],[2,6],3⟩) from rfl))
private theorem rec16272 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(2),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[64]? = some (⟨547,(2),[12],[2,6],3⟩) from rfl))
private theorem rec16275 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(3),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[67]? = some (⟨547,(3),[12],[2,6],3⟩) from rfl))
private theorem rec16278 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(4),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[70]? = some (⟨547,(4),[12],[2,6],3⟩) from rfl))
private theorem rec16281 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(5),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[73]? = some (⟨547,(5),[12],[2,6],3⟩) from rfl))
private theorem rec16284 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(6),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[76]? = some (⟨547,(6),[12],[2,6],3⟩) from rfl))
private theorem rec16287 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(7),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[79]? = some (⟨547,(7),[12],[2,6],3⟩) from rfl))
private theorem rec16290 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(8),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[82]? = some (⟨547,(8),[12],[2,6],3⟩) from rfl))
private theorem rec16293 (si parent : ℕ) (hs : si ∈ ([12] : List ℕ)) (hp : parent ∈ ([2, 6] : List ℕ)) : section14Recorded section14Catalog si parent 547 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(9),[12],[2,6],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[85]? = some (⟨547,(9),[12],[2,6],3⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 12).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 12)).drop 0).take 16, section14Recorded section14Catalog 12 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 12 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 12).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(613,⟨([1],[]),true,([1],[]),false,false,[]⟩),(483,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(484,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(548,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(485,⟨([2],[]),true,([2],[]),false,false,[]⟩),(486,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(487,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(488,⟨([3],[]),true,([3],[]),false,false,[]⟩),(489,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(490,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(614,⟨([1],[]),true,([2],[]),false,false,[]⟩),(492,⟨([2],[]),true,([1],[]),false,false,[]⟩),(493,⟨([2],[]),true,([3],[]),false,false,[]⟩),(494,⟨([3],[]),true,([2],[]),false,false,[]⟩),(615,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec430 12 0 (by decide) (by decide)
  · left
    exact rec431 12 1 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(613,⟨([1],[]),true,([1],[]),false,false,[]⟩),(483,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(484,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(548,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(485,⟨([2],[]),true,([2],[]),false,false,[]⟩),(486,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(487,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(488,⟨([3],[]),true,([3],[]),false,false,[]⟩),(489,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(490,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(614,⟨([1],[]),true,([2],[]),false,false,[]⟩),(492,⟨([2],[]),true,([1],[]),false,false,[]⟩),(493,⟨([2],[]),true,([3],[]),false,false,[]⟩),(494,⟨([3],[]),true,([2],[]),false,false,[]⟩),(615,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 613)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 483)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15952 12 2 (by decide) (by decide)
      · right
        exact rec15955 12 2 (by decide) (by decide)
      · right
        exact rec15958 12 2 (by decide) (by decide)
      · right
        exact rec15961 12 2 (by decide) (by decide)
      · right
        exact rec15964 12 2 (by decide) (by decide)
      · right
        exact rec15967 12 2 (by decide) (by decide)
      · right
        exact rec15970 12 2 (by decide) (by decide)
      · right
        exact rec15973 12 2 (by decide) (by decide)
      · right
        exact rec15976 12 2 (by decide) (by decide)
      · right
        exact rec15979 12 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 484)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 547)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16266 12 2 (by decide) (by decide)
      · right
        exact rec16269 12 2 (by decide) (by decide)
      · right
        exact rec16272 12 2 (by decide) (by decide)
      · right
        exact rec16275 12 2 (by decide) (by decide)
      · right
        exact rec16278 12 2 (by decide) (by decide)
      · right
        exact rec16281 12 2 (by decide) (by decide)
      · right
        exact rec16284 12 2 (by decide) (by decide)
      · right
        exact rec16287 12 2 (by decide) (by decide)
      · right
        exact rec16290 12 2 (by decide) (by decide)
      · right
        exact rec16293 12 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 548)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 485)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 486)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15982 12 2 (by decide) (by decide)
      · right
        exact rec15985 12 2 (by decide) (by decide)
      · right
        exact rec15988 12 2 (by decide) (by decide)
      · right
        exact rec15991 12 2 (by decide) (by decide)
      · right
        exact rec15994 12 2 (by decide) (by decide)
      · right
        exact rec15997 12 2 (by decide) (by decide)
      · right
        exact rec16000 12 2 (by decide) (by decide)
      · right
        exact rec16003 12 2 (by decide) (by decide)
      · right
        exact rec16006 12 2 (by decide) (by decide)
      · right
        exact rec16009 12 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 487)).length = 10 := by decide +kernel
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
        exact rec1388 12 2 (by decide) (by decide)
      · right
        exact rec1412 12 2 (by decide) (by decide)
      · right
        exact rec1436 12 2 (by decide) (by decide)
      · right
        exact rec1460 12 2 (by decide) (by decide)
      · right
        exact rec1484 12 2 (by decide) (by decide)
      · right
        exact rec1505 12 2 (by decide) (by decide)
      · right
        exact rec1529 12 2 (by decide) (by decide)
      · right
        exact rec1553 12 2 (by decide) (by decide)
      · right
        exact rec1577 12 2 (by decide) (by decide)
      · right
        exact rec1601 12 2 (by decide) (by decide)
      · right
        exact rec1622 12 2 (by decide) (by decide)
      · right
        exact rec1646 12 2 (by decide) (by decide)
      · right
        exact rec1670 12 2 (by decide) (by decide)
      · right
        exact rec1694 12 2 (by decide) (by decide)
      · right
        exact rec1718 12 2 (by decide) (by decide)
      · right
        exact rec1739 12 2 (by decide) (by decide)
      · right
        exact rec1763 12 2 (by decide) (by decide)
      · right
        exact rec1787 12 2 (by decide) (by decide)
      · right
        exact rec1811 12 2 (by decide) (by decide)
      · right
        exact rec1835 12 2 (by decide) (by decide)
      · right
        exact rec1856 12 2 (by decide) (by decide)
      · right
        exact rec1880 12 2 (by decide) (by decide)
      · right
        exact rec1904 12 2 (by decide) (by decide)
      · right
        exact rec1928 12 2 (by decide) (by decide)
      · right
        exact rec1952 12 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 26)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 488)).length = 1 := by decide +kernel
      have hjj : j < 1 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 489)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16012 12 2 (by decide) (by decide)
      · right
        exact rec16015 12 2 (by decide) (by decide)
      · right
        exact rec16018 12 2 (by decide) (by decide)
      · right
        exact rec16021 12 2 (by decide) (by decide)
      · right
        exact rec16024 12 2 (by decide) (by decide)
      · right
        exact rec16027 12 2 (by decide) (by decide)
      · right
        exact rec16030 12 2 (by decide) (by decide)
      · right
        exact rec16033 12 2 (by decide) (by decide)
      · right
        exact rec16036 12 2 (by decide) (by decide)
      · right
        exact rec16039 12 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 490)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 30)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2368 12 2 (by decide) (by decide)
      · right
        exact rec2383 12 2 (by decide) (by decide)
      · right
        exact rec2403 12 2 (by decide) (by decide)
      · right
        exact rec2427 12 2 (by decide) (by decide)
      · right
        exact rec2451 12 2 (by decide) (by decide)
      · right
        exact rec2475 12 2 (by decide) (by decide)
      · right
        exact rec2499 12 2 (by decide) (by decide)
      · right
        exact rec2523 12 2 (by decide) (by decide)
      · right
        exact rec2547 12 2 (by decide) (by decide)
      · right
        exact rec2571 12 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 31)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 614)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 492)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16042 12 2 (by decide) (by decide)
      · right
        exact rec16045 12 2 (by decide) (by decide)
      · right
        exact rec16048 12 2 (by decide) (by decide)
      · right
        exact rec16051 12 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 493)).length = 1 := by decide +kernel
      have hjj : j < 1 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 494)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16054 12 2 (by decide) (by decide)
      · right
        exact rec16057 12 2 (by decide) (by decide)
      · right
        exact rec16060 12 2 (by decide) (by decide)
      · right
        exact rec16063 12 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 615)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 37)).length = 5 := by decide +kernel
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
  · left
    exact rec453 12 3 (by decide) (by decide)
  · left
    exact rec432 12 4 (by decide) (by decide)
  · left
    exact rec415 12 5 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(613,⟨([1],[]),true,([1],[]),false,false,[]⟩),(483,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(484,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(548,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(485,⟨([2],[]),true,([2],[]),false,false,[]⟩),(486,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(487,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(488,⟨([3],[]),true,([3],[]),false,false,[]⟩),(489,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(490,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(614,⟨([1],[]),true,([2],[]),false,false,[]⟩),(492,⟨([2],[]),true,([1],[]),false,false,[]⟩),(493,⟨([2],[]),true,([3],[]),false,false,[]⟩),(494,⟨([3],[]),true,([2],[]),false,false,[]⟩),(615,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 613)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 483)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15950 12 6 (by decide) (by decide)
      · right
        exact rec15953 12 6 (by decide) (by decide)
      · right
        exact rec15956 12 6 (by decide) (by decide)
      · right
        exact rec15959 12 6 (by decide) (by decide)
      · right
        exact rec15962 12 6 (by decide) (by decide)
      · right
        exact rec15965 12 6 (by decide) (by decide)
      · right
        exact rec15968 12 6 (by decide) (by decide)
      · right
        exact rec15971 12 6 (by decide) (by decide)
      · right
        exact rec15974 12 6 (by decide) (by decide)
      · right
        exact rec15977 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 484)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 547)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16266 12 6 (by decide) (by decide)
      · right
        exact rec16269 12 6 (by decide) (by decide)
      · right
        exact rec16272 12 6 (by decide) (by decide)
      · right
        exact rec16275 12 6 (by decide) (by decide)
      · right
        exact rec16278 12 6 (by decide) (by decide)
      · right
        exact rec16281 12 6 (by decide) (by decide)
      · right
        exact rec16284 12 6 (by decide) (by decide)
      · right
        exact rec16287 12 6 (by decide) (by decide)
      · right
        exact rec16290 12 6 (by decide) (by decide)
      · right
        exact rec16293 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 548)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 485)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 486)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15980 12 6 (by decide) (by decide)
      · right
        exact rec15983 12 6 (by decide) (by decide)
      · right
        exact rec15986 12 6 (by decide) (by decide)
      · right
        exact rec15989 12 6 (by decide) (by decide)
      · right
        exact rec15992 12 6 (by decide) (by decide)
      · right
        exact rec15995 12 6 (by decide) (by decide)
      · right
        exact rec15998 12 6 (by decide) (by decide)
      · right
        exact rec16001 12 6 (by decide) (by decide)
      · right
        exact rec16004 12 6 (by decide) (by decide)
      · right
        exact rec16007 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 487)).length = 10 := by decide +kernel
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
        exact rec1380 12 6 (by decide) (by decide)
      · right
        exact rec1407 12 6 (by decide) (by decide)
      · right
        exact rec1431 12 6 (by decide) (by decide)
      · right
        exact rec1455 12 6 (by decide) (by decide)
      · right
        exact rec1479 12 6 (by decide) (by decide)
      · right
        exact rec1497 12 6 (by decide) (by decide)
      · right
        exact rec1524 12 6 (by decide) (by decide)
      · right
        exact rec1548 12 6 (by decide) (by decide)
      · right
        exact rec1572 12 6 (by decide) (by decide)
      · right
        exact rec1596 12 6 (by decide) (by decide)
      · right
        exact rec1614 12 6 (by decide) (by decide)
      · right
        exact rec1641 12 6 (by decide) (by decide)
      · right
        exact rec1665 12 6 (by decide) (by decide)
      · right
        exact rec1689 12 6 (by decide) (by decide)
      · right
        exact rec1713 12 6 (by decide) (by decide)
      · right
        exact rec1731 12 6 (by decide) (by decide)
      · right
        exact rec1758 12 6 (by decide) (by decide)
      · right
        exact rec1782 12 6 (by decide) (by decide)
      · right
        exact rec1806 12 6 (by decide) (by decide)
      · right
        exact rec1830 12 6 (by decide) (by decide)
      · right
        exact rec1848 12 6 (by decide) (by decide)
      · right
        exact rec1875 12 6 (by decide) (by decide)
      · right
        exact rec1899 12 6 (by decide) (by decide)
      · right
        exact rec1923 12 6 (by decide) (by decide)
      · right
        exact rec1947 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 26)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 488)).length = 1 := by decide +kernel
      have hjj : j < 1 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 489)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16011 12 6 (by decide) (by decide)
      · right
        exact rec16014 12 6 (by decide) (by decide)
      · right
        exact rec16017 12 6 (by decide) (by decide)
      · right
        exact rec16020 12 6 (by decide) (by decide)
      · right
        exact rec16023 12 6 (by decide) (by decide)
      · right
        exact rec16026 12 6 (by decide) (by decide)
      · right
        exact rec16029 12 6 (by decide) (by decide)
      · right
        exact rec16032 12 6 (by decide) (by decide)
      · right
        exact rec16035 12 6 (by decide) (by decide)
      · right
        exact rec16038 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 490)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 30)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2364 12 6 (by decide) (by decide)
      · right
        exact rec2378 12 6 (by decide) (by decide)
      · right
        exact rec2398 12 6 (by decide) (by decide)
      · right
        exact rec2422 12 6 (by decide) (by decide)
      · right
        exact rec2446 12 6 (by decide) (by decide)
      · right
        exact rec2470 12 6 (by decide) (by decide)
      · right
        exact rec2494 12 6 (by decide) (by decide)
      · right
        exact rec2518 12 6 (by decide) (by decide)
      · right
        exact rec2542 12 6 (by decide) (by decide)
      · right
        exact rec2566 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 31)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 614)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 492)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16040 12 6 (by decide) (by decide)
      · right
        exact rec16043 12 6 (by decide) (by decide)
      · right
        exact rec16046 12 6 (by decide) (by decide)
      · right
        exact rec16049 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 493)).length = 1 := by decide +kernel
      have hjj : j < 1 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 494)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16053 12 6 (by decide) (by decide)
      · right
        exact rec16056 12 6 (by decide) (by decide)
      · right
        exact rec16059 12 6 (by decide) (by decide)
      · right
        exact rec16062 12 6 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 615)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 37)).length = 5 := by decide +kernel
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
  · left
    exact rec438 12 7 (by decide) (by decide)
  · left
    exact rec428 12 8 (by decide) (by decide)
  · left
    exact rec433 12 9 (by decide) (by decide)
  · left
    exact rec435 12 10 (by decide) (by decide)
  · left
    exact rec436 12 11 (by decide) (by decide)
  · left
    exact rec429 12 12 (by decide) (by decide)
  · left
    exact rec434 12 13 (by decide) (by decide)
  · left
    exact rec452 12 14 (by decide) (by decide)
  · left
    exact rec437 12 15 (by decide) (by decide)
end Section14Coverage_12_1_p0_16

#print axioms solution
