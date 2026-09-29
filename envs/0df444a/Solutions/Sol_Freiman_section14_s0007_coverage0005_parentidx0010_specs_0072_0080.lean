-- Prove2me | solution 1 for Freiman.section14_s0007_coverage0005_parentidx0010_specs_0072_0080
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:36:15.939338+00:00
-- url     : https://prove2.me/submissions/a1d83db5-1b6b-4185-b4c8-f663b545af86

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
namespace Section14CoverageSpec_7_5_p10_72_80
private theorem rec11505 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(0),[7],[10],1616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[776]? = some (⟨226,(0),[7],[10],1616⟩) from rfl))
private theorem rec11509 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[780]? = some (⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩) from rfl))
private theorem rec11515 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[786]? = some (⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩) from rfl))
private theorem rec11521 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[792]? = some (⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩) from rfl))
private theorem rec11527 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[798]? = some (⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩) from rfl))
private theorem rec11533 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[804]? = some (⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩) from rfl))
private theorem rec11539 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[810]? = some (⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩) from rfl))
private theorem rec11545 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(7),[3,4,7,8,12,15,16],[10],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[816]? = some (⟨226,(7),[3,4,7,8,12,15,16],[10],771⟩) from rfl))
private theorem rec11551 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(8),[3,4,7,8,12,15,16],[10],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[822]? = some (⟨226,(8),[3,4,7,8,12,15,16],[10],772⟩) from rfl))
private theorem rec11557 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 226 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(9),[3,4,7,8,12,15,16],[10],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[828]? = some (⟨226,(9),[3,4,7,8,12,15,16],[10],772⟩) from rfl))
private theorem rec11563 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(0),[3,4,7,8,12,15,16],[10],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[834]? = some (⟨227,(0),[3,4,7,8,12,15,16],[10],773⟩) from rfl))
private theorem rec11569 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(1),[3,4,7,8,12,15,16],[10],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[840]? = some (⟨227,(1),[3,4,7,8,12,15,16],[10],774⟩) from rfl))
private theorem rec11576 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(2),[3,7,15],[10],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[847]? = some (⟨227,(2),[3,7,15],[10],775⟩) from rfl))
private theorem rec11583 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(3),[3,4,7,8,12,15,16],[10],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[854]? = some (⟨227,(3),[3,4,7,8,12,15,16],[10],776⟩) from rfl))
private theorem rec11590 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(4),[3,7,15],[10],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[861]? = some (⟨227,(4),[3,7,15],[10],775⟩) from rfl))
private theorem rec11597 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(5),[3,4,7,8,12,15,16],[10],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[868]? = some (⟨227,(5),[3,4,7,8,12,15,16],[10],773⟩) from rfl))
private theorem rec11603 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(6),[3,4,7,8,12,15,16],[10],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[874]? = some (⟨227,(6),[3,4,7,8,12,15,16],[10],774⟩) from rfl))
private theorem rec11610 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(7),[3,7,15],[10],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[881]? = some (⟨227,(7),[3,7,15],[10],775⟩) from rfl))
private theorem rec11617 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(8),[3,4,7,8,12,15,16],[10],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[888]? = some (⟨227,(8),[3,4,7,8,12,15,16],[10],776⟩) from rfl))
private theorem rec11624 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(9),[3,7,15],[10],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[895]? = some (⟨227,(9),[3,7,15],[10],775⟩) from rfl))
private theorem rec11631 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(10),[3,4,7,8,12,15,16],[10],777⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[902]? = some (⟨227,(10),[3,4,7,8,12,15,16],[10],777⟩) from rfl))
private theorem rec11637 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(11),[3,4,7,8,12,15,16],[10],778⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[908]? = some (⟨227,(11),[3,4,7,8,12,15,16],[10],778⟩) from rfl))
private theorem rec11644 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(12),[3,7,15],[10],779⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[915]? = some (⟨227,(12),[3,7,15],[10],779⟩) from rfl))
private theorem rec11651 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(13),[3,4,7,8,12,15,16],[10],780⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[922]? = some (⟨227,(13),[3,4,7,8,12,15,16],[10],780⟩) from rfl))
private theorem rec11658 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(14),[3,7,15],[10],779⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[929]? = some (⟨227,(14),[3,7,15],[10],779⟩) from rfl))
private theorem rec11665 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(15),[3,4,7,8,12,15,16],[10],781⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[936]? = some (⟨227,(15),[3,4,7,8,12,15,16],[10],781⟩) from rfl))
private theorem rec11671 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(16),[3,4,7,8,12,15,16],[10],782⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[942]? = some (⟨227,(16),[3,4,7,8,12,15,16],[10],782⟩) from rfl))
private theorem rec11678 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(17),[3,7,15],[10],783⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[949]? = some (⟨227,(17),[3,7,15],[10],783⟩) from rfl))
private theorem rec11685 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(18),[3,4,7,8,12,15,16],[10],784⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[956]? = some (⟨227,(18),[3,4,7,8,12,15,16],[10],784⟩) from rfl))
private theorem rec11692 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(19),[3,7,15],[10],783⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[963]? = some (⟨227,(19),[3,7,15],[10],783⟩) from rfl))
private theorem rec11699 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(20),[3,4,7,8,12,15,16],[10],785⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[970]? = some (⟨227,(20),[3,4,7,8,12,15,16],[10],785⟩) from rfl))
private theorem rec11705 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(21),[3,4,7,8,12,15,16],[10],786⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[976]? = some (⟨227,(21),[3,4,7,8,12,15,16],[10],786⟩) from rfl))
private theorem rec11712 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(22),[3,7,15],[10],787⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[983]? = some (⟨227,(22),[3,7,15],[10],787⟩) from rfl))
private theorem rec11719 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(23),[3,4,7,8,12,15,16],[10],788⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[990]? = some (⟨227,(23),[3,4,7,8,12,15,16],[10],788⟩) from rfl))
private theorem rec11726 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 227 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(24),[3,7,15],[10],787⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[997]? = some (⟨227,(24),[3,7,15],[10],787⟩) from rfl))
private theorem rec11736 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(0),[7],[10],1617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1007]? = some (⟨228,(0),[7],[10],1617⟩) from rfl))
private theorem rec11743 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(1),[7],[10],1618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1014]? = some (⟨228,(1),[7],[10],1618⟩) from rfl))
private theorem rec11753 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(2),[7],[10],1619⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1024]? = some (⟨228,(2),[7],[10],1619⟩) from rfl))
private theorem rec11760 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(3),[7],[10],1620⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1031]? = some (⟨228,(3),[7],[10],1620⟩) from rfl))
private theorem rec11764 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(4),[3,4,7,8,12,15,16],[10],793⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1035]? = some (⟨228,(4),[3,4,7,8,12,15,16],[10],793⟩) from rfl))
private theorem rec11770 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(5),[3,4,7,8,12,15,16],[10],794⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1041]? = some (⟨228,(5),[3,4,7,8,12,15,16],[10],794⟩) from rfl))
private theorem rec11776 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(6),[3,4,7,8,12,15,16],[10],795⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1047]? = some (⟨228,(6),[3,4,7,8,12,15,16],[10],795⟩) from rfl))
private theorem rec11782 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(7),[3,4,7,8,12,15,16],[10],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1053]? = some (⟨228,(7),[3,4,7,8,12,15,16],[10],796⟩) from rfl))
private theorem rec11788 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(8),[3,4,7,8,12,15,16],[10],797⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1059]? = some (⟨228,(8),[3,4,7,8,12,15,16],[10],797⟩) from rfl))
private theorem rec11794 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(9),[3,4,7,15,16],[10],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1065]? = some (⟨228,(9),[3,4,7,15,16],[10],796⟩) from rfl))
private theorem rec11801 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(10),[3,4,7,8,12,15,16],[10],798⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1072]? = some (⟨228,(10),[3,4,7,8,12,15,16],[10],798⟩) from rfl))
private theorem rec11807 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(11),[3,4,7,8,12,15,16],[10],799⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1078]? = some (⟨228,(11),[3,4,7,8,12,15,16],[10],799⟩) from rfl))
private theorem rec11813 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(12),[3,4,7,8,12,15,16],[10],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1084]? = some (⟨228,(12),[3,4,7,8,12,15,16],[10],800⟩) from rfl))
private theorem rec11819 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(13),[3,4,7,8,12,15,16],[10],801⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1090]? = some (⟨228,(13),[3,4,7,8,12,15,16],[10],801⟩) from rfl))
private theorem rec11825 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(14),[3,4,7,8,12,15,16],[10],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1096]? = some (⟨228,(14),[3,4,7,8,12,15,16],[10],800⟩) from rfl))
private theorem rec11831 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(15),[3,4,7,8,12,15,16],[10],802⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1102]? = some (⟨228,(15),[3,4,7,8,12,15,16],[10],802⟩) from rfl))
private theorem rec11837 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(16),[3,4,7,8,12,15,16],[10],803⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1108]? = some (⟨228,(16),[3,4,7,8,12,15,16],[10],803⟩) from rfl))
private theorem rec11843 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(17),[3,4,7,8,12,15,16],[10],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1114]? = some (⟨228,(17),[3,4,7,8,12,15,16],[10],804⟩) from rfl))
private theorem rec11849 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(18),[3,4,7,8,12,15,16],[10],805⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1120]? = some (⟨228,(18),[3,4,7,8,12,15,16],[10],805⟩) from rfl))
private theorem rec11855 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(19),[3,4,7,8,12,15,16],[10],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1126]? = some (⟨228,(19),[3,4,7,8,12,15,16],[10],804⟩) from rfl))
private theorem rec11861 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(20),[3,4,7,8,12,15,16],[10],806⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1132]? = some (⟨228,(20),[3,4,7,8,12,15,16],[10],806⟩) from rfl))
private theorem rec11867 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(21),[3,4,7,8,12,15,16],[10],807⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1138]? = some (⟨228,(21),[3,4,7,8,12,15,16],[10],807⟩) from rfl))
private theorem rec11873 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(22),[3,4,7,8,12,15,16],[10],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1144]? = some (⟨228,(22),[3,4,7,8,12,15,16],[10],808⟩) from rfl))
private theorem rec11879 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(23),[3,4,7,8,12,15,16],[10],809⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1150]? = some (⟨228,(23),[3,4,7,8,12,15,16],[10],809⟩) from rfl))
private theorem rec11885 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 228 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(24),[3,4,7,8,12,15,16],[10],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1156]? = some (⟨228,(24),[3,4,7,8,12,15,16],[10],808⟩) from rfl))
private theorem rec11891 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(0),[3,4,7,8,12,15,16],[10],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1162]? = some (⟨230,(0),[3,4,7,8,12,15,16],[10],810⟩) from rfl))
private theorem rec11897 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(1),[3,4,7,8,15,16],[10],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1168]? = some (⟨230,(1),[3,4,7,8,15,16],[10],811⟩) from rfl))
private theorem rec11904 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(2),[3,4,7,8,12,15,16],[10],812⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1175]? = some (⟨230,(2),[3,4,7,8,12,15,16],[10],812⟩) from rfl))
private theorem rec11910 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(3),[3,4,7,8,12,15,16],[10],813⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1181]? = some (⟨230,(3),[3,4,7,8,12,15,16],[10],813⟩) from rfl))
private theorem rec11916 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(4),[3,4,7,8,12,15,16],[10],814⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1187]? = some (⟨230,(4),[3,4,7,8,12,15,16],[10],814⟩) from rfl))
private theorem rec11922 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(5),[3,4,7,8,12,15,16],[10],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1193]? = some (⟨230,(5),[3,4,7,8,12,15,16],[10],810⟩) from rfl))
private theorem rec11928 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(6),[3,4,7,8,15,16],[10],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1199]? = some (⟨230,(6),[3,4,7,8,15,16],[10],811⟩) from rfl))
private theorem rec11937 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(7),[3,7,15],[10],922⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[8]? = some (⟨230,(7),[3,7,15],[10],922⟩) from rfl))
private theorem rec11944 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(8),[3,4,7,8,12,15,16],[10],816⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[15]? = some (⟨230,(8),[3,4,7,8,12,15,16],[10],816⟩) from rfl))
private theorem rec11951 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(9),[3,7,15],[10],817⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[22]? = some (⟨230,(9),[3,7,15],[10],817⟩) from rfl))
private theorem rec11959 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(10),[3,4,7,8,12,15,16],[10],818⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[30]? = some (⟨230,(10),[3,4,7,8,12,15,16],[10],818⟩) from rfl))
private theorem rec11965 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(11),[3,4,7,8,12,15,16],[10],819⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[36]? = some (⟨230,(11),[3,4,7,8,12,15,16],[10],819⟩) from rfl))
private theorem rec11973 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(12),[3,7,15],[10],923⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[44]? = some (⟨230,(12),[3,7,15],[10],923⟩) from rfl))
private theorem rec11979 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(13),[3,4,7,8,12,15,16],[10],821⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[50]? = some (⟨230,(13),[3,4,7,8,12,15,16],[10],821⟩) from rfl))
private theorem rec11986 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(14),[3,7,15],[10],817⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[57]? = some (⟨230,(14),[3,7,15],[10],817⟩) from rfl))
private theorem rec11994 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[65]? = some (⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩) from rfl))
private theorem rec12000 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[71]? = some (⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩) from rfl))
private theorem rec12007 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(17),[3,7,15],[10],824⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[78]? = some (⟨230,(17),[3,7,15],[10],824⟩) from rfl))
private theorem rec12014 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[85]? = some (⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩) from rfl))
private theorem rec12021 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(19),[3,7,15],[10],824⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[92]? = some (⟨230,(19),[3,7,15],[10],824⟩) from rfl))
private theorem rec12028 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[99]? = some (⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩) from rfl))
private theorem rec12034 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[105]? = some (⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩) from rfl))
private theorem rec12041 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(22),[3,7,15],[10],828⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[112]? = some (⟨230,(22),[3,7,15],[10],828⟩) from rfl))
private theorem rec12048 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[119]? = some (⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩) from rfl))
private theorem rec12055 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 230 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(24),[3,7,15],[10],828⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[126]? = some (⟨230,(24),[3,7,15],[10],828⟩) from rfl))
private theorem rec12065 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(0),[7],[10],1621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[136]? = some (⟨231,(0),[7],[10],1621⟩) from rfl))
private theorem rec12069 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(1),[3,4,7,15,16],[10],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[140]? = some (⟨231,(1),[3,4,7,15,16],[10],831⟩) from rfl))
private theorem rec12077 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(2),[3,4,7,8,12,15,16],[10],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[148]? = some (⟨231,(2),[3,4,7,8,12,15,16],[10],832⟩) from rfl))
private theorem rec12083 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(3),[3,4,7,8,12,15,16],[10],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[154]? = some (⟨231,(3),[3,4,7,8,12,15,16],[10],833⟩) from rfl))
private theorem rec12092 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(4),[7],[10],1621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[163]? = some (⟨231,(4),[7],[10],1621⟩) from rfl))
private theorem rec12096 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(5),[3,4,7,15,16],[10],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[167]? = some (⟨231,(5),[3,4,7,15,16],[10],831⟩) from rfl))
private theorem rec12104 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(6),[3,4,7,8,12,15,16],[10],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[175]? = some (⟨231,(6),[3,4,7,8,12,15,16],[10],832⟩) from rfl))
private theorem rec12110 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(7),[3,4,7,8,12,15,16],[10],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[181]? = some (⟨231,(7),[3,4,7,8,12,15,16],[10],833⟩) from rfl))
private theorem rec12116 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(8),[3,4,7,8,12,15,16],[10],834⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[187]? = some (⟨231,(8),[3,4,7,8,12,15,16],[10],834⟩) from rfl))
private theorem rec12122 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(9),[3,4,7,8,12,15,16],[10],835⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[193]? = some (⟨231,(9),[3,4,7,8,12,15,16],[10],835⟩) from rfl))
private theorem rec12128 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(10),[3,4,7,8,12,15,16],[10],836⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[199]? = some (⟨231,(10),[3,4,7,8,12,15,16],[10],836⟩) from rfl))
private theorem rec12134 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(11),[3,4,7,8,12,15,16],[10],837⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[205]? = some (⟨231,(11),[3,4,7,8,12,15,16],[10],837⟩) from rfl))
private theorem rec12140 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(12),[3,4,7,8,12,15,16],[10],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[211]? = some (⟨231,(12),[3,4,7,8,12,15,16],[10],838⟩) from rfl))
private theorem rec12146 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(13),[3,4,7,8,12,15,16],[10],839⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[217]? = some (⟨231,(13),[3,4,7,8,12,15,16],[10],839⟩) from rfl))
private theorem rec12152 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(14),[3,4,7,8,12,15,16],[10],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[223]? = some (⟨231,(14),[3,4,7,8,12,15,16],[10],838⟩) from rfl))
private theorem rec12158 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(15),[3,4,7,8,12,15,16],[10],840⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[229]? = some (⟨231,(15),[3,4,7,8,12,15,16],[10],840⟩) from rfl))
private theorem rec12164 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(16),[3,4,7,8,12,15,16],[10],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[235]? = some (⟨231,(16),[3,4,7,8,12,15,16],[10],841⟩) from rfl))
private theorem rec12170 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(17),[3,4,7,8,12,15,16],[10],842⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[241]? = some (⟨231,(17),[3,4,7,8,12,15,16],[10],842⟩) from rfl))
private theorem rec12176 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(18),[3,4,7,8,12,15,16],[10],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[247]? = some (⟨231,(18),[3,4,7,8,12,15,16],[10],841⟩) from rfl))
private theorem rec12182 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 231 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(19),[3,4,7,8,12,15,16],[10],843⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[253]? = some (⟨231,(19),[3,4,7,8,12,15,16],[10],843⟩) from rfl))
private theorem rec12188 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(0),[3,4,7,8,12,15,16],[10],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[259]? = some (⟨232,(0),[3,4,7,8,12,15,16],[10],844⟩) from rfl))
private theorem rec12194 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(1),[3,4,7,8,12,15,16],[10],845⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[265]? = some (⟨232,(1),[3,4,7,8,12,15,16],[10],845⟩) from rfl))
private theorem rec12201 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(2),[3,4,7,8,12,15,16],[10],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[272]? = some (⟨232,(2),[3,4,7,8,12,15,16],[10],846⟩) from rfl))
private theorem rec12207 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(3),[3,4,7,8,12,15,16],[10],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[278]? = some (⟨232,(3),[3,4,7,8,12,15,16],[10],847⟩) from rfl))
private theorem rec12215 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(4),[3,7,15],[10],855⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[286]? = some (⟨232,(4),[3,7,15],[10],855⟩) from rfl))
private theorem rec12221 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(5),[3,4,7,8,12,15,16],[10],849⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[292]? = some (⟨232,(5),[3,4,7,8,12,15,16],[10],849⟩) from rfl))
private theorem rec12227 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(6),[3,4,7,8,12,15,16],[10],850⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[298]? = some (⟨232,(6),[3,4,7,8,12,15,16],[10],850⟩) from rfl))
private theorem rec12234 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(7),[3,4,7,8,12,15,16],[10],851⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[305]? = some (⟨232,(7),[3,4,7,8,12,15,16],[10],851⟩) from rfl))
private theorem rec12240 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(8),[3,4,7,8,12,15,16],[10],852⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[311]? = some (⟨232,(8),[3,4,7,8,12,15,16],[10],852⟩) from rfl))
private theorem rec12247 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(9),[3,7,15],[10],853⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[318]? = some (⟨232,(9),[3,7,15],[10],853⟩) from rfl))
private theorem rec12254 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(10),[3,4,7,8,12,15,16],[10],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[325]? = some (⟨232,(10),[3,4,7,8,12,15,16],[10],844⟩) from rfl))
private theorem rec12260 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(11),[3,4,7,8,12,15,16],[10],854⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[331]? = some (⟨232,(11),[3,4,7,8,12,15,16],[10],854⟩) from rfl))
private theorem rec12267 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(12),[3,4,7,8,12,15,16],[10],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[338]? = some (⟨232,(12),[3,4,7,8,12,15,16],[10],846⟩) from rfl))
private theorem rec12273 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(13),[3,4,7,8,12,15,16],[10],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[344]? = some (⟨232,(13),[3,4,7,8,12,15,16],[10],847⟩) from rfl))
private theorem rec12280 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(14),[3,7,15],[10],855⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[351]? = some (⟨232,(14),[3,7,15],[10],855⟩) from rfl))
private theorem rec12287 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(15),[3,4,7,8,12,15,16],[10],856⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[358]? = some (⟨232,(15),[3,4,7,8,12,15,16],[10],856⟩) from rfl))
private theorem rec12293 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(16),[3,4,7,8,12,15,16],[10],857⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[364]? = some (⟨232,(16),[3,4,7,8,12,15,16],[10],857⟩) from rfl))
private theorem rec12300 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(17),[3,4,7,8,12,15,16],[10],858⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[371]? = some (⟨232,(17),[3,4,7,8,12,15,16],[10],858⟩) from rfl))
private theorem rec12306 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(18),[3,4,7,8,12,15,16],[10],859⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[377]? = some (⟨232,(18),[3,4,7,8,12,15,16],[10],859⟩) from rfl))
private theorem rec12313 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 232 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(19),[3,7,15],[10],860⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[384]? = some (⟨232,(19),[3,7,15],[10],860⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 72).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 10 gs.1 j := by
  have hp : ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 72).take 8) = [(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 226)).length = 10 := by decide +kernel
    have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11505 7 10 (by decide) (by decide)
    · right
      exact rec11509 7 10 (by decide) (by decide)
    · right
      exact rec11515 7 10 (by decide) (by decide)
    · right
      exact rec11521 7 10 (by decide) (by decide)
    · right
      exact rec11527 7 10 (by decide) (by decide)
    · right
      exact rec11533 7 10 (by decide) (by decide)
    · right
      exact rec11539 7 10 (by decide) (by decide)
    · right
      exact rec11545 7 10 (by decide) (by decide)
    · right
      exact rec11551 7 10 (by decide) (by decide)
    · right
      exact rec11557 7 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 227)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11563 7 10 (by decide) (by decide)
    · right
      exact rec11569 7 10 (by decide) (by decide)
    · right
      exact rec11576 7 10 (by decide) (by decide)
    · right
      exact rec11583 7 10 (by decide) (by decide)
    · right
      exact rec11590 7 10 (by decide) (by decide)
    · right
      exact rec11597 7 10 (by decide) (by decide)
    · right
      exact rec11603 7 10 (by decide) (by decide)
    · right
      exact rec11610 7 10 (by decide) (by decide)
    · right
      exact rec11617 7 10 (by decide) (by decide)
    · right
      exact rec11624 7 10 (by decide) (by decide)
    · right
      exact rec11631 7 10 (by decide) (by decide)
    · right
      exact rec11637 7 10 (by decide) (by decide)
    · right
      exact rec11644 7 10 (by decide) (by decide)
    · right
      exact rec11651 7 10 (by decide) (by decide)
    · right
      exact rec11658 7 10 (by decide) (by decide)
    · right
      exact rec11665 7 10 (by decide) (by decide)
    · right
      exact rec11671 7 10 (by decide) (by decide)
    · right
      exact rec11678 7 10 (by decide) (by decide)
    · right
      exact rec11685 7 10 (by decide) (by decide)
    · right
      exact rec11692 7 10 (by decide) (by decide)
    · right
      exact rec11699 7 10 (by decide) (by decide)
    · right
      exact rec11705 7 10 (by decide) (by decide)
    · right
      exact rec11712 7 10 (by decide) (by decide)
    · right
      exact rec11719 7 10 (by decide) (by decide)
    · right
      exact rec11726 7 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 228)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11736 7 10 (by decide) (by decide)
    · right
      exact rec11743 7 10 (by decide) (by decide)
    · right
      exact rec11753 7 10 (by decide) (by decide)
    · right
      exact rec11760 7 10 (by decide) (by decide)
    · right
      exact rec11764 7 10 (by decide) (by decide)
    · right
      exact rec11770 7 10 (by decide) (by decide)
    · right
      exact rec11776 7 10 (by decide) (by decide)
    · right
      exact rec11782 7 10 (by decide) (by decide)
    · right
      exact rec11788 7 10 (by decide) (by decide)
    · right
      exact rec11794 7 10 (by decide) (by decide)
    · right
      exact rec11801 7 10 (by decide) (by decide)
    · right
      exact rec11807 7 10 (by decide) (by decide)
    · right
      exact rec11813 7 10 (by decide) (by decide)
    · right
      exact rec11819 7 10 (by decide) (by decide)
    · right
      exact rec11825 7 10 (by decide) (by decide)
    · right
      exact rec11831 7 10 (by decide) (by decide)
    · right
      exact rec11837 7 10 (by decide) (by decide)
    · right
      exact rec11843 7 10 (by decide) (by decide)
    · right
      exact rec11849 7 10 (by decide) (by decide)
    · right
      exact rec11855 7 10 (by decide) (by decide)
    · right
      exact rec11861 7 10 (by decide) (by decide)
    · right
      exact rec11867 7 10 (by decide) (by decide)
    · right
      exact rec11873 7 10 (by decide) (by decide)
    · right
      exact rec11879 7 10 (by decide) (by decide)
    · right
      exact rec11885 7 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 229)).length = 25 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 230)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11891 7 10 (by decide) (by decide)
    · right
      exact rec11897 7 10 (by decide) (by decide)
    · right
      exact rec11904 7 10 (by decide) (by decide)
    · right
      exact rec11910 7 10 (by decide) (by decide)
    · right
      exact rec11916 7 10 (by decide) (by decide)
    · right
      exact rec11922 7 10 (by decide) (by decide)
    · right
      exact rec11928 7 10 (by decide) (by decide)
    · right
      exact rec11937 7 10 (by decide) (by decide)
    · right
      exact rec11944 7 10 (by decide) (by decide)
    · right
      exact rec11951 7 10 (by decide) (by decide)
    · right
      exact rec11959 7 10 (by decide) (by decide)
    · right
      exact rec11965 7 10 (by decide) (by decide)
    · right
      exact rec11973 7 10 (by decide) (by decide)
    · right
      exact rec11979 7 10 (by decide) (by decide)
    · right
      exact rec11986 7 10 (by decide) (by decide)
    · right
      exact rec11994 7 10 (by decide) (by decide)
    · right
      exact rec12000 7 10 (by decide) (by decide)
    · right
      exact rec12007 7 10 (by decide) (by decide)
    · right
      exact rec12014 7 10 (by decide) (by decide)
    · right
      exact rec12021 7 10 (by decide) (by decide)
    · right
      exact rec12028 7 10 (by decide) (by decide)
    · right
      exact rec12034 7 10 (by decide) (by decide)
    · right
      exact rec12041 7 10 (by decide) (by decide)
    · right
      exact rec12048 7 10 (by decide) (by decide)
    · right
      exact rec12055 7 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 231)).length = 20 := by decide +kernel
    have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12065 7 10 (by decide) (by decide)
    · right
      exact rec12069 7 10 (by decide) (by decide)
    · right
      exact rec12077 7 10 (by decide) (by decide)
    · right
      exact rec12083 7 10 (by decide) (by decide)
    · right
      exact rec12092 7 10 (by decide) (by decide)
    · right
      exact rec12096 7 10 (by decide) (by decide)
    · right
      exact rec12104 7 10 (by decide) (by decide)
    · right
      exact rec12110 7 10 (by decide) (by decide)
    · right
      exact rec12116 7 10 (by decide) (by decide)
    · right
      exact rec12122 7 10 (by decide) (by decide)
    · right
      exact rec12128 7 10 (by decide) (by decide)
    · right
      exact rec12134 7 10 (by decide) (by decide)
    · right
      exact rec12140 7 10 (by decide) (by decide)
    · right
      exact rec12146 7 10 (by decide) (by decide)
    · right
      exact rec12152 7 10 (by decide) (by decide)
    · right
      exact rec12158 7 10 (by decide) (by decide)
    · right
      exact rec12164 7 10 (by decide) (by decide)
    · right
      exact rec12170 7 10 (by decide) (by decide)
    · right
      exact rec12176 7 10 (by decide) (by decide)
    · right
      exact rec12182 7 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 232)).length = 20 := by decide +kernel
    have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12188 7 10 (by decide) (by decide)
    · right
      exact rec12194 7 10 (by decide) (by decide)
    · right
      exact rec12201 7 10 (by decide) (by decide)
    · right
      exact rec12207 7 10 (by decide) (by decide)
    · right
      exact rec12215 7 10 (by decide) (by decide)
    · right
      exact rec12221 7 10 (by decide) (by decide)
    · right
      exact rec12227 7 10 (by decide) (by decide)
    · right
      exact rec12234 7 10 (by decide) (by decide)
    · right
      exact rec12240 7 10 (by decide) (by decide)
    · right
      exact rec12247 7 10 (by decide) (by decide)
    · right
      exact rec12254 7 10 (by decide) (by decide)
    · right
      exact rec12260 7 10 (by decide) (by decide)
    · right
      exact rec12267 7 10 (by decide) (by decide)
    · right
      exact rec12273 7 10 (by decide) (by decide)
    · right
      exact rec12280 7 10 (by decide) (by decide)
    · right
      exact rec12287 7 10 (by decide) (by decide)
    · right
      exact rec12293 7 10 (by decide) (by decide)
    · right
      exact rec12300 7 10 (by decide) (by decide)
    · right
      exact rec12306 7 10 (by decide) (by decide)
    · right
      exact rec12313 7 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 233)).length = 4 := by decide +kernel
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
end Section14CoverageSpec_7_5_p10_72_80

#print axioms solution
