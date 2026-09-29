-- Prove2me | solution 1 for Freiman.section14_s0010_coverage0001_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T15:47:37.629528+00:00
-- url     : https://prove2.me/submissions/c3b42d41-e0ee-4ad3-a901-43c2b2f2c18a

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
namespace Section14Coverage_10_1_p32_48
private theorem rec461 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[461]? = some (⟨16,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) from rfl))
private theorem rec473 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[9,10],[42],205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[473]? = some (⟨16,(-1),[9,10],[42],205⟩) from rfl))
private theorem rec474 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([43] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[9,10],[43],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[474]? = some (⟨16,(-1),[9,10],[43],207⟩) from rfl))
private theorem rec475 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([47] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[9,10],[47],239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[475]? = some (⟨16,(-1),[9,10],[47],239⟩) from rfl))
private theorem rec480 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([39] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[9,10],[39],1397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[480]? = some (⟨16,(-1),[9,10],[39],1397⟩) from rfl))
private theorem rec481 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[9,10],[46],1398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[481]? = some (⟨16,(-1),[9,10],[46],1398⟩) from rfl))
private theorem rec507 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[9,10],[35],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[507]? = some (⟨18,(0),[9,10],[35],106⟩) from rfl))
private theorem rec508 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[9,10],[38],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[508]? = some (⟨18,(0),[9,10],[38],160⟩) from rfl))
private theorem rec509 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[10],[34],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[509]? = some (⟨18,(0),[10],[34],106⟩) from rfl))
private theorem rec524 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[9,10],[35],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[524]? = some (⟨18,(1),[9,10],[35],106⟩) from rfl))
private theorem rec525 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[9,10],[38],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[525]? = some (⟨18,(1),[9,10],[38],160⟩) from rfl))
private theorem rec526 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[10],[34],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[526]? = some (⟨18,(1),[10],[34],106⟩) from rfl))
private theorem rec541 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[9,10],[35],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[541]? = some (⟨18,(2),[9,10],[35],106⟩) from rfl))
private theorem rec542 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[9,10],[38],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[542]? = some (⟨18,(2),[9,10],[38],160⟩) from rfl))
private theorem rec543 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[10],[34],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[543]? = some (⟨18,(2),[10],[34],106⟩) from rfl))
private theorem rec559 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[9,10],[38],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[559]? = some (⟨18,(3),[9,10],[38],160⟩) from rfl))
private theorem rec560 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[10],[34,35],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[560]? = some (⟨18,(3),[10],[34,35],106⟩) from rfl))
private theorem rec575 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[9,10],[35],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[575]? = some (⟨18,(4),[9,10],[35],106⟩) from rfl))
private theorem rec576 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[9,10],[38],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[576]? = some (⟨18,(4),[9,10],[38],160⟩) from rfl))
private theorem rec577 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[10],[34],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[577]? = some (⟨18,(4),[10],[34],106⟩) from rfl))
private theorem rec592 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[9,10],[35],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[592]? = some (⟨18,(5),[9,10],[35],107⟩) from rfl))
private theorem rec593 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[9,10],[38],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[593]? = some (⟨18,(5),[9,10],[38],161⟩) from rfl))
private theorem rec594 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[10],[34],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[594]? = some (⟨18,(5),[10],[34],107⟩) from rfl))
private theorem rec609 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[9,10],[35],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[609]? = some (⟨18,(6),[9,10],[35],107⟩) from rfl))
private theorem rec610 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[9,10],[38],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[610]? = some (⟨18,(6),[9,10],[38],161⟩) from rfl))
private theorem rec611 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[10],[34],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[611]? = some (⟨18,(6),[10],[34],107⟩) from rfl))
private theorem rec626 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[9,10],[35],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[626]? = some (⟨18,(7),[9,10],[35],107⟩) from rfl))
private theorem rec627 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[9,10],[38],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[627]? = some (⟨18,(7),[9,10],[38],161⟩) from rfl))
private theorem rec628 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[10],[34],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[628]? = some (⟨18,(7),[10],[34],107⟩) from rfl))
private theorem rec644 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[9,10],[38],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[644]? = some (⟨18,(8),[9,10],[38],161⟩) from rfl))
private theorem rec645 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[10],[34,35],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[645]? = some (⟨18,(8),[10],[34,35],107⟩) from rfl))
private theorem rec660 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[9,10],[35],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[660]? = some (⟨18,(9),[9,10],[35],107⟩) from rfl))
private theorem rec661 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[9,10],[38],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[661]? = some (⟨18,(9),[9,10],[38],161⟩) from rfl))
private theorem rec662 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[10],[34],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[662]? = some (⟨18,(9),[10],[34],107⟩) from rfl))
private theorem rec677 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[9,10],[35],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[677]? = some (⟨18,(10),[9,10],[35],108⟩) from rfl))
private theorem rec678 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[9,10],[38],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[678]? = some (⟨18,(10),[9,10],[38],162⟩) from rfl))
private theorem rec679 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[10],[34],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[679]? = some (⟨18,(10),[10],[34],108⟩) from rfl))
private theorem rec694 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[9,10],[35],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[694]? = some (⟨18,(11),[9,10],[35],109⟩) from rfl))
private theorem rec695 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[9,10],[38],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[695]? = some (⟨18,(11),[9,10],[38],163⟩) from rfl))
private theorem rec696 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[10],[34],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[696]? = some (⟨18,(11),[10],[34],109⟩) from rfl))
private theorem rec711 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[9,10],[35],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[711]? = some (⟨18,(12),[9,10],[35],110⟩) from rfl))
private theorem rec712 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[9,10],[38],164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[712]? = some (⟨18,(12),[9,10],[38],164⟩) from rfl))
private theorem rec713 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[10],[34],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[713]? = some (⟨18,(12),[10],[34],110⟩) from rfl))
private theorem rec729 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[9,10],[38],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[729]? = some (⟨18,(13),[9,10],[38],163⟩) from rfl))
private theorem rec730 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[10],[34,35],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[730]? = some (⟨18,(13),[10],[34,35],109⟩) from rfl))
private theorem rec745 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[9,10],[35],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[745]? = some (⟨18,(14),[9,10],[35],111⟩) from rfl))
private theorem rec746 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[9,10],[38],165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[746]? = some (⟨18,(14),[9,10],[38],165⟩) from rfl))
private theorem rec747 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[10],[34],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[747]? = some (⟨18,(14),[10],[34],111⟩) from rfl))
private theorem rec762 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[9,10],[35],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[762]? = some (⟨18,(15),[9,10],[35],108⟩) from rfl))
private theorem rec763 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[9,10],[38],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[763]? = some (⟨18,(15),[9,10],[38],162⟩) from rfl))
private theorem rec764 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[10],[34],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[764]? = some (⟨18,(15),[10],[34],108⟩) from rfl))
private theorem rec779 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[9,10],[35],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[779]? = some (⟨18,(16),[9,10],[35],112⟩) from rfl))
private theorem rec780 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[9,10],[38],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[780]? = some (⟨18,(16),[9,10],[38],166⟩) from rfl))
private theorem rec781 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[10],[34],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[781]? = some (⟨18,(16),[10],[34],112⟩) from rfl))
private theorem rec796 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[9,10],[35],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[796]? = some (⟨18,(17),[9,10],[35],112⟩) from rfl))
private theorem rec797 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[9,10],[38],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[797]? = some (⟨18,(17),[9,10],[38],166⟩) from rfl))
private theorem rec798 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[10],[34],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[798]? = some (⟨18,(17),[10],[34],112⟩) from rfl))
private theorem rec814 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[9,10],[38],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[814]? = some (⟨18,(18),[9,10],[38],166⟩) from rfl))
private theorem rec815 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[10],[34,35],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[815]? = some (⟨18,(18),[10],[34,35],112⟩) from rfl))
private theorem rec830 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[9,10],[35],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[830]? = some (⟨18,(19),[9,10],[35],112⟩) from rfl))
private theorem rec831 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[9,10],[38],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[831]? = some (⟨18,(19),[9,10],[38],166⟩) from rfl))
private theorem rec832 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[10],[34],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[832]? = some (⟨18,(19),[10],[34],112⟩) from rfl))
private theorem rec847 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[9,10],[35],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[847]? = some (⟨18,(20),[9,10],[35],108⟩) from rfl))
private theorem rec848 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[9,10],[38],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[848]? = some (⟨18,(20),[9,10],[38],162⟩) from rfl))
private theorem rec849 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[10],[34],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[849]? = some (⟨18,(20),[10],[34],108⟩) from rfl))
private theorem rec864 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[9,10],[35],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[864]? = some (⟨18,(21),[9,10],[35],109⟩) from rfl))
private theorem rec865 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[9,10],[38],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[865]? = some (⟨18,(21),[9,10],[38],163⟩) from rfl))
private theorem rec866 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[10],[34],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[866]? = some (⟨18,(21),[10],[34],109⟩) from rfl))
private theorem rec881 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[9,10],[35],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[881]? = some (⟨18,(22),[9,10],[35],110⟩) from rfl))
private theorem rec882 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[9,10],[38],164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[882]? = some (⟨18,(22),[9,10],[38],164⟩) from rfl))
private theorem rec883 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[10],[34],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[883]? = some (⟨18,(22),[10],[34],110⟩) from rfl))
private theorem rec899 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[9,10],[38],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[899]? = some (⟨18,(23),[9,10],[38],163⟩) from rfl))
private theorem rec900 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[10],[34,35],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[900]? = some (⟨18,(23),[10],[34,35],109⟩) from rfl))
private theorem rec915 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[9,10],[35],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[915]? = some (⟨18,(24),[9,10],[35],111⟩) from rfl))
private theorem rec916 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[9,10],[38],165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[916]? = some (⟨18,(24),[9,10],[38],165⟩) from rfl))
private theorem rec917 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[10],[34],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[917]? = some (⟨18,(24),[10],[34],111⟩) from rfl))
private theorem rec1199 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[30]? = some (⟨23,(0),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1206 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[37]? = some (⟨23,(1),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1213 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[44]? = some (⟨23,(2),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1220 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[51]? = some (⟨23,(3),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1227 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[58]? = some (⟨23,(4),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1234 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[65]? = some (⟨23,(5),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1241 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[72]? = some (⟨23,(6),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1248 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[79]? = some (⟨23,(7),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1255 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[86]? = some (⟨23,(8),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1262 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[93]? = some (⟨23,(9),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1269 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[100]? = some (⟨23,(10),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1276 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[107]? = some (⟨23,(11),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1283 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[114]? = some (⟨23,(12),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1290 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[121]? = some (⟨23,(13),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1297 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[128]? = some (⟨23,(14),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1304 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[135]? = some (⟨23,(15),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1311 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[142]? = some (⟨23,(16),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1318 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[149]? = some (⟨23,(17),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1325 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[156]? = some (⟨23,(18),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1332 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[163]? = some (⟨23,(19),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1339 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[170]? = some (⟨23,(20),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1346 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[177]? = some (⟨23,(21),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1353 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[184]? = some (⟨23,(22),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1360 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[191]? = some (⟨23,(23),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1367 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[198]? = some (⟨23,(24),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec1384 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[9,10],[34],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[215]? = some (⟨25,(0),[9,10],[34],80⟩) from rfl))
private theorem rec1385 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[9,10],[35],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[216]? = some (⟨25,(0),[9,10],[35],167⟩) from rfl))
private theorem rec1386 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[9,10],[38],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[217]? = some (⟨25,(0),[9,10],[38],189⟩) from rfl))
private theorem rec1408 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[9,10],[34],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[239]? = some (⟨25,(1),[9,10],[34],81⟩) from rfl))
private theorem rec1409 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[9,10],[35],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[240]? = some (⟨25,(1),[9,10],[35],168⟩) from rfl))
private theorem rec1410 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[9,10],[38],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[241]? = some (⟨25,(1),[9,10],[38],216⟩) from rfl))
private theorem rec1432 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[9,10],[34],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[263]? = some (⟨25,(2),[9,10],[34],80⟩) from rfl))
private theorem rec1433 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[9,10],[35],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[264]? = some (⟨25,(2),[9,10],[35],167⟩) from rfl))
private theorem rec1434 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[9,10],[38],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[265]? = some (⟨25,(2),[9,10],[38],217⟩) from rfl))
private theorem rec1456 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[9,10],[34],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[287]? = some (⟨25,(3),[9,10],[34],82⟩) from rfl))
private theorem rec1457 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[9,10],[35],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[288]? = some (⟨25,(3),[9,10],[35],169⟩) from rfl))
private theorem rec1458 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[9,10],[38],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[289]? = some (⟨25,(3),[9,10],[38],218⟩) from rfl))
private theorem rec1480 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[9,10],[34],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[311]? = some (⟨25,(4),[9,10],[34],83⟩) from rfl))
private theorem rec1481 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[9,10],[35],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[312]? = some (⟨25,(4),[9,10],[35],170⟩) from rfl))
private theorem rec1482 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[9,10],[38],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[313]? = some (⟨25,(4),[9,10],[38],219⟩) from rfl))
private theorem rec1501 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[9,10],[34],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[332]? = some (⟨25,(5),[9,10],[34],80⟩) from rfl))
private theorem rec1502 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[9,10],[35],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[333]? = some (⟨25,(5),[9,10],[35],167⟩) from rfl))
private theorem rec1503 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[9,10],[38],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[334]? = some (⟨25,(5),[9,10],[38],189⟩) from rfl))
private theorem rec1525 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[9,10],[34],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[356]? = some (⟨25,(6),[9,10],[34],81⟩) from rfl))
private theorem rec1526 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[9,10],[35],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[357]? = some (⟨25,(6),[9,10],[35],168⟩) from rfl))
private theorem rec1527 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[9,10],[38],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[358]? = some (⟨25,(6),[9,10],[38],216⟩) from rfl))
private theorem rec1549 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[9,10],[34],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[380]? = some (⟨25,(7),[9,10],[34],80⟩) from rfl))
private theorem rec1550 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[9,10],[35],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[381]? = some (⟨25,(7),[9,10],[35],167⟩) from rfl))
private theorem rec1551 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[9,10],[38],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[382]? = some (⟨25,(7),[9,10],[38],217⟩) from rfl))
private theorem rec1573 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[9,10],[34],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[404]? = some (⟨25,(8),[9,10],[34],82⟩) from rfl))
private theorem rec1574 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[9,10],[35],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[405]? = some (⟨25,(8),[9,10],[35],169⟩) from rfl))
private theorem rec1575 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[9,10],[38],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[406]? = some (⟨25,(8),[9,10],[38],218⟩) from rfl))
private theorem rec1597 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[9,10],[34],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[428]? = some (⟨25,(9),[9,10],[34],83⟩) from rfl))
private theorem rec1598 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[9,10],[35],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[429]? = some (⟨25,(9),[9,10],[35],170⟩) from rfl))
private theorem rec1599 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[9,10],[38],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[430]? = some (⟨25,(9),[9,10],[38],219⟩) from rfl))
private theorem rec1618 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[9,10],[34],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[449]? = some (⟨25,(10),[9,10],[34],84⟩) from rfl))
private theorem rec1619 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[9,10],[35],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[450]? = some (⟨25,(10),[9,10],[35],171⟩) from rfl))
private theorem rec1620 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[9,10],[38],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[451]? = some (⟨25,(10),[9,10],[38],194⟩) from rfl))
private theorem rec1642 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[9,10],[34],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[473]? = some (⟨25,(11),[9,10],[34],84⟩) from rfl))
private theorem rec1643 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[9,10],[35],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[474]? = some (⟨25,(11),[9,10],[35],171⟩) from rfl))
private theorem rec1644 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[9,10],[38],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[475]? = some (⟨25,(11),[9,10],[38],220⟩) from rfl))
private theorem rec1666 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[9,10],[34],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[497]? = some (⟨25,(12),[9,10],[34],84⟩) from rfl))
private theorem rec1667 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[9,10],[35],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[498]? = some (⟨25,(12),[9,10],[35],171⟩) from rfl))
private theorem rec1668 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[9,10],[38],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[499]? = some (⟨25,(12),[9,10],[38],220⟩) from rfl))
private theorem rec1690 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[9,10],[34],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[521]? = some (⟨25,(13),[9,10],[34],84⟩) from rfl))
private theorem rec1691 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[9,10],[35],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[522]? = some (⟨25,(13),[9,10],[35],171⟩) from rfl))
private theorem rec1692 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[9,10],[38],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[523]? = some (⟨25,(13),[9,10],[38],220⟩) from rfl))
private theorem rec1714 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[9,10],[34],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[545]? = some (⟨25,(14),[9,10],[34],83⟩) from rfl))
private theorem rec1715 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[9,10],[35],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[546]? = some (⟨25,(14),[9,10],[35],170⟩) from rfl))
private theorem rec1716 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[9,10],[38],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[547]? = some (⟨25,(14),[9,10],[38],219⟩) from rfl))
private theorem rec1735 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[9,10],[34],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[566]? = some (⟨25,(15),[9,10],[34],35⟩) from rfl))
private theorem rec1736 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[9,10],[35],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[567]? = some (⟨25,(15),[9,10],[35],172⟩) from rfl))
private theorem rec1737 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[9,10],[38],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[568]? = some (⟨25,(15),[9,10],[38],196⟩) from rfl))
private theorem rec1759 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[9,10],[34],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[590]? = some (⟨25,(16),[9,10],[34],35⟩) from rfl))
private theorem rec1760 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[9,10],[35],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[591]? = some (⟨25,(16),[9,10],[35],172⟩) from rfl))
private theorem rec1761 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[9,10],[38],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[592]? = some (⟨25,(16),[9,10],[38],221⟩) from rfl))
private theorem rec1783 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[9,10],[34],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[614]? = some (⟨25,(17),[9,10],[34],35⟩) from rfl))
private theorem rec1784 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[9,10],[35],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[615]? = some (⟨25,(17),[9,10],[35],172⟩) from rfl))
private theorem rec1785 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[9,10],[38],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[616]? = some (⟨25,(17),[9,10],[38],221⟩) from rfl))
private theorem rec1807 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[9,10],[34],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[638]? = some (⟨25,(18),[9,10],[34],35⟩) from rfl))
private theorem rec1808 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[9,10],[35],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[639]? = some (⟨25,(18),[9,10],[35],172⟩) from rfl))
private theorem rec1809 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[9,10],[38],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[640]? = some (⟨25,(18),[9,10],[38],221⟩) from rfl))
private theorem rec1831 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[9,10],[34],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[662]? = some (⟨25,(19),[9,10],[34],35⟩) from rfl))
private theorem rec1832 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[9,10],[35],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[663]? = some (⟨25,(19),[9,10],[35],172⟩) from rfl))
private theorem rec1833 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[9,10],[38],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[664]? = some (⟨25,(19),[9,10],[38],221⟩) from rfl))
private theorem rec1852 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[9,10],[34],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[683]? = some (⟨25,(20),[9,10],[34],38⟩) from rfl))
private theorem rec1853 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[9,10],[35],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[684]? = some (⟨25,(20),[9,10],[35],173⟩) from rfl))
private theorem rec1854 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[9,10],[38],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[685]? = some (⟨25,(20),[9,10],[38],198⟩) from rfl))
private theorem rec1876 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[9,10],[34],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[707]? = some (⟨25,(21),[9,10],[34],38⟩) from rfl))
private theorem rec1877 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[9,10],[35],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[708]? = some (⟨25,(21),[9,10],[35],173⟩) from rfl))
private theorem rec1878 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[9,10],[38],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[709]? = some (⟨25,(21),[9,10],[38],222⟩) from rfl))
private theorem rec1900 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[9,10],[34],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[731]? = some (⟨25,(22),[9,10],[34],38⟩) from rfl))
private theorem rec1901 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[9,10],[35],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[732]? = some (⟨25,(22),[9,10],[35],173⟩) from rfl))
private theorem rec1902 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[9,10],[38],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[733]? = some (⟨25,(22),[9,10],[38],222⟩) from rfl))
private theorem rec1924 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[9,10],[34],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[755]? = some (⟨25,(23),[9,10],[34],38⟩) from rfl))
private theorem rec1925 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[9,10],[35],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[756]? = some (⟨25,(23),[9,10],[35],173⟩) from rfl))
private theorem rec1926 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[9,10],[38],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[757]? = some (⟨25,(23),[9,10],[38],222⟩) from rfl))
private theorem rec1948 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[9,10],[34],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[779]? = some (⟨25,(24),[9,10],[34],38⟩) from rfl))
private theorem rec1949 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[9,10],[35],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[780]? = some (⟨25,(24),[9,10],[35],173⟩) from rfl))
private theorem rec1950 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[9,10],[38],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[781]? = some (⟨25,(24),[9,10],[38],222⟩) from rfl))
private theorem rec1966 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[9,10],[35],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[797]? = some (⟨28,(0),[9,10],[35],113⟩) from rfl))
private theorem rec1967 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[9,10],[38],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[798]? = some (⟨28,(0),[9,10],[38],174⟩) from rfl))
private theorem rec1968 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[10],[34],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[799]? = some (⟨28,(0),[10],[34],113⟩) from rfl))
private theorem rec1982 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[9,10],[35],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[813]? = some (⟨28,(1),[9,10],[35],113⟩) from rfl))
private theorem rec1983 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[9,10],[38],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[814]? = some (⟨28,(1),[9,10],[38],174⟩) from rfl))
private theorem rec1984 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[10],[34],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[815]? = some (⟨28,(1),[10],[34],113⟩) from rfl))
private theorem rec1998 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[9,10],[35],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[829]? = some (⟨28,(2),[9,10],[35],113⟩) from rfl))
private theorem rec1999 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[9,10],[38],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[830]? = some (⟨28,(2),[9,10],[38],174⟩) from rfl))
private theorem rec2000 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[10],[34],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[831]? = some (⟨28,(2),[10],[34],113⟩) from rfl))
private theorem rec2014 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[9,10],[35],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[845]? = some (⟨28,(3),[9,10],[35],113⟩) from rfl))
private theorem rec2015 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[9,10],[38],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[846]? = some (⟨28,(3),[9,10],[38],174⟩) from rfl))
private theorem rec2016 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[10],[34],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[847]? = some (⟨28,(3),[10],[34],113⟩) from rfl))
private theorem rec2030 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[9,10],[35],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[861]? = some (⟨28,(4),[9,10],[35],113⟩) from rfl))
private theorem rec2031 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[9,10],[38],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[862]? = some (⟨28,(4),[9,10],[38],174⟩) from rfl))
private theorem rec2032 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[10],[34],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[863]? = some (⟨28,(4),[10],[34],113⟩) from rfl))
private theorem rec2046 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[9,10],[35],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[877]? = some (⟨28,(5),[9,10],[35],114⟩) from rfl))
private theorem rec2047 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[9,10],[38],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[878]? = some (⟨28,(5),[9,10],[38],175⟩) from rfl))
private theorem rec2048 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[10],[34],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[879]? = some (⟨28,(5),[10],[34],114⟩) from rfl))
private theorem rec2062 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[9,10],[35],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[893]? = some (⟨28,(6),[9,10],[35],114⟩) from rfl))
private theorem rec2063 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[9,10],[38],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[894]? = some (⟨28,(6),[9,10],[38],175⟩) from rfl))
private theorem rec2064 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[10],[34],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[895]? = some (⟨28,(6),[10],[34],114⟩) from rfl))
private theorem rec2078 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[9,10],[35],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[909]? = some (⟨28,(7),[9,10],[35],114⟩) from rfl))
private theorem rec2079 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[9,10],[38],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[910]? = some (⟨28,(7),[9,10],[38],175⟩) from rfl))
private theorem rec2080 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[10],[34],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[911]? = some (⟨28,(7),[10],[34],114⟩) from rfl))
private theorem rec2094 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[9,10],[35],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[925]? = some (⟨28,(8),[9,10],[35],114⟩) from rfl))
private theorem rec2095 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[9,10],[38],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[926]? = some (⟨28,(8),[9,10],[38],175⟩) from rfl))
private theorem rec2096 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[10],[34],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[927]? = some (⟨28,(8),[10],[34],114⟩) from rfl))
private theorem rec2110 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[9,10],[35],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[941]? = some (⟨28,(9),[9,10],[35],114⟩) from rfl))
private theorem rec2111 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[9,10],[38],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[942]? = some (⟨28,(9),[9,10],[38],175⟩) from rfl))
private theorem rec2112 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[10],[34],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[943]? = some (⟨28,(9),[10],[34],114⟩) from rfl))
private theorem rec2126 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[9,10],[35],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[957]? = some (⟨28,(10),[9,10],[35],115⟩) from rfl))
private theorem rec2127 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[9,10],[38],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[958]? = some (⟨28,(10),[9,10],[38],176⟩) from rfl))
private theorem rec2128 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[10],[34],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[959]? = some (⟨28,(10),[10],[34],115⟩) from rfl))
private theorem rec2142 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[9,10],[35],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[973]? = some (⟨28,(11),[9,10],[35],116⟩) from rfl))
private theorem rec2143 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[9,10],[38],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[974]? = some (⟨28,(11),[9,10],[38],177⟩) from rfl))
private theorem rec2144 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[10],[34],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[975]? = some (⟨28,(11),[10],[34],116⟩) from rfl))
private theorem rec2158 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[9,10],[35],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[989]? = some (⟨28,(12),[9,10],[35],117⟩) from rfl))
private theorem rec2159 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[9,10],[38],178⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[990]? = some (⟨28,(12),[9,10],[38],178⟩) from rfl))
private theorem rec2160 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[10],[34],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[991]? = some (⟨28,(12),[10],[34],117⟩) from rfl))
private theorem rec2174 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[9,10],[35],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1005]? = some (⟨28,(13),[9,10],[35],116⟩) from rfl))
private theorem rec2175 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[9,10],[38],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1006]? = some (⟨28,(13),[9,10],[38],177⟩) from rfl))
private theorem rec2176 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[10],[34],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1007]? = some (⟨28,(13),[10],[34],116⟩) from rfl))
private theorem rec2190 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[9,10],[35],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1021]? = some (⟨28,(14),[9,10],[35],118⟩) from rfl))
private theorem rec2191 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[9,10],[38],179⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1022]? = some (⟨28,(14),[9,10],[38],179⟩) from rfl))
private theorem rec2192 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[10],[34],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1023]? = some (⟨28,(14),[10],[34],118⟩) from rfl))
private theorem rec2206 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[9,10],[35],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1037]? = some (⟨28,(15),[9,10],[35],115⟩) from rfl))
private theorem rec2207 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[9,10],[38],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1038]? = some (⟨28,(15),[9,10],[38],176⟩) from rfl))
private theorem rec2208 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[10],[34],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1039]? = some (⟨28,(15),[10],[34],115⟩) from rfl))
private theorem rec2222 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[9,10],[35],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1053]? = some (⟨28,(16),[9,10],[35],119⟩) from rfl))
private theorem rec2223 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[9,10],[38],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1054]? = some (⟨28,(16),[9,10],[38],180⟩) from rfl))
private theorem rec2224 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[10],[34],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1055]? = some (⟨28,(16),[10],[34],119⟩) from rfl))
private theorem rec2238 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[9,10],[35],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1069]? = some (⟨28,(17),[9,10],[35],119⟩) from rfl))
private theorem rec2239 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[9,10],[38],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1070]? = some (⟨28,(17),[9,10],[38],180⟩) from rfl))
private theorem rec2240 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[10],[34],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1071]? = some (⟨28,(17),[10],[34],119⟩) from rfl))
private theorem rec2254 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[9,10],[35],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1085]? = some (⟨28,(18),[9,10],[35],119⟩) from rfl))
private theorem rec2255 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[9,10],[38],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1086]? = some (⟨28,(18),[9,10],[38],180⟩) from rfl))
private theorem rec2256 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[10],[34],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1087]? = some (⟨28,(18),[10],[34],119⟩) from rfl))
private theorem rec2270 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[9,10],[35],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1101]? = some (⟨28,(19),[9,10],[35],119⟩) from rfl))
private theorem rec2271 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[9,10],[38],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1102]? = some (⟨28,(19),[9,10],[38],180⟩) from rfl))
private theorem rec2272 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[10],[34],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1103]? = some (⟨28,(19),[10],[34],119⟩) from rfl))
private theorem rec2286 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[9,10],[35],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1117]? = some (⟨28,(20),[9,10],[35],115⟩) from rfl))
private theorem rec2287 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[9,10],[38],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1118]? = some (⟨28,(20),[9,10],[38],176⟩) from rfl))
private theorem rec2288 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[10],[34],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1119]? = some (⟨28,(20),[10],[34],115⟩) from rfl))
private theorem rec2302 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[9,10],[35],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1133]? = some (⟨28,(21),[9,10],[35],116⟩) from rfl))
private theorem rec2303 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[9,10],[38],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1134]? = some (⟨28,(21),[9,10],[38],177⟩) from rfl))
private theorem rec2304 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[10],[34],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1135]? = some (⟨28,(21),[10],[34],116⟩) from rfl))
private theorem rec2318 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[9,10],[35],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1149]? = some (⟨28,(22),[9,10],[35],117⟩) from rfl))
private theorem rec2319 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[9,10],[38],178⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1150]? = some (⟨28,(22),[9,10],[38],178⟩) from rfl))
private theorem rec2320 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[10],[34],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1151]? = some (⟨28,(22),[10],[34],117⟩) from rfl))
private theorem rec2334 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[9,10],[35],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1165]? = some (⟨28,(23),[9,10],[35],116⟩) from rfl))
private theorem rec2335 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[9,10],[38],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1166]? = some (⟨28,(23),[9,10],[38],177⟩) from rfl))
private theorem rec2336 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[10],[34],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1167]? = some (⟨28,(23),[10],[34],116⟩) from rfl))
private theorem rec2350 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[9,10],[35],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1181]? = some (⟨28,(24),[9,10],[35],118⟩) from rfl))
private theorem rec2351 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[9,10],[38],179⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1182]? = some (⟨28,(24),[9,10],[38],179⟩) from rfl))
private theorem rec2352 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[10],[34],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1183]? = some (⟨28,(24),[10],[34],118⟩) from rfl))
private theorem rec2367 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[9,10],[34,35,38],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1198]? = some (⟨30,(0),[9,10],[34,35,38],152⟩) from rfl))
private theorem rec2382 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[9,10],[34,35,38],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1213]? = some (⟨30,(1),[9,10],[34,35,38],153⟩) from rfl))
private theorem rec2399 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[9,10],[34],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1230]? = some (⟨30,(2),[9,10],[34],92⟩) from rfl))
private theorem rec2400 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[9,10],[35],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1231]? = some (⟨30,(2),[9,10],[35],120⟩) from rfl))
private theorem rec2401 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[9,10],[38],200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1232]? = some (⟨30,(2),[9,10],[38],200⟩) from rfl))
private theorem rec2423 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[9,10],[34],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1254]? = some (⟨30,(3),[9,10],[34],93⟩) from rfl))
private theorem rec2424 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[9,10],[35],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1255]? = some (⟨30,(3),[9,10],[35],181⟩) from rfl))
private theorem rec2425 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[9,10],[38],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1256]? = some (⟨30,(3),[9,10],[38],230⟩) from rfl))
private theorem rec2447 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[9,10],[34],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[4]? = some (⟨30,(4),[9,10],[34],94⟩) from rfl))
private theorem rec2448 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[9,10],[35],182⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[5]? = some (⟨30,(4),[9,10],[35],182⟩) from rfl))
private theorem rec2449 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[9,10],[38],231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[6]? = some (⟨30,(4),[9,10],[38],231⟩) from rfl))
private theorem rec2471 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[9,10],[34],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[28]? = some (⟨30,(5),[9,10],[34],93⟩) from rfl))
private theorem rec2472 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[9,10],[35],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[29]? = some (⟨30,(5),[9,10],[35],181⟩) from rfl))
private theorem rec2473 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[9,10],[38],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[30]? = some (⟨30,(5),[9,10],[38],230⟩) from rfl))
private theorem rec2495 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[9,10],[34],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[52]? = some (⟨30,(6),[9,10],[34],95⟩) from rfl))
private theorem rec2496 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[9,10],[35],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[53]? = some (⟨30,(6),[9,10],[35],183⟩) from rfl))
private theorem rec2497 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[9,10],[38],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[54]? = some (⟨30,(6),[9,10],[38],232⟩) from rfl))
private theorem rec2519 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[9,10],[34],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[76]? = some (⟨30,(7),[9,10],[34],95⟩) from rfl))
private theorem rec2520 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[9,10],[35],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[77]? = some (⟨30,(7),[9,10],[35],183⟩) from rfl))
private theorem rec2521 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[9,10],[38],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[78]? = some (⟨30,(7),[9,10],[38],232⟩) from rfl))
private theorem rec2543 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[9,10],[34],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[100]? = some (⟨30,(8),[9,10],[34],96⟩) from rfl))
private theorem rec2544 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[9,10],[35],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[101]? = some (⟨30,(8),[9,10],[35],184⟩) from rfl))
private theorem rec2545 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[9,10],[38],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[102]? = some (⟨30,(8),[9,10],[38],233⟩) from rfl))
private theorem rec2567 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[9,10],[34],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[124]? = some (⟨30,(9),[9,10],[34],96⟩) from rfl))
private theorem rec2568 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[9,10],[35],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[125]? = some (⟨30,(9),[9,10],[35],184⟩) from rfl))
private theorem rec2569 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[9,10],[38],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[126]? = some (⟨30,(9),[9,10],[38],233⟩) from rfl))
private theorem rec2581 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[9,10],[34,35],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[138]? = some (⟨33,(0),[9,10],[34,35],2⟩) from rfl))
private theorem rec2582 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[139]? = some (⟨33,(0),[10],[38],2⟩) from rfl))
private theorem rec2593 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[9,10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[150]? = some (⟨33,(1),[9,10],[38],2⟩) from rfl))
private theorem rec2594 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[10],[34,35],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[151]? = some (⟨33,(1),[10],[34,35],2⟩) from rfl))
private theorem rec2607 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[164]? = some (⟨33,(2),[10],[34,35,38],3⟩) from rfl))
private theorem rec2618 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[175]? = some (⟨33,(3),[10],[34,35,38],3⟩) from rfl))
private theorem rec2630 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[9,10],[34,35],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[187]? = some (⟨33,(4),[9,10],[34,35],2⟩) from rfl))
private theorem rec2631 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[188]? = some (⟨33,(4),[10],[38],2⟩) from rfl))
private theorem rec2642 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[9,10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[199]? = some (⟨33,(5),[9,10],[38],2⟩) from rfl))
private theorem rec2643 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[10],[34,35],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[200]? = some (⟨33,(5),[10],[34,35],2⟩) from rfl))
private theorem rec2655 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[212]? = some (⟨33,(6),[10],[34,35,38],3⟩) from rfl))
private theorem rec2665 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[222]? = some (⟨33,(7),[10],[34,35,38],3⟩) from rfl))
private theorem rec2674 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[9,10],[34,35],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[231]? = some (⟨33,(8),[9,10],[34,35],97⟩) from rfl))
private theorem rec2675 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[9,10],[38],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[232]? = some (⟨33,(8),[9,10],[38],98⟩) from rfl))
private theorem rec2684 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[9,10],[34,35],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[241]? = some (⟨33,(9),[9,10],[34,35],98⟩) from rfl))
private theorem rec2685 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[9,10],[38],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[242]? = some (⟨33,(9),[9,10],[38],159⟩) from rfl))
private theorem rec2696 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[253]? = some (⟨33,(10),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec2704 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[261]? = some (⟨33,(11),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec2713 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[9,10],[34,35],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[270]? = some (⟨33,(12),[9,10],[34,35],99⟩) from rfl))
private theorem rec2714 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[10],[38],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[271]? = some (⟨33,(12),[10],[38],99⟩) from rfl))
private theorem rec2725 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[9,10],[38],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[282]? = some (⟨33,(13),[9,10],[38],99⟩) from rfl))
private theorem rec2726 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34, 35] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[10],[34,35],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[283]? = some (⟨33,(13),[10],[34,35],99⟩) from rfl))
private theorem rec2738 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[295]? = some (⟨33,(14),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec2749 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[306]? = some (⟨33,(15),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec2755 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[312]? = some (⟨35,(0),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec2760 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[317]? = some (⟨35,(1),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec2775 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[9,10],[35],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[332]? = some (⟨35,(2),[9,10],[35],101⟩) from rfl))
private theorem rec2776 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[9,10],[38],185⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[333]? = some (⟨35,(2),[9,10],[38],185⟩) from rfl))
private theorem rec2777 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[10],[34],121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[334]? = some (⟨35,(2),[10],[34],121⟩) from rfl))
private theorem rec2786 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[9,10],[34,38],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[343]? = some (⟨35,(3),[9,10],[34,38],101⟩) from rfl))
private theorem rec2787 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[9,10],[35],121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[344]? = some (⟨35,(3),[9,10],[35],121⟩) from rfl))
private theorem rec2792 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[349]? = some (⟨35,(4),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec2797 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[354]? = some (⟨35,(5),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec2812 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[9,10],[35],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[369]? = some (⟨35,(6),[9,10],[35],101⟩) from rfl))
private theorem rec2813 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[9,10],[38],186⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[370]? = some (⟨35,(6),[9,10],[38],186⟩) from rfl))
private theorem rec2814 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[10],[34],122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[371]? = some (⟨35,(6),[10],[34],122⟩) from rfl))
private theorem rec2823 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[9,10],[34,38],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[380]? = some (⟨35,(7),[9,10],[34,38],101⟩) from rfl))
private theorem rec2824 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[9,10],[35],122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[381]? = some (⟨35,(7),[9,10],[35],122⟩) from rfl))
private theorem rec2829 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[386]? = some (⟨35,(8),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec2834 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[391]? = some (⟨35,(9),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec2849 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[9,10],[35],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[406]? = some (⟨35,(10),[9,10],[35],101⟩) from rfl))
private theorem rec2850 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[9,10],[38],1396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[407]? = some (⟨35,(10),[9,10],[38],1396⟩) from rfl))
private theorem rec2851 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[10],[34],915⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[408]? = some (⟨35,(10),[10],[34],915⟩) from rfl))
private theorem rec2860 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[9,10],[34,38],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[417]? = some (⟨35,(11),[9,10],[34,38],101⟩) from rfl))
private theorem rec2861 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[9,10],[35],123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[418]? = some (⟨35,(11),[9,10],[35],123⟩) from rfl))
private theorem rec2866 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[423]? = some (⟨35,(12),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec2871 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[9,10],[34,35,38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[428]? = some (⟨35,(13),[9,10],[34,35,38],2⟩) from rfl))
private theorem rec2886 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[9,10],[35],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[443]? = some (⟨35,(14),[9,10],[35],101⟩) from rfl))
private theorem rec2887 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[9,10],[38],188⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[444]? = some (⟨35,(14),[9,10],[38],188⟩) from rfl))
private theorem rec2888 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[10],[34],124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[445]? = some (⟨35,(14),[10],[34],124⟩) from rfl))
private theorem rec2897 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 38] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[9,10],[34,38],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[454]? = some (⟨35,(15),[9,10],[34,38],101⟩) from rfl))
private theorem rec2898 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[9,10],[35],124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[455]? = some (⟨35,(15),[9,10],[35],124⟩) from rfl))
private theorem rec16264 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(0),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[56]? = some (⟨547,(0),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16267 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(1),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[59]? = some (⟨547,(1),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16270 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(2),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[62]? = some (⟨547,(2),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16273 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(3),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[65]? = some (⟨547,(3),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16276 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(4),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[68]? = some (⟨547,(4),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16279 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(5),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[71]? = some (⟨547,(5),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16282 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(6),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[74]? = some (⟨547,(6),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16285 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(7),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[77]? = some (⟨547,(7),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16288 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(8),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[80]? = some (⟨547,(8),[9,10],[34,35,38],3⟩) from rfl))
private theorem rec16291 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34, 35, 38] : List ℕ)) : section14Recorded section14Catalog si parent 547 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(9),[9,10],[34,35,38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[83]? = some (⟨547,(9),[9,10],[34,35,38],3⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 32).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 10).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(546,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(548,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(549,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(550,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 32).take 16 = [⟨4,32,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨4,33,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,34,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,35,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,36,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨4,37,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,38,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,39,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,40,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨4,41,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨4,42,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨4,43,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨4,44,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨4,45,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨4,46,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨4,47,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec461 10 32 (by decide) (by decide)
  · left
    exact rec461 10 33 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(546,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(548,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(549,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(550,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 546)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec509 10 34 (by decide) (by decide)
      · right
        exact rec526 10 34 (by decide) (by decide)
      · right
        exact rec543 10 34 (by decide) (by decide)
      · right
        exact rec560 10 34 (by decide) (by decide)
      · right
        exact rec577 10 34 (by decide) (by decide)
      · right
        exact rec594 10 34 (by decide) (by decide)
      · right
        exact rec611 10 34 (by decide) (by decide)
      · right
        exact rec628 10 34 (by decide) (by decide)
      · right
        exact rec645 10 34 (by decide) (by decide)
      · right
        exact rec662 10 34 (by decide) (by decide)
      · right
        exact rec679 10 34 (by decide) (by decide)
      · right
        exact rec696 10 34 (by decide) (by decide)
      · right
        exact rec713 10 34 (by decide) (by decide)
      · right
        exact rec730 10 34 (by decide) (by decide)
      · right
        exact rec747 10 34 (by decide) (by decide)
      · right
        exact rec764 10 34 (by decide) (by decide)
      · right
        exact rec781 10 34 (by decide) (by decide)
      · right
        exact rec798 10 34 (by decide) (by decide)
      · right
        exact rec815 10 34 (by decide) (by decide)
      · right
        exact rec832 10 34 (by decide) (by decide)
      · right
        exact rec849 10 34 (by decide) (by decide)
      · right
        exact rec866 10 34 (by decide) (by decide)
      · right
        exact rec883 10 34 (by decide) (by decide)
      · right
        exact rec900 10 34 (by decide) (by decide)
      · right
        exact rec917 10 34 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 547)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16264 10 34 (by decide) (by decide)
      · right
        exact rec16267 10 34 (by decide) (by decide)
      · right
        exact rec16270 10 34 (by decide) (by decide)
      · right
        exact rec16273 10 34 (by decide) (by decide)
      · right
        exact rec16276 10 34 (by decide) (by decide)
      · right
        exact rec16279 10 34 (by decide) (by decide)
      · right
        exact rec16282 10 34 (by decide) (by decide)
      · right
        exact rec16285 10 34 (by decide) (by decide)
      · right
        exact rec16288 10 34 (by decide) (by decide)
      · right
        exact rec16291 10 34 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1199 10 34 (by decide) (by decide)
      · right
        exact rec1206 10 34 (by decide) (by decide)
      · right
        exact rec1213 10 34 (by decide) (by decide)
      · right
        exact rec1220 10 34 (by decide) (by decide)
      · right
        exact rec1227 10 34 (by decide) (by decide)
      · right
        exact rec1234 10 34 (by decide) (by decide)
      · right
        exact rec1241 10 34 (by decide) (by decide)
      · right
        exact rec1248 10 34 (by decide) (by decide)
      · right
        exact rec1255 10 34 (by decide) (by decide)
      · right
        exact rec1262 10 34 (by decide) (by decide)
      · right
        exact rec1269 10 34 (by decide) (by decide)
      · right
        exact rec1276 10 34 (by decide) (by decide)
      · right
        exact rec1283 10 34 (by decide) (by decide)
      · right
        exact rec1290 10 34 (by decide) (by decide)
      · right
        exact rec1297 10 34 (by decide) (by decide)
      · right
        exact rec1304 10 34 (by decide) (by decide)
      · right
        exact rec1311 10 34 (by decide) (by decide)
      · right
        exact rec1318 10 34 (by decide) (by decide)
      · right
        exact rec1325 10 34 (by decide) (by decide)
      · right
        exact rec1332 10 34 (by decide) (by decide)
      · right
        exact rec1339 10 34 (by decide) (by decide)
      · right
        exact rec1346 10 34 (by decide) (by decide)
      · right
        exact rec1353 10 34 (by decide) (by decide)
      · right
        exact rec1360 10 34 (by decide) (by decide)
      · right
        exact rec1367 10 34 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1384 10 34 (by decide) (by decide)
      · right
        exact rec1408 10 34 (by decide) (by decide)
      · right
        exact rec1432 10 34 (by decide) (by decide)
      · right
        exact rec1456 10 34 (by decide) (by decide)
      · right
        exact rec1480 10 34 (by decide) (by decide)
      · right
        exact rec1501 10 34 (by decide) (by decide)
      · right
        exact rec1525 10 34 (by decide) (by decide)
      · right
        exact rec1549 10 34 (by decide) (by decide)
      · right
        exact rec1573 10 34 (by decide) (by decide)
      · right
        exact rec1597 10 34 (by decide) (by decide)
      · right
        exact rec1618 10 34 (by decide) (by decide)
      · right
        exact rec1642 10 34 (by decide) (by decide)
      · right
        exact rec1666 10 34 (by decide) (by decide)
      · right
        exact rec1690 10 34 (by decide) (by decide)
      · right
        exact rec1714 10 34 (by decide) (by decide)
      · right
        exact rec1735 10 34 (by decide) (by decide)
      · right
        exact rec1759 10 34 (by decide) (by decide)
      · right
        exact rec1783 10 34 (by decide) (by decide)
      · right
        exact rec1807 10 34 (by decide) (by decide)
      · right
        exact rec1831 10 34 (by decide) (by decide)
      · right
        exact rec1852 10 34 (by decide) (by decide)
      · right
        exact rec1876 10 34 (by decide) (by decide)
      · right
        exact rec1900 10 34 (by decide) (by decide)
      · right
        exact rec1924 10 34 (by decide) (by decide)
      · right
        exact rec1948 10 34 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1968 10 34 (by decide) (by decide)
      · right
        exact rec1984 10 34 (by decide) (by decide)
      · right
        exact rec2000 10 34 (by decide) (by decide)
      · right
        exact rec2016 10 34 (by decide) (by decide)
      · right
        exact rec2032 10 34 (by decide) (by decide)
      · right
        exact rec2048 10 34 (by decide) (by decide)
      · right
        exact rec2064 10 34 (by decide) (by decide)
      · right
        exact rec2080 10 34 (by decide) (by decide)
      · right
        exact rec2096 10 34 (by decide) (by decide)
      · right
        exact rec2112 10 34 (by decide) (by decide)
      · right
        exact rec2128 10 34 (by decide) (by decide)
      · right
        exact rec2144 10 34 (by decide) (by decide)
      · right
        exact rec2160 10 34 (by decide) (by decide)
      · right
        exact rec2176 10 34 (by decide) (by decide)
      · right
        exact rec2192 10 34 (by decide) (by decide)
      · right
        exact rec2208 10 34 (by decide) (by decide)
      · right
        exact rec2224 10 34 (by decide) (by decide)
      · right
        exact rec2240 10 34 (by decide) (by decide)
      · right
        exact rec2256 10 34 (by decide) (by decide)
      · right
        exact rec2272 10 34 (by decide) (by decide)
      · right
        exact rec2288 10 34 (by decide) (by decide)
      · right
        exact rec2304 10 34 (by decide) (by decide)
      · right
        exact rec2320 10 34 (by decide) (by decide)
      · right
        exact rec2336 10 34 (by decide) (by decide)
      · right
        exact rec2352 10 34 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 30)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2367 10 34 (by decide) (by decide)
      · right
        exact rec2382 10 34 (by decide) (by decide)
      · right
        exact rec2399 10 34 (by decide) (by decide)
      · right
        exact rec2423 10 34 (by decide) (by decide)
      · right
        exact rec2447 10 34 (by decide) (by decide)
      · right
        exact rec2471 10 34 (by decide) (by decide)
      · right
        exact rec2495 10 34 (by decide) (by decide)
      · right
        exact rec2519 10 34 (by decide) (by decide)
      · right
        exact rec2543 10 34 (by decide) (by decide)
      · right
        exact rec2567 10 34 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 549)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2581 10 34 (by decide) (by decide)
      · right
        exact rec2594 10 34 (by decide) (by decide)
      · right
        exact rec2607 10 34 (by decide) (by decide)
      · right
        exact rec2618 10 34 (by decide) (by decide)
      · right
        exact rec2630 10 34 (by decide) (by decide)
      · right
        exact rec2643 10 34 (by decide) (by decide)
      · right
        exact rec2655 10 34 (by decide) (by decide)
      · right
        exact rec2665 10 34 (by decide) (by decide)
      · right
        exact rec2674 10 34 (by decide) (by decide)
      · right
        exact rec2684 10 34 (by decide) (by decide)
      · right
        exact rec2696 10 34 (by decide) (by decide)
      · right
        exact rec2704 10 34 (by decide) (by decide)
      · right
        exact rec2713 10 34 (by decide) (by decide)
      · right
        exact rec2726 10 34 (by decide) (by decide)
      · right
        exact rec2738 10 34 (by decide) (by decide)
      · right
        exact rec2749 10 34 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2755 10 34 (by decide) (by decide)
      · right
        exact rec2760 10 34 (by decide) (by decide)
      · right
        exact rec2777 10 34 (by decide) (by decide)
      · right
        exact rec2786 10 34 (by decide) (by decide)
      · right
        exact rec2792 10 34 (by decide) (by decide)
      · right
        exact rec2797 10 34 (by decide) (by decide)
      · right
        exact rec2814 10 34 (by decide) (by decide)
      · right
        exact rec2823 10 34 (by decide) (by decide)
      · right
        exact rec2829 10 34 (by decide) (by decide)
      · right
        exact rec2834 10 34 (by decide) (by decide)
      · right
        exact rec2851 10 34 (by decide) (by decide)
      · right
        exact rec2860 10 34 (by decide) (by decide)
      · right
        exact rec2866 10 34 (by decide) (by decide)
      · right
        exact rec2871 10 34 (by decide) (by decide)
      · right
        exact rec2888 10 34 (by decide) (by decide)
      · right
        exact rec2897 10 34 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 550)).length = 2 := by decide +kernel
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
  · right
    intro gs hgs
    change gs ∈ [(546,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(548,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(549,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(550,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 546)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec507 10 35 (by decide) (by decide)
      · right
        exact rec524 10 35 (by decide) (by decide)
      · right
        exact rec541 10 35 (by decide) (by decide)
      · right
        exact rec560 10 35 (by decide) (by decide)
      · right
        exact rec575 10 35 (by decide) (by decide)
      · right
        exact rec592 10 35 (by decide) (by decide)
      · right
        exact rec609 10 35 (by decide) (by decide)
      · right
        exact rec626 10 35 (by decide) (by decide)
      · right
        exact rec645 10 35 (by decide) (by decide)
      · right
        exact rec660 10 35 (by decide) (by decide)
      · right
        exact rec677 10 35 (by decide) (by decide)
      · right
        exact rec694 10 35 (by decide) (by decide)
      · right
        exact rec711 10 35 (by decide) (by decide)
      · right
        exact rec730 10 35 (by decide) (by decide)
      · right
        exact rec745 10 35 (by decide) (by decide)
      · right
        exact rec762 10 35 (by decide) (by decide)
      · right
        exact rec779 10 35 (by decide) (by decide)
      · right
        exact rec796 10 35 (by decide) (by decide)
      · right
        exact rec815 10 35 (by decide) (by decide)
      · right
        exact rec830 10 35 (by decide) (by decide)
      · right
        exact rec847 10 35 (by decide) (by decide)
      · right
        exact rec864 10 35 (by decide) (by decide)
      · right
        exact rec881 10 35 (by decide) (by decide)
      · right
        exact rec900 10 35 (by decide) (by decide)
      · right
        exact rec915 10 35 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 547)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16264 10 35 (by decide) (by decide)
      · right
        exact rec16267 10 35 (by decide) (by decide)
      · right
        exact rec16270 10 35 (by decide) (by decide)
      · right
        exact rec16273 10 35 (by decide) (by decide)
      · right
        exact rec16276 10 35 (by decide) (by decide)
      · right
        exact rec16279 10 35 (by decide) (by decide)
      · right
        exact rec16282 10 35 (by decide) (by decide)
      · right
        exact rec16285 10 35 (by decide) (by decide)
      · right
        exact rec16288 10 35 (by decide) (by decide)
      · right
        exact rec16291 10 35 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1199 10 35 (by decide) (by decide)
      · right
        exact rec1206 10 35 (by decide) (by decide)
      · right
        exact rec1213 10 35 (by decide) (by decide)
      · right
        exact rec1220 10 35 (by decide) (by decide)
      · right
        exact rec1227 10 35 (by decide) (by decide)
      · right
        exact rec1234 10 35 (by decide) (by decide)
      · right
        exact rec1241 10 35 (by decide) (by decide)
      · right
        exact rec1248 10 35 (by decide) (by decide)
      · right
        exact rec1255 10 35 (by decide) (by decide)
      · right
        exact rec1262 10 35 (by decide) (by decide)
      · right
        exact rec1269 10 35 (by decide) (by decide)
      · right
        exact rec1276 10 35 (by decide) (by decide)
      · right
        exact rec1283 10 35 (by decide) (by decide)
      · right
        exact rec1290 10 35 (by decide) (by decide)
      · right
        exact rec1297 10 35 (by decide) (by decide)
      · right
        exact rec1304 10 35 (by decide) (by decide)
      · right
        exact rec1311 10 35 (by decide) (by decide)
      · right
        exact rec1318 10 35 (by decide) (by decide)
      · right
        exact rec1325 10 35 (by decide) (by decide)
      · right
        exact rec1332 10 35 (by decide) (by decide)
      · right
        exact rec1339 10 35 (by decide) (by decide)
      · right
        exact rec1346 10 35 (by decide) (by decide)
      · right
        exact rec1353 10 35 (by decide) (by decide)
      · right
        exact rec1360 10 35 (by decide) (by decide)
      · right
        exact rec1367 10 35 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1385 10 35 (by decide) (by decide)
      · right
        exact rec1409 10 35 (by decide) (by decide)
      · right
        exact rec1433 10 35 (by decide) (by decide)
      · right
        exact rec1457 10 35 (by decide) (by decide)
      · right
        exact rec1481 10 35 (by decide) (by decide)
      · right
        exact rec1502 10 35 (by decide) (by decide)
      · right
        exact rec1526 10 35 (by decide) (by decide)
      · right
        exact rec1550 10 35 (by decide) (by decide)
      · right
        exact rec1574 10 35 (by decide) (by decide)
      · right
        exact rec1598 10 35 (by decide) (by decide)
      · right
        exact rec1619 10 35 (by decide) (by decide)
      · right
        exact rec1643 10 35 (by decide) (by decide)
      · right
        exact rec1667 10 35 (by decide) (by decide)
      · right
        exact rec1691 10 35 (by decide) (by decide)
      · right
        exact rec1715 10 35 (by decide) (by decide)
      · right
        exact rec1736 10 35 (by decide) (by decide)
      · right
        exact rec1760 10 35 (by decide) (by decide)
      · right
        exact rec1784 10 35 (by decide) (by decide)
      · right
        exact rec1808 10 35 (by decide) (by decide)
      · right
        exact rec1832 10 35 (by decide) (by decide)
      · right
        exact rec1853 10 35 (by decide) (by decide)
      · right
        exact rec1877 10 35 (by decide) (by decide)
      · right
        exact rec1901 10 35 (by decide) (by decide)
      · right
        exact rec1925 10 35 (by decide) (by decide)
      · right
        exact rec1949 10 35 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1966 10 35 (by decide) (by decide)
      · right
        exact rec1982 10 35 (by decide) (by decide)
      · right
        exact rec1998 10 35 (by decide) (by decide)
      · right
        exact rec2014 10 35 (by decide) (by decide)
      · right
        exact rec2030 10 35 (by decide) (by decide)
      · right
        exact rec2046 10 35 (by decide) (by decide)
      · right
        exact rec2062 10 35 (by decide) (by decide)
      · right
        exact rec2078 10 35 (by decide) (by decide)
      · right
        exact rec2094 10 35 (by decide) (by decide)
      · right
        exact rec2110 10 35 (by decide) (by decide)
      · right
        exact rec2126 10 35 (by decide) (by decide)
      · right
        exact rec2142 10 35 (by decide) (by decide)
      · right
        exact rec2158 10 35 (by decide) (by decide)
      · right
        exact rec2174 10 35 (by decide) (by decide)
      · right
        exact rec2190 10 35 (by decide) (by decide)
      · right
        exact rec2206 10 35 (by decide) (by decide)
      · right
        exact rec2222 10 35 (by decide) (by decide)
      · right
        exact rec2238 10 35 (by decide) (by decide)
      · right
        exact rec2254 10 35 (by decide) (by decide)
      · right
        exact rec2270 10 35 (by decide) (by decide)
      · right
        exact rec2286 10 35 (by decide) (by decide)
      · right
        exact rec2302 10 35 (by decide) (by decide)
      · right
        exact rec2318 10 35 (by decide) (by decide)
      · right
        exact rec2334 10 35 (by decide) (by decide)
      · right
        exact rec2350 10 35 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 30)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2367 10 35 (by decide) (by decide)
      · right
        exact rec2382 10 35 (by decide) (by decide)
      · right
        exact rec2400 10 35 (by decide) (by decide)
      · right
        exact rec2424 10 35 (by decide) (by decide)
      · right
        exact rec2448 10 35 (by decide) (by decide)
      · right
        exact rec2472 10 35 (by decide) (by decide)
      · right
        exact rec2496 10 35 (by decide) (by decide)
      · right
        exact rec2520 10 35 (by decide) (by decide)
      · right
        exact rec2544 10 35 (by decide) (by decide)
      · right
        exact rec2568 10 35 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 549)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2581 10 35 (by decide) (by decide)
      · right
        exact rec2594 10 35 (by decide) (by decide)
      · right
        exact rec2607 10 35 (by decide) (by decide)
      · right
        exact rec2618 10 35 (by decide) (by decide)
      · right
        exact rec2630 10 35 (by decide) (by decide)
      · right
        exact rec2643 10 35 (by decide) (by decide)
      · right
        exact rec2655 10 35 (by decide) (by decide)
      · right
        exact rec2665 10 35 (by decide) (by decide)
      · right
        exact rec2674 10 35 (by decide) (by decide)
      · right
        exact rec2684 10 35 (by decide) (by decide)
      · right
        exact rec2696 10 35 (by decide) (by decide)
      · right
        exact rec2704 10 35 (by decide) (by decide)
      · right
        exact rec2713 10 35 (by decide) (by decide)
      · right
        exact rec2726 10 35 (by decide) (by decide)
      · right
        exact rec2738 10 35 (by decide) (by decide)
      · right
        exact rec2749 10 35 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2755 10 35 (by decide) (by decide)
      · right
        exact rec2760 10 35 (by decide) (by decide)
      · right
        exact rec2775 10 35 (by decide) (by decide)
      · right
        exact rec2787 10 35 (by decide) (by decide)
      · right
        exact rec2792 10 35 (by decide) (by decide)
      · right
        exact rec2797 10 35 (by decide) (by decide)
      · right
        exact rec2812 10 35 (by decide) (by decide)
      · right
        exact rec2824 10 35 (by decide) (by decide)
      · right
        exact rec2829 10 35 (by decide) (by decide)
      · right
        exact rec2834 10 35 (by decide) (by decide)
      · right
        exact rec2849 10 35 (by decide) (by decide)
      · right
        exact rec2861 10 35 (by decide) (by decide)
      · right
        exact rec2866 10 35 (by decide) (by decide)
      · right
        exact rec2871 10 35 (by decide) (by decide)
      · right
        exact rec2886 10 35 (by decide) (by decide)
      · right
        exact rec2898 10 35 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 550)).length = 2 := by decide +kernel
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
    exact rec461 10 36 (by decide) (by decide)
  · left
    exact rec461 10 37 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(546,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(548,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(549,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(550,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 546)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec508 10 38 (by decide) (by decide)
      · right
        exact rec525 10 38 (by decide) (by decide)
      · right
        exact rec542 10 38 (by decide) (by decide)
      · right
        exact rec559 10 38 (by decide) (by decide)
      · right
        exact rec576 10 38 (by decide) (by decide)
      · right
        exact rec593 10 38 (by decide) (by decide)
      · right
        exact rec610 10 38 (by decide) (by decide)
      · right
        exact rec627 10 38 (by decide) (by decide)
      · right
        exact rec644 10 38 (by decide) (by decide)
      · right
        exact rec661 10 38 (by decide) (by decide)
      · right
        exact rec678 10 38 (by decide) (by decide)
      · right
        exact rec695 10 38 (by decide) (by decide)
      · right
        exact rec712 10 38 (by decide) (by decide)
      · right
        exact rec729 10 38 (by decide) (by decide)
      · right
        exact rec746 10 38 (by decide) (by decide)
      · right
        exact rec763 10 38 (by decide) (by decide)
      · right
        exact rec780 10 38 (by decide) (by decide)
      · right
        exact rec797 10 38 (by decide) (by decide)
      · right
        exact rec814 10 38 (by decide) (by decide)
      · right
        exact rec831 10 38 (by decide) (by decide)
      · right
        exact rec848 10 38 (by decide) (by decide)
      · right
        exact rec865 10 38 (by decide) (by decide)
      · right
        exact rec882 10 38 (by decide) (by decide)
      · right
        exact rec899 10 38 (by decide) (by decide)
      · right
        exact rec916 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 547)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16264 10 38 (by decide) (by decide)
      · right
        exact rec16267 10 38 (by decide) (by decide)
      · right
        exact rec16270 10 38 (by decide) (by decide)
      · right
        exact rec16273 10 38 (by decide) (by decide)
      · right
        exact rec16276 10 38 (by decide) (by decide)
      · right
        exact rec16279 10 38 (by decide) (by decide)
      · right
        exact rec16282 10 38 (by decide) (by decide)
      · right
        exact rec16285 10 38 (by decide) (by decide)
      · right
        exact rec16288 10 38 (by decide) (by decide)
      · right
        exact rec16291 10 38 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1199 10 38 (by decide) (by decide)
      · right
        exact rec1206 10 38 (by decide) (by decide)
      · right
        exact rec1213 10 38 (by decide) (by decide)
      · right
        exact rec1220 10 38 (by decide) (by decide)
      · right
        exact rec1227 10 38 (by decide) (by decide)
      · right
        exact rec1234 10 38 (by decide) (by decide)
      · right
        exact rec1241 10 38 (by decide) (by decide)
      · right
        exact rec1248 10 38 (by decide) (by decide)
      · right
        exact rec1255 10 38 (by decide) (by decide)
      · right
        exact rec1262 10 38 (by decide) (by decide)
      · right
        exact rec1269 10 38 (by decide) (by decide)
      · right
        exact rec1276 10 38 (by decide) (by decide)
      · right
        exact rec1283 10 38 (by decide) (by decide)
      · right
        exact rec1290 10 38 (by decide) (by decide)
      · right
        exact rec1297 10 38 (by decide) (by decide)
      · right
        exact rec1304 10 38 (by decide) (by decide)
      · right
        exact rec1311 10 38 (by decide) (by decide)
      · right
        exact rec1318 10 38 (by decide) (by decide)
      · right
        exact rec1325 10 38 (by decide) (by decide)
      · right
        exact rec1332 10 38 (by decide) (by decide)
      · right
        exact rec1339 10 38 (by decide) (by decide)
      · right
        exact rec1346 10 38 (by decide) (by decide)
      · right
        exact rec1353 10 38 (by decide) (by decide)
      · right
        exact rec1360 10 38 (by decide) (by decide)
      · right
        exact rec1367 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1386 10 38 (by decide) (by decide)
      · right
        exact rec1410 10 38 (by decide) (by decide)
      · right
        exact rec1434 10 38 (by decide) (by decide)
      · right
        exact rec1458 10 38 (by decide) (by decide)
      · right
        exact rec1482 10 38 (by decide) (by decide)
      · right
        exact rec1503 10 38 (by decide) (by decide)
      · right
        exact rec1527 10 38 (by decide) (by decide)
      · right
        exact rec1551 10 38 (by decide) (by decide)
      · right
        exact rec1575 10 38 (by decide) (by decide)
      · right
        exact rec1599 10 38 (by decide) (by decide)
      · right
        exact rec1620 10 38 (by decide) (by decide)
      · right
        exact rec1644 10 38 (by decide) (by decide)
      · right
        exact rec1668 10 38 (by decide) (by decide)
      · right
        exact rec1692 10 38 (by decide) (by decide)
      · right
        exact rec1716 10 38 (by decide) (by decide)
      · right
        exact rec1737 10 38 (by decide) (by decide)
      · right
        exact rec1761 10 38 (by decide) (by decide)
      · right
        exact rec1785 10 38 (by decide) (by decide)
      · right
        exact rec1809 10 38 (by decide) (by decide)
      · right
        exact rec1833 10 38 (by decide) (by decide)
      · right
        exact rec1854 10 38 (by decide) (by decide)
      · right
        exact rec1878 10 38 (by decide) (by decide)
      · right
        exact rec1902 10 38 (by decide) (by decide)
      · right
        exact rec1926 10 38 (by decide) (by decide)
      · right
        exact rec1950 10 38 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1967 10 38 (by decide) (by decide)
      · right
        exact rec1983 10 38 (by decide) (by decide)
      · right
        exact rec1999 10 38 (by decide) (by decide)
      · right
        exact rec2015 10 38 (by decide) (by decide)
      · right
        exact rec2031 10 38 (by decide) (by decide)
      · right
        exact rec2047 10 38 (by decide) (by decide)
      · right
        exact rec2063 10 38 (by decide) (by decide)
      · right
        exact rec2079 10 38 (by decide) (by decide)
      · right
        exact rec2095 10 38 (by decide) (by decide)
      · right
        exact rec2111 10 38 (by decide) (by decide)
      · right
        exact rec2127 10 38 (by decide) (by decide)
      · right
        exact rec2143 10 38 (by decide) (by decide)
      · right
        exact rec2159 10 38 (by decide) (by decide)
      · right
        exact rec2175 10 38 (by decide) (by decide)
      · right
        exact rec2191 10 38 (by decide) (by decide)
      · right
        exact rec2207 10 38 (by decide) (by decide)
      · right
        exact rec2223 10 38 (by decide) (by decide)
      · right
        exact rec2239 10 38 (by decide) (by decide)
      · right
        exact rec2255 10 38 (by decide) (by decide)
      · right
        exact rec2271 10 38 (by decide) (by decide)
      · right
        exact rec2287 10 38 (by decide) (by decide)
      · right
        exact rec2303 10 38 (by decide) (by decide)
      · right
        exact rec2319 10 38 (by decide) (by decide)
      · right
        exact rec2335 10 38 (by decide) (by decide)
      · right
        exact rec2351 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 30)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2367 10 38 (by decide) (by decide)
      · right
        exact rec2382 10 38 (by decide) (by decide)
      · right
        exact rec2401 10 38 (by decide) (by decide)
      · right
        exact rec2425 10 38 (by decide) (by decide)
      · right
        exact rec2449 10 38 (by decide) (by decide)
      · right
        exact rec2473 10 38 (by decide) (by decide)
      · right
        exact rec2497 10 38 (by decide) (by decide)
      · right
        exact rec2521 10 38 (by decide) (by decide)
      · right
        exact rec2545 10 38 (by decide) (by decide)
      · right
        exact rec2569 10 38 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 549)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2582 10 38 (by decide) (by decide)
      · right
        exact rec2593 10 38 (by decide) (by decide)
      · right
        exact rec2607 10 38 (by decide) (by decide)
      · right
        exact rec2618 10 38 (by decide) (by decide)
      · right
        exact rec2631 10 38 (by decide) (by decide)
      · right
        exact rec2642 10 38 (by decide) (by decide)
      · right
        exact rec2655 10 38 (by decide) (by decide)
      · right
        exact rec2665 10 38 (by decide) (by decide)
      · right
        exact rec2675 10 38 (by decide) (by decide)
      · right
        exact rec2685 10 38 (by decide) (by decide)
      · right
        exact rec2696 10 38 (by decide) (by decide)
      · right
        exact rec2704 10 38 (by decide) (by decide)
      · right
        exact rec2714 10 38 (by decide) (by decide)
      · right
        exact rec2725 10 38 (by decide) (by decide)
      · right
        exact rec2738 10 38 (by decide) (by decide)
      · right
        exact rec2749 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2755 10 38 (by decide) (by decide)
      · right
        exact rec2760 10 38 (by decide) (by decide)
      · right
        exact rec2776 10 38 (by decide) (by decide)
      · right
        exact rec2786 10 38 (by decide) (by decide)
      · right
        exact rec2792 10 38 (by decide) (by decide)
      · right
        exact rec2797 10 38 (by decide) (by decide)
      · right
        exact rec2813 10 38 (by decide) (by decide)
      · right
        exact rec2823 10 38 (by decide) (by decide)
      · right
        exact rec2829 10 38 (by decide) (by decide)
      · right
        exact rec2834 10 38 (by decide) (by decide)
      · right
        exact rec2850 10 38 (by decide) (by decide)
      · right
        exact rec2860 10 38 (by decide) (by decide)
      · right
        exact rec2866 10 38 (by decide) (by decide)
      · right
        exact rec2871 10 38 (by decide) (by decide)
      · right
        exact rec2887 10 38 (by decide) (by decide)
      · right
        exact rec2897 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 550)).length = 2 := by decide +kernel
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
    exact rec480 10 39 (by decide) (by decide)
  · left
    exact rec461 10 40 (by decide) (by decide)
  · left
    exact rec461 10 41 (by decide) (by decide)
  · left
    exact rec473 10 42 (by decide) (by decide)
  · left
    exact rec474 10 43 (by decide) (by decide)
  · left
    exact rec461 10 44 (by decide) (by decide)
  · left
    exact rec461 10 45 (by decide) (by decide)
  · left
    exact rec481 10 46 (by decide) (by decide)
  · left
    exact rec475 10 47 (by decide) (by decide)
end Section14Coverage_10_1_p32_48

#print axioms solution
