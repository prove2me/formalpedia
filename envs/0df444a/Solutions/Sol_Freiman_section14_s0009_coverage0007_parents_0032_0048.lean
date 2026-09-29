-- Prove2me | solution 1 for Freiman.section14_s0009_coverage0007_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T19:52:35.262347+00:00
-- url     : https://prove2.me/submissions/821a439d-8aa6-46f4-9214-871d6bc5b2a1

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
namespace Section14Coverage_9_7_p32_48
private theorem rec13316 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[868]? = some (⟨260,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) from rfl))
private theorem rec13320 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[9,10],[34],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[872]? = some (⟨260,(-1),[9,10],[34],884⟩) from rfl))
private theorem rec13321 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35, 39, 43, 47] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[9,10],[35,39,43,47],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[873]? = some (⟨260,(-1),[9,10],[35,39,43,47],886⟩) from rfl))
private theorem rec13322 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[9,10],[38],887⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[874]? = some (⟨260,(-1),[9,10],[38],887⟩) from rfl))
private theorem rec13323 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[9,10],[46],909⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[875]? = some (⟨260,(-1),[9,10],[46],909⟩) from rfl))
private theorem rec13331 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(0),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[883]? = some (⟨262,(0),[9],[42],3⟩) from rfl))
private theorem rec13333 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(1),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[885]? = some (⟨262,(1),[9],[42],3⟩) from rfl))
private theorem rec13335 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(2),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[887]? = some (⟨262,(2),[9],[42],3⟩) from rfl))
private theorem rec13337 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(3),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[889]? = some (⟨262,(3),[9],[42],3⟩) from rfl))
private theorem rec13339 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(4),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[891]? = some (⟨262,(4),[9],[42],3⟩) from rfl))
private theorem rec13341 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(5),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[893]? = some (⟨262,(5),[9],[42],3⟩) from rfl))
private theorem rec13343 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(6),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[895]? = some (⟨262,(6),[9],[42],3⟩) from rfl))
private theorem rec13345 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(7),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[897]? = some (⟨262,(7),[9],[42],3⟩) from rfl))
private theorem rec13347 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(8),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[899]? = some (⟨262,(8),[9],[42],3⟩) from rfl))
private theorem rec13349 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(9),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[901]? = some (⟨262,(9),[9],[42],3⟩) from rfl))
private theorem rec13351 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(10),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[903]? = some (⟨262,(10),[9],[42],3⟩) from rfl))
private theorem rec13353 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(11),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[905]? = some (⟨262,(11),[9],[42],3⟩) from rfl))
private theorem rec13355 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(12),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[907]? = some (⟨262,(12),[9],[42],3⟩) from rfl))
private theorem rec13357 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(13),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[909]? = some (⟨262,(13),[9],[42],3⟩) from rfl))
private theorem rec13359 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(14),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[911]? = some (⟨262,(14),[9],[42],3⟩) from rfl))
private theorem rec13361 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(15),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[913]? = some (⟨262,(15),[9],[42],3⟩) from rfl))
private theorem rec13363 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(16),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[915]? = some (⟨262,(16),[9],[42],3⟩) from rfl))
private theorem rec13365 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(17),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[917]? = some (⟨262,(17),[9],[42],3⟩) from rfl))
private theorem rec13367 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(18),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[919]? = some (⟨262,(18),[9],[42],3⟩) from rfl))
private theorem rec13369 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(19),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[921]? = some (⟨262,(19),[9],[42],3⟩) from rfl))
private theorem rec13371 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(20),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[923]? = some (⟨262,(20),[9],[42],3⟩) from rfl))
private theorem rec13373 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(21),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[925]? = some (⟨262,(21),[9],[42],3⟩) from rfl))
private theorem rec13375 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(22),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[927]? = some (⟨262,(22),[9],[42],3⟩) from rfl))
private theorem rec13377 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(23),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[929]? = some (⟨262,(23),[9],[42],3⟩) from rfl))
private theorem rec13379 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 262 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨262,(24),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[931]? = some (⟨262,(24),[9],[42],3⟩) from rfl))
private theorem rec13432 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(0),[9],[42],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[984]? = some (⟨267,(0),[9],[42],1086⟩) from rfl))
private theorem rec13435 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(1),[9],[42],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[987]? = some (⟨267,(1),[9],[42],1087⟩) from rfl))
private theorem rec13438 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(2),[9],[42],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[990]? = some (⟨267,(2),[9],[42],1088⟩) from rfl))
private theorem rec13441 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(3),[9],[42],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[993]? = some (⟨267,(3),[9],[42],1089⟩) from rfl))
private theorem rec13444 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(4),[9],[42],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[996]? = some (⟨267,(4),[9],[42],1086⟩) from rfl))
private theorem rec13447 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(5),[9],[42],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[999]? = some (⟨267,(5),[9],[42],1087⟩) from rfl))
private theorem rec13450 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(6),[9],[42],1090⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1002]? = some (⟨267,(6),[9],[42],1090⟩) from rfl))
private theorem rec13453 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(7),[9],[42],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1005]? = some (⟨267,(7),[9],[42],1089⟩) from rfl))
private theorem rec13456 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(8),[9],[42],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1008]? = some (⟨267,(8),[9],[42],1086⟩) from rfl))
private theorem rec13459 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(9),[9],[42],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1011]? = some (⟨267,(9),[9],[42],1087⟩) from rfl))
private theorem rec13462 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(10),[9],[42],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1014]? = some (⟨267,(10),[9],[42],1088⟩) from rfl))
private theorem rec13465 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(11),[9],[42],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1017]? = some (⟨267,(11),[9],[42],1089⟩) from rfl))
private theorem rec13468 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(12),[9],[42],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1020]? = some (⟨267,(12),[9],[42],1086⟩) from rfl))
private theorem rec13471 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(13),[9],[42],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1023]? = some (⟨267,(13),[9],[42],1087⟩) from rfl))
private theorem rec13474 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(14),[9],[42],1091⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1026]? = some (⟨267,(14),[9],[42],1091⟩) from rfl))
private theorem rec13477 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 267 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨267,(15),[9],[42],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1029]? = some (⟨267,(15),[9],[42],1089⟩) from rfl))
private theorem rec13480 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(0),[9],[42],1414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1032]? = some (⟨270,(0),[9],[42],1414⟩) from rfl))
private theorem rec13483 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(1),[9],[42],1415⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1035]? = some (⟨270,(1),[9],[42],1415⟩) from rfl))
private theorem rec13486 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(2),[9],[42],1414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1038]? = some (⟨270,(2),[9],[42],1414⟩) from rfl))
private theorem rec13489 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(3),[9],[42],1416⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1041]? = some (⟨270,(3),[9],[42],1416⟩) from rfl))
private theorem rec13492 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(4),[9],[42],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1044]? = some (⟨270,(4),[9],[42],1417⟩) from rfl))
private theorem rec13495 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(5),[9],[42],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1047]? = some (⟨270,(5),[9],[42],1417⟩) from rfl))
private theorem rec13498 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(6),[9],[42],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1050]? = some (⟨270,(6),[9],[42],1417⟩) from rfl))
private theorem rec13501 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(7),[9],[42],1417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1053]? = some (⟨270,(7),[9],[42],1417⟩) from rfl))
private theorem rec13504 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(8),[9],[42],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1056]? = some (⟨270,(8),[9],[42],1418⟩) from rfl))
private theorem rec13507 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(9),[9],[42],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1059]? = some (⟨270,(9),[9],[42],1418⟩) from rfl))
private theorem rec13510 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(10),[9],[42],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1062]? = some (⟨270,(10),[9],[42],1418⟩) from rfl))
private theorem rec13513 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(11),[9],[42],1418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1065]? = some (⟨270,(11),[9],[42],1418⟩) from rfl))
private theorem rec13516 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(12),[9],[42],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1068]? = some (⟨270,(12),[9],[42],1419⟩) from rfl))
private theorem rec13519 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(13),[9],[42],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1071]? = some (⟨270,(13),[9],[42],1419⟩) from rfl))
private theorem rec13522 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(14),[9],[42],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1074]? = some (⟨270,(14),[9],[42],1419⟩) from rfl))
private theorem rec13525 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 270 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨270,(15),[9],[42],1419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1077]? = some (⟨270,(15),[9],[42],1419⟩) from rfl))
private theorem rec13528 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(0),[9],[42],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1080]? = some (⟨273,(0),[9],[42],1098⟩) from rfl))
private theorem rec13531 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(1),[9],[42],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1083]? = some (⟨273,(1),[9],[42],1099⟩) from rfl))
private theorem rec13534 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(2),[9],[42],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1086]? = some (⟨273,(2),[9],[42],1100⟩) from rfl))
private theorem rec13537 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(3),[9],[42],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1089]? = some (⟨273,(3),[9],[42],1100⟩) from rfl))
private theorem rec13540 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(4),[9],[42],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1092]? = some (⟨273,(4),[9],[42],1100⟩) from rfl))
private theorem rec13543 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(5),[9],[42],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1095]? = some (⟨273,(5),[9],[42],1098⟩) from rfl))
private theorem rec13546 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(6),[9],[42],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1098]? = some (⟨273,(6),[9],[42],1099⟩) from rfl))
private theorem rec13549 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(7),[9],[42],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1101]? = some (⟨273,(7),[9],[42],1101⟩) from rfl))
private theorem rec13552 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(8),[9],[42],1102⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1104]? = some (⟨273,(8),[9],[42],1102⟩) from rfl))
private theorem rec13555 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 273 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨273,(9),[9],[42],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1107]? = some (⟨273,(9),[9],[42],1101⟩) from rfl))
private theorem rec13558 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(0),[9],[42],1420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1110]? = some (⟨275,(0),[9],[42],1420⟩) from rfl))
private theorem rec13561 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(1),[9],[42],1420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1113]? = some (⟨275,(1),[9],[42],1420⟩) from rfl))
private theorem rec13564 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(2),[9],[42],1421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1116]? = some (⟨275,(2),[9],[42],1421⟩) from rfl))
private theorem rec13567 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(3),[9],[42],1422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1119]? = some (⟨275,(3),[9],[42],1422⟩) from rfl))
private theorem rec13570 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(4),[9],[42],1423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1122]? = some (⟨275,(4),[9],[42],1423⟩) from rfl))
private theorem rec13573 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(5),[9],[42],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1125]? = some (⟨275,(5),[9],[42],1424⟩) from rfl))
private theorem rec13576 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(6),[9],[42],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1128]? = some (⟨275,(6),[9],[42],1424⟩) from rfl))
private theorem rec13579 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(7),[9],[42],1424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1131]? = some (⟨275,(7),[9],[42],1424⟩) from rfl))
private theorem rec13582 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(8),[9],[42],1422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1134]? = some (⟨275,(8),[9],[42],1422⟩) from rfl))
private theorem rec13585 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 275 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨275,(9),[9],[42],1423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1137]? = some (⟨275,(9),[9],[42],1423⟩) from rfl))
private theorem rec13588 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(0),[9],[42],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1140]? = some (⟨278,(0),[9],[42],1108⟩) from rfl))
private theorem rec13591 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(1),[9],[42],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1143]? = some (⟨278,(1),[9],[42],1109⟩) from rfl))
private theorem rec13594 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(2),[9],[42],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1146]? = some (⟨278,(2),[9],[42],1110⟩) from rfl))
private theorem rec13597 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(3),[9],[42],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1149]? = some (⟨278,(3),[9],[42],1110⟩) from rfl))
private theorem rec13600 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(4),[9],[42],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1152]? = some (⟨278,(4),[9],[42],1110⟩) from rfl))
private theorem rec13603 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(5),[9],[42],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[0]? = some (⟨278,(5),[9],[42],1108⟩) from rfl))
private theorem rec13606 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(6),[9],[42],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[3]? = some (⟨278,(6),[9],[42],1109⟩) from rfl))
private theorem rec13609 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(7),[9],[42],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[6]? = some (⟨278,(7),[9],[42],1111⟩) from rfl))
private theorem rec13612 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(8),[9],[42],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[9]? = some (⟨278,(8),[9],[42],1112⟩) from rfl))
private theorem rec13615 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(9),[9],[42],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[12]? = some (⟨278,(9),[9],[42],1111⟩) from rfl))
private theorem rec13618 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(10),[9],[42],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[15]? = some (⟨278,(10),[9],[42],1108⟩) from rfl))
private theorem rec13621 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(11),[9],[42],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[18]? = some (⟨278,(11),[9],[42],1109⟩) from rfl))
private theorem rec13624 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(12),[9],[42],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[21]? = some (⟨278,(12),[9],[42],1113⟩) from rfl))
private theorem rec13627 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(13),[9],[42],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[24]? = some (⟨278,(13),[9],[42],1112⟩) from rfl))
private theorem rec13630 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(14),[9],[42],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[27]? = some (⟨278,(14),[9],[42],1113⟩) from rfl))
private theorem rec13633 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(15),[9],[42],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[30]? = some (⟨278,(15),[9],[42],1108⟩) from rfl))
private theorem rec13636 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(16),[9],[42],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[33]? = some (⟨278,(16),[9],[42],1109⟩) from rfl))
private theorem rec13639 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(17),[9],[42],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[36]? = some (⟨278,(17),[9],[42],1111⟩) from rfl))
private theorem rec13642 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(18),[9],[42],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[39]? = some (⟨278,(18),[9],[42],1112⟩) from rfl))
private theorem rec13645 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(19),[9],[42],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[42]? = some (⟨278,(19),[9],[42],1111⟩) from rfl))
private theorem rec13648 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(20),[9],[42],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[45]? = some (⟨278,(20),[9],[42],1108⟩) from rfl))
private theorem rec13651 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(21),[9],[42],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[48]? = some (⟨278,(21),[9],[42],1109⟩) from rfl))
private theorem rec13654 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(22),[9],[42],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[51]? = some (⟨278,(22),[9],[42],1114⟩) from rfl))
private theorem rec13657 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(23),[9],[42],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[54]? = some (⟨278,(23),[9],[42],1112⟩) from rfl))
private theorem rec13660 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 278 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨278,(24),[9],[42],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[57]? = some (⟨278,(24),[9],[42],1114⟩) from rfl))
private theorem rec13663 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(0),[9],[42],1425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[60]? = some (⟨280,(0),[9],[42],1425⟩) from rfl))
private theorem rec13666 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(1),[9],[42],1425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[63]? = some (⟨280,(1),[9],[42],1425⟩) from rfl))
private theorem rec13669 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(2),[9],[42],1426⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[66]? = some (⟨280,(2),[9],[42],1426⟩) from rfl))
private theorem rec13672 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(3),[9],[42],1427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[69]? = some (⟨280,(3),[9],[42],1427⟩) from rfl))
private theorem rec13675 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(4),[9],[42],1428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[72]? = some (⟨280,(4),[9],[42],1428⟩) from rfl))
private theorem rec13678 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(5),[9],[42],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[75]? = some (⟨280,(5),[9],[42],1429⟩) from rfl))
private theorem rec13681 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(6),[9],[42],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[78]? = some (⟨280,(6),[9],[42],1429⟩) from rfl))
private theorem rec13684 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(7),[9],[42],1429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[81]? = some (⟨280,(7),[9],[42],1429⟩) from rfl))
private theorem rec13687 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(8),[9],[42],1427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[84]? = some (⟨280,(8),[9],[42],1427⟩) from rfl))
private theorem rec13690 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 280 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨280,(9),[9],[42],1428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[87]? = some (⟨280,(9),[9],[42],1428⟩) from rfl))
private theorem rec13693 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(0),[9],[42],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[90]? = some (⟨283,(0),[9],[42],1120⟩) from rfl))
private theorem rec13696 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(1),[9],[42],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[93]? = some (⟨283,(1),[9],[42],1121⟩) from rfl))
private theorem rec13699 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(2),[9],[42],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[96]? = some (⟨283,(2),[9],[42],1122⟩) from rfl))
private theorem rec13702 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(3),[9],[42],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[99]? = some (⟨283,(3),[9],[42],1122⟩) from rfl))
private theorem rec13705 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(4),[9],[42],1123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[102]? = some (⟨283,(4),[9],[42],1123⟩) from rfl))
private theorem rec13708 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(5),[9],[42],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[105]? = some (⟨283,(5),[9],[42],1120⟩) from rfl))
private theorem rec13711 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(6),[9],[42],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[108]? = some (⟨283,(6),[9],[42],1121⟩) from rfl))
private theorem rec13714 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(7),[9],[42],1124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[111]? = some (⟨283,(7),[9],[42],1124⟩) from rfl))
private theorem rec13717 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(8),[9],[42],1125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[114]? = some (⟨283,(8),[9],[42],1125⟩) from rfl))
private theorem rec13720 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 283 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨283,(9),[9],[42],1126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[117]? = some (⟨283,(9),[9],[42],1126⟩) from rfl))
private theorem rec13723 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(0),[9],[42],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[120]? = some (⟨285,(0),[9],[42],1430⟩) from rfl))
private theorem rec13726 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(1),[9],[42],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[123]? = some (⟨285,(1),[9],[42],1430⟩) from rfl))
private theorem rec13729 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(2),[9],[42],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[126]? = some (⟨285,(2),[9],[42],1431⟩) from rfl))
private theorem rec13732 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(3),[9],[42],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[129]? = some (⟨285,(3),[9],[42],1432⟩) from rfl))
private theorem rec13735 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(4),[9],[42],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[132]? = some (⟨285,(4),[9],[42],1433⟩) from rfl))
private theorem rec13738 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(5),[9],[42],1434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[135]? = some (⟨285,(5),[9],[42],1434⟩) from rfl))
private theorem rec13741 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(6),[9],[42],1434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[138]? = some (⟨285,(6),[9],[42],1434⟩) from rfl))
private theorem rec13744 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(7),[9],[42],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[141]? = some (⟨285,(7),[9],[42],1431⟩) from rfl))
private theorem rec13747 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(8),[9],[42],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[144]? = some (⟨285,(8),[9],[42],1432⟩) from rfl))
private theorem rec13750 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(9),[9],[42],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[147]? = some (⟨285,(9),[9],[42],1433⟩) from rfl))
private theorem rec13753 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(10),[9],[42],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[150]? = some (⟨285,(10),[9],[42],1430⟩) from rfl))
private theorem rec13756 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(11),[9],[42],1430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[153]? = some (⟨285,(11),[9],[42],1430⟩) from rfl))
private theorem rec13759 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(12),[9],[42],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[156]? = some (⟨285,(12),[9],[42],1431⟩) from rfl))
private theorem rec13762 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(13),[9],[42],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[159]? = some (⟨285,(13),[9],[42],1432⟩) from rfl))
private theorem rec13765 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(14),[9],[42],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[162]? = some (⟨285,(14),[9],[42],1433⟩) from rfl))
private theorem rec13768 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(15),[9],[42],1435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[165]? = some (⟨285,(15),[9],[42],1435⟩) from rfl))
private theorem rec13771 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(16),[9],[42],1435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[168]? = some (⟨285,(16),[9],[42],1435⟩) from rfl))
private theorem rec13774 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(17),[9],[42],1431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[171]? = some (⟨285,(17),[9],[42],1431⟩) from rfl))
private theorem rec13777 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(18),[9],[42],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[174]? = some (⟨285,(18),[9],[42],1432⟩) from rfl))
private theorem rec13780 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(19),[9],[42],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[177]? = some (⟨285,(19),[9],[42],1433⟩) from rfl))
private theorem rec13783 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(20),[9],[42],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[180]? = some (⟨285,(20),[9],[42],1436⟩) from rfl))
private theorem rec13786 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(21),[9],[42],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[183]? = some (⟨285,(21),[9],[42],1436⟩) from rfl))
private theorem rec13789 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(22),[9],[42],1436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[186]? = some (⟨285,(22),[9],[42],1436⟩) from rfl))
private theorem rec13792 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(23),[9],[42],1432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[189]? = some (⟨285,(23),[9],[42],1432⟩) from rfl))
private theorem rec13795 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 285 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨285,(24),[9],[42],1433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[192]? = some (⟨285,(24),[9],[42],1433⟩) from rfl))
private theorem rec13798 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(0),[9],[42],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[195]? = some (⟨288,(0),[9],[42],1134⟩) from rfl))
private theorem rec13801 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(1),[9],[42],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[198]? = some (⟨288,(1),[9],[42],1135⟩) from rfl))
private theorem rec13804 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(2),[9],[42],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[201]? = some (⟨288,(2),[9],[42],1136⟩) from rfl))
private theorem rec13807 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(3),[9],[42],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[204]? = some (⟨288,(3),[9],[42],1136⟩) from rfl))
private theorem rec13810 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(4),[9],[42],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[207]? = some (⟨288,(4),[9],[42],1136⟩) from rfl))
private theorem rec13813 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(5),[9],[42],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[210]? = some (⟨288,(5),[9],[42],1134⟩) from rfl))
private theorem rec13816 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(6),[9],[42],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[213]? = some (⟨288,(6),[9],[42],1135⟩) from rfl))
private theorem rec13819 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(7),[9],[42],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[216]? = some (⟨288,(7),[9],[42],1137⟩) from rfl))
private theorem rec13822 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(8),[9],[42],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[219]? = some (⟨288,(8),[9],[42],1138⟩) from rfl))
private theorem rec13825 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(9),[9],[42],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[222]? = some (⟨288,(9),[9],[42],1137⟩) from rfl))
private theorem rec13828 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(10),[9],[42],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[225]? = some (⟨288,(10),[9],[42],1134⟩) from rfl))
private theorem rec13831 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(11),[9],[42],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[228]? = some (⟨288,(11),[9],[42],1135⟩) from rfl))
private theorem rec13834 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(12),[9],[42],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[231]? = some (⟨288,(12),[9],[42],1139⟩) from rfl))
private theorem rec13837 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(13),[9],[42],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[234]? = some (⟨288,(13),[9],[42],1138⟩) from rfl))
private theorem rec13840 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(14),[9],[42],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[237]? = some (⟨288,(14),[9],[42],1139⟩) from rfl))
private theorem rec13843 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(15),[9],[42],1140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[240]? = some (⟨288,(15),[9],[42],1140⟩) from rfl))
private theorem rec13846 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(16),[9],[42],1141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[243]? = some (⟨288,(16),[9],[42],1141⟩) from rfl))
private theorem rec13849 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(17),[9],[42],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[246]? = some (⟨288,(17),[9],[42],1142⟩) from rfl))
private theorem rec13852 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(18),[9],[42],1143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[249]? = some (⟨288,(18),[9],[42],1143⟩) from rfl))
private theorem rec13855 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(19),[9],[42],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[252]? = some (⟨288,(19),[9],[42],1142⟩) from rfl))
private theorem rec13858 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(20),[9],[42],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[255]? = some (⟨288,(20),[9],[42],1134⟩) from rfl))
private theorem rec13861 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(21),[9],[42],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[258]? = some (⟨288,(21),[9],[42],1135⟩) from rfl))
private theorem rec13864 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(22),[9],[42],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[261]? = some (⟨288,(22),[9],[42],1144⟩) from rfl))
private theorem rec13867 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(23),[9],[42],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[264]? = some (⟨288,(23),[9],[42],1138⟩) from rfl))
private theorem rec13870 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 288 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨288,(24),[9],[42],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[267]? = some (⟨288,(24),[9],[42],1144⟩) from rfl))
private theorem rec13873 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(0),[9],[42],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[270]? = some (⟨290,(0),[9],[42],1437⟩) from rfl))
private theorem rec13876 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(1),[9],[42],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[273]? = some (⟨290,(1),[9],[42],1437⟩) from rfl))
private theorem rec13879 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(2),[9],[42],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[276]? = some (⟨290,(2),[9],[42],1438⟩) from rfl))
private theorem rec13882 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(3),[9],[42],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[279]? = some (⟨290,(3),[9],[42],1439⟩) from rfl))
private theorem rec13885 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(4),[9],[42],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[282]? = some (⟨290,(4),[9],[42],1440⟩) from rfl))
private theorem rec13888 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(5),[9],[42],1441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[285]? = some (⟨290,(5),[9],[42],1441⟩) from rfl))
private theorem rec13891 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(6),[9],[42],1441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[288]? = some (⟨290,(6),[9],[42],1441⟩) from rfl))
private theorem rec13894 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(7),[9],[42],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[291]? = some (⟨290,(7),[9],[42],1438⟩) from rfl))
private theorem rec13897 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(8),[9],[42],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[294]? = some (⟨290,(8),[9],[42],1439⟩) from rfl))
private theorem rec13900 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(9),[9],[42],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[297]? = some (⟨290,(9),[9],[42],1440⟩) from rfl))
private theorem rec13903 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(10),[9],[42],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[300]? = some (⟨290,(10),[9],[42],1437⟩) from rfl))
private theorem rec13906 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(11),[9],[42],1437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[303]? = some (⟨290,(11),[9],[42],1437⟩) from rfl))
private theorem rec13909 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(12),[9],[42],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[306]? = some (⟨290,(12),[9],[42],1438⟩) from rfl))
private theorem rec13912 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(13),[9],[42],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[309]? = some (⟨290,(13),[9],[42],1439⟩) from rfl))
private theorem rec13915 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(14),[9],[42],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[312]? = some (⟨290,(14),[9],[42],1440⟩) from rfl))
private theorem rec13918 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(15),[9],[42],1442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[315]? = some (⟨290,(15),[9],[42],1442⟩) from rfl))
private theorem rec13921 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(16),[9],[42],1442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[318]? = some (⟨290,(16),[9],[42],1442⟩) from rfl))
private theorem rec13924 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(17),[9],[42],1438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[321]? = some (⟨290,(17),[9],[42],1438⟩) from rfl))
private theorem rec13927 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(18),[9],[42],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[324]? = some (⟨290,(18),[9],[42],1439⟩) from rfl))
private theorem rec13930 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(19),[9],[42],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[327]? = some (⟨290,(19),[9],[42],1440⟩) from rfl))
private theorem rec13933 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(20),[9],[42],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[330]? = some (⟨290,(20),[9],[42],1443⟩) from rfl))
private theorem rec13936 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(21),[9],[42],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[333]? = some (⟨290,(21),[9],[42],1443⟩) from rfl))
private theorem rec13939 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(22),[9],[42],1443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[336]? = some (⟨290,(22),[9],[42],1443⟩) from rfl))
private theorem rec13942 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(23),[9],[42],1439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[339]? = some (⟨290,(23),[9],[42],1439⟩) from rfl))
private theorem rec13945 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 290 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨290,(24),[9],[42],1440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[342]? = some (⟨290,(24),[9],[42],1440⟩) from rfl))
private theorem rec13948 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(0),[9],[42],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[345]? = some (⟨293,(0),[9],[42],1152⟩) from rfl))
private theorem rec13951 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(1),[9],[42],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[348]? = some (⟨293,(1),[9],[42],1153⟩) from rfl))
private theorem rec13954 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(2),[9],[42],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[351]? = some (⟨293,(2),[9],[42],1154⟩) from rfl))
private theorem rec13957 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(3),[9],[42],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[354]? = some (⟨293,(3),[9],[42],1154⟩) from rfl))
private theorem rec13960 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(4),[9],[42],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[357]? = some (⟨293,(4),[9],[42],1154⟩) from rfl))
private theorem rec13963 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(5),[9],[42],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[360]? = some (⟨293,(5),[9],[42],1152⟩) from rfl))
private theorem rec13966 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(6),[9],[42],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[363]? = some (⟨293,(6),[9],[42],1153⟩) from rfl))
private theorem rec13969 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(7),[9],[42],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[366]? = some (⟨293,(7),[9],[42],1155⟩) from rfl))
private theorem rec13972 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(8),[9],[42],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[369]? = some (⟨293,(8),[9],[42],1156⟩) from rfl))
private theorem rec13975 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(9),[9],[42],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[372]? = some (⟨293,(9),[9],[42],1155⟩) from rfl))
private theorem rec13978 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(10),[9],[42],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[375]? = some (⟨293,(10),[9],[42],1152⟩) from rfl))
private theorem rec13981 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(11),[9],[42],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[378]? = some (⟨293,(11),[9],[42],1153⟩) from rfl))
private theorem rec13984 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(12),[9],[42],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[381]? = some (⟨293,(12),[9],[42],1157⟩) from rfl))
private theorem rec13987 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(13),[9],[42],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[384]? = some (⟨293,(13),[9],[42],1156⟩) from rfl))
private theorem rec13990 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(14),[9],[42],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[387]? = some (⟨293,(14),[9],[42],1157⟩) from rfl))
private theorem rec13993 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(15),[9],[42],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[390]? = some (⟨293,(15),[9],[42],1152⟩) from rfl))
private theorem rec13996 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(16),[9],[42],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[393]? = some (⟨293,(16),[9],[42],1153⟩) from rfl))
private theorem rec13999 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(17),[9],[42],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[396]? = some (⟨293,(17),[9],[42],1155⟩) from rfl))
private theorem rec14002 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(18),[9],[42],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[399]? = some (⟨293,(18),[9],[42],1156⟩) from rfl))
private theorem rec14005 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(19),[9],[42],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[402]? = some (⟨293,(19),[9],[42],1155⟩) from rfl))
private theorem rec14008 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(20),[9],[42],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[405]? = some (⟨293,(20),[9],[42],1152⟩) from rfl))
private theorem rec14011 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(21),[9],[42],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[408]? = some (⟨293,(21),[9],[42],1153⟩) from rfl))
private theorem rec14014 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(22),[9],[42],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[411]? = some (⟨293,(22),[9],[42],1158⟩) from rfl))
private theorem rec14017 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(23),[9],[42],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[414]? = some (⟨293,(23),[9],[42],1156⟩) from rfl))
private theorem rec14020 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 293 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨293,(24),[9],[42],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[417]? = some (⟨293,(24),[9],[42],1158⟩) from rfl))
private theorem rec14023 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(0),[9],[42],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[420]? = some (⟨295,(0),[9],[42],1444⟩) from rfl))
private theorem rec14026 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(1),[9],[42],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[423]? = some (⟨295,(1),[9],[42],1444⟩) from rfl))
private theorem rec14029 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(2),[9],[42],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[426]? = some (⟨295,(2),[9],[42],1445⟩) from rfl))
private theorem rec14032 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(3),[9],[42],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[429]? = some (⟨295,(3),[9],[42],1446⟩) from rfl))
private theorem rec14035 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(4),[9],[42],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[432]? = some (⟨295,(4),[9],[42],1447⟩) from rfl))
private theorem rec14038 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(5),[9],[42],1448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[435]? = some (⟨295,(5),[9],[42],1448⟩) from rfl))
private theorem rec14041 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(6),[9],[42],1448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[438]? = some (⟨295,(6),[9],[42],1448⟩) from rfl))
private theorem rec14044 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(7),[9],[42],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[441]? = some (⟨295,(7),[9],[42],1445⟩) from rfl))
private theorem rec14047 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(8),[9],[42],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[444]? = some (⟨295,(8),[9],[42],1446⟩) from rfl))
private theorem rec14050 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(9),[9],[42],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[447]? = some (⟨295,(9),[9],[42],1447⟩) from rfl))
private theorem rec14053 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(10),[9],[42],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[450]? = some (⟨295,(10),[9],[42],1444⟩) from rfl))
private theorem rec14056 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(11),[9],[42],1444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[453]? = some (⟨295,(11),[9],[42],1444⟩) from rfl))
private theorem rec14059 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(12),[9],[42],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[456]? = some (⟨295,(12),[9],[42],1445⟩) from rfl))
private theorem rec14062 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(13),[9],[42],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[459]? = some (⟨295,(13),[9],[42],1446⟩) from rfl))
private theorem rec14065 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(14),[9],[42],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[462]? = some (⟨295,(14),[9],[42],1447⟩) from rfl))
private theorem rec14068 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(15),[9],[42],1449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[465]? = some (⟨295,(15),[9],[42],1449⟩) from rfl))
private theorem rec14071 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(16),[9],[42],1449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[468]? = some (⟨295,(16),[9],[42],1449⟩) from rfl))
private theorem rec14074 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(17),[9],[42],1445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[471]? = some (⟨295,(17),[9],[42],1445⟩) from rfl))
private theorem rec14077 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(18),[9],[42],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[474]? = some (⟨295,(18),[9],[42],1446⟩) from rfl))
private theorem rec14080 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(19),[9],[42],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[477]? = some (⟨295,(19),[9],[42],1447⟩) from rfl))
private theorem rec14083 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(20),[9],[42],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[480]? = some (⟨295,(20),[9],[42],1450⟩) from rfl))
private theorem rec14086 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(21),[9],[42],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[483]? = some (⟨295,(21),[9],[42],1450⟩) from rfl))
private theorem rec14089 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(22),[9],[42],1450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[486]? = some (⟨295,(22),[9],[42],1450⟩) from rfl))
private theorem rec14092 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(23),[9],[42],1446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[489]? = some (⟨295,(23),[9],[42],1446⟩) from rfl))
private theorem rec14095 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 295 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨295,(24),[9],[42],1447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[492]? = some (⟨295,(24),[9],[42],1447⟩) from rfl))
private theorem rec14098 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(0),[9],[42],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[495]? = some (⟨297,(0),[9],[42],1451⟩) from rfl))
private theorem rec14101 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(1),[9],[42],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[498]? = some (⟨297,(1),[9],[42],1452⟩) from rfl))
private theorem rec14104 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(2),[9],[42],1453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[501]? = some (⟨297,(2),[9],[42],1453⟩) from rfl))
private theorem rec14107 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(3),[9],[42],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[504]? = some (⟨297,(3),[9],[42],1454⟩) from rfl))
private theorem rec14110 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(4),[9],[42],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[507]? = some (⟨297,(4),[9],[42],1451⟩) from rfl))
private theorem rec14113 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(5),[9],[42],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[510]? = some (⟨297,(5),[9],[42],1452⟩) from rfl))
private theorem rec14116 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(6),[9],[42],1455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[513]? = some (⟨297,(6),[9],[42],1455⟩) from rfl))
private theorem rec14119 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(7),[9],[42],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[516]? = some (⟨297,(7),[9],[42],1454⟩) from rfl))
private theorem rec14122 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(8),[9],[42],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[519]? = some (⟨297,(8),[9],[42],1451⟩) from rfl))
private theorem rec14125 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(9),[9],[42],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[522]? = some (⟨297,(9),[9],[42],1452⟩) from rfl))
private theorem rec14128 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(10),[9],[42],1453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[525]? = some (⟨297,(10),[9],[42],1453⟩) from rfl))
private theorem rec14131 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(11),[9],[42],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[528]? = some (⟨297,(11),[9],[42],1454⟩) from rfl))
private theorem rec14134 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(12),[9],[42],1451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[531]? = some (⟨297,(12),[9],[42],1451⟩) from rfl))
private theorem rec14137 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(13),[9],[42],1452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[534]? = some (⟨297,(13),[9],[42],1452⟩) from rfl))
private theorem rec14140 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(14),[9],[42],1456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[537]? = some (⟨297,(14),[9],[42],1456⟩) from rfl))
private theorem rec14143 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 297 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨297,(15),[9],[42],1454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[540]? = some (⟨297,(15),[9],[42],1454⟩) from rfl))
private theorem rec14146 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(0),[9],[42],1457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[543]? = some (⟨300,(0),[9],[42],1457⟩) from rfl))
private theorem rec14149 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(1),[9],[42],1458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[546]? = some (⟨300,(1),[9],[42],1458⟩) from rfl))
private theorem rec14152 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(2),[9],[42],1457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[549]? = some (⟨300,(2),[9],[42],1457⟩) from rfl))
private theorem rec14155 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(3),[9],[42],1459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[552]? = some (⟨300,(3),[9],[42],1459⟩) from rfl))
private theorem rec14158 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(4),[9],[42],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[555]? = some (⟨300,(4),[9],[42],1460⟩) from rfl))
private theorem rec14161 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(5),[9],[42],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[558]? = some (⟨300,(5),[9],[42],1460⟩) from rfl))
private theorem rec14164 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(6),[9],[42],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[561]? = some (⟨300,(6),[9],[42],1460⟩) from rfl))
private theorem rec14167 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(7),[9],[42],1460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[564]? = some (⟨300,(7),[9],[42],1460⟩) from rfl))
private theorem rec14170 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(8),[9],[42],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[567]? = some (⟨300,(8),[9],[42],1461⟩) from rfl))
private theorem rec14173 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(9),[9],[42],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[570]? = some (⟨300,(9),[9],[42],1461⟩) from rfl))
private theorem rec14176 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(10),[9],[42],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[573]? = some (⟨300,(10),[9],[42],1461⟩) from rfl))
private theorem rec14179 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(11),[9],[42],1461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[576]? = some (⟨300,(11),[9],[42],1461⟩) from rfl))
private theorem rec14182 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(12),[9],[42],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[579]? = some (⟨300,(12),[9],[42],1462⟩) from rfl))
private theorem rec14185 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(13),[9],[42],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[582]? = some (⟨300,(13),[9],[42],1462⟩) from rfl))
private theorem rec14188 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(14),[9],[42],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[585]? = some (⟨300,(14),[9],[42],1462⟩) from rfl))
private theorem rec14191 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 300 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨300,(15),[9],[42],1462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[588]? = some (⟨300,(15),[9],[42],1462⟩) from rfl))
private theorem rec14194 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(0),[9],[42],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[591]? = some (⟨302,(0),[9],[42],1463⟩) from rfl))
private theorem rec14197 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(1),[9],[42],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[594]? = some (⟨302,(1),[9],[42],1464⟩) from rfl))
private theorem rec14200 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(2),[9],[42],1465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[597]? = some (⟨302,(2),[9],[42],1465⟩) from rfl))
private theorem rec14203 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(3),[9],[42],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[600]? = some (⟨302,(3),[9],[42],1466⟩) from rfl))
private theorem rec14206 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(4),[9],[42],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[603]? = some (⟨302,(4),[9],[42],1463⟩) from rfl))
private theorem rec14209 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(5),[9],[42],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[606]? = some (⟨302,(5),[9],[42],1464⟩) from rfl))
private theorem rec14212 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(6),[9],[42],1467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[609]? = some (⟨302,(6),[9],[42],1467⟩) from rfl))
private theorem rec14215 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(7),[9],[42],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[612]? = some (⟨302,(7),[9],[42],1466⟩) from rfl))
private theorem rec14218 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(8),[9],[42],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[615]? = some (⟨302,(8),[9],[42],1463⟩) from rfl))
private theorem rec14221 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(9),[9],[42],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[618]? = some (⟨302,(9),[9],[42],1464⟩) from rfl))
private theorem rec14224 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(10),[9],[42],1465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[621]? = some (⟨302,(10),[9],[42],1465⟩) from rfl))
private theorem rec14227 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(11),[9],[42],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[624]? = some (⟨302,(11),[9],[42],1466⟩) from rfl))
private theorem rec14230 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(12),[9],[42],1463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[627]? = some (⟨302,(12),[9],[42],1463⟩) from rfl))
private theorem rec14233 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(13),[9],[42],1464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[630]? = some (⟨302,(13),[9],[42],1464⟩) from rfl))
private theorem rec14236 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(14),[9],[42],1468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[633]? = some (⟨302,(14),[9],[42],1468⟩) from rfl))
private theorem rec14239 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 302 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨302,(15),[9],[42],1466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[636]? = some (⟨302,(15),[9],[42],1466⟩) from rfl))
private theorem rec14242 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 305 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(0),[9],[42],1469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[639]? = some (⟨305,(0),[9],[42],1469⟩) from rfl))
private theorem rec14245 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 305 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(1),[9],[42],1470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[642]? = some (⟨305,(1),[9],[42],1470⟩) from rfl))
private theorem rec14248 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 305 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(2),[9],[42],1471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[645]? = some (⟨305,(2),[9],[42],1471⟩) from rfl))
private theorem rec14251 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 305 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨305,(3),[9],[42],1472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[648]? = some (⟨305,(3),[9],[42],1472⟩) from rfl))
private theorem rec14254 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(0),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[651]? = some (⟨307,(0),[9],[42],3⟩) from rfl))
private theorem rec14257 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(1),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[654]? = some (⟨307,(1),[9],[42],3⟩) from rfl))
private theorem rec14260 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(2),[9],[42],1473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[657]? = some (⟨307,(2),[9],[42],1473⟩) from rfl))
private theorem rec14263 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(3),[9],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[660]? = some (⟨307,(3),[9],[42],29⟩) from rfl))
private theorem rec14266 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(4),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[663]? = some (⟨307,(4),[9],[42],3⟩) from rfl))
private theorem rec14269 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(5),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[666]? = some (⟨307,(5),[9],[42],3⟩) from rfl))
private theorem rec14272 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(6),[9],[42],511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[669]? = some (⟨307,(6),[9],[42],511⟩) from rfl))
private theorem rec14275 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(7),[9],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[672]? = some (⟨307,(7),[9],[42],29⟩) from rfl))
private theorem rec14278 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(8),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[675]? = some (⟨307,(8),[9],[42],3⟩) from rfl))
private theorem rec14281 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(9),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[678]? = some (⟨307,(9),[9],[42],3⟩) from rfl))
private theorem rec14284 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(10),[9],[42],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[681]? = some (⟨307,(10),[9],[42],512⟩) from rfl))
private theorem rec14287 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(11),[9],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[684]? = some (⟨307,(11),[9],[42],29⟩) from rfl))
private theorem rec14290 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(12),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[687]? = some (⟨307,(12),[9],[42],3⟩) from rfl))
private theorem rec14293 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(13),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[690]? = some (⟨307,(13),[9],[42],3⟩) from rfl))
private theorem rec14296 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(14),[9],[42],513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[693]? = some (⟨307,(14),[9],[42],513⟩) from rfl))
private theorem rec14299 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(15),[9],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[696]? = some (⟨307,(15),[9],[42],29⟩) from rfl))
private theorem rec14302 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(16),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[699]? = some (⟨307,(16),[9],[42],3⟩) from rfl))
private theorem rec14305 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(17),[9],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[702]? = some (⟨307,(17),[9],[42],3⟩) from rfl))
private theorem rec14308 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(18),[9],[42],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[705]? = some (⟨307,(18),[9],[42],514⟩) from rfl))
private theorem rec14311 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 307 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨307,(19),[9],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[708]? = some (⟨307,(19),[9],[42],29⟩) from rfl))
private theorem rec14314 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 308 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(8),[9],[42],1474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[711]? = some (⟨308,(8),[9],[42],1474⟩) from rfl))
private theorem rec14317 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 308 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(9),[9],[42],1475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[714]? = some (⟨308,(9),[9],[42],1475⟩) from rfl))
private theorem rec14320 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 308 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(10),[9],[42],1474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[717]? = some (⟨308,(10),[9],[42],1474⟩) from rfl))
private theorem rec14323 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 308 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨308,(11),[9],[42],1476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[720]? = some (⟨308,(11),[9],[42],1476⟩) from rfl))
private theorem rec14326 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 309 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(0),[9],[42],1188⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[723]? = some (⟨309,(0),[9],[42],1188⟩) from rfl))
private theorem rec14329 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 309 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(1),[9],[42],1189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[726]? = some (⟨309,(1),[9],[42],1189⟩) from rfl))
private theorem rec14332 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 309 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(2),[9],[42],1190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[729]? = some (⟨309,(2),[9],[42],1190⟩) from rfl))
private theorem rec14335 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 309 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(3),[9],[42],1191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[732]? = some (⟨309,(3),[9],[42],1191⟩) from rfl))
private theorem rec14338 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 309 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨309,(4),[9],[42],1477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[735]? = some (⟨309,(4),[9],[42],1477⟩) from rfl))
private theorem rec14341 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 311 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(0),[9],[42],1478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[738]? = some (⟨311,(0),[9],[42],1478⟩) from rfl))
private theorem rec14344 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 311 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(1),[9],[42],1479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[741]? = some (⟨311,(1),[9],[42],1479⟩) from rfl))
private theorem rec14347 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 311 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(2),[9],[42],1480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[744]? = some (⟨311,(2),[9],[42],1480⟩) from rfl))
private theorem rec14350 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 311 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨311,(3),[9],[42],1481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[747]? = some (⟨311,(3),[9],[42],1481⟩) from rfl))
private theorem rec14353 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 312 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(0),[9],[42],1482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[750]? = some (⟨312,(0),[9],[42],1482⟩) from rfl))
private theorem rec14356 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 312 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(1),[9],[42],1483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[753]? = some (⟨312,(1),[9],[42],1483⟩) from rfl))
private theorem rec14359 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 312 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(2),[9],[42],1482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[756]? = some (⟨312,(2),[9],[42],1482⟩) from rfl))
private theorem rec14362 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 312 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨312,(3),[9],[42],1484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[759]? = some (⟨312,(3),[9],[42],1484⟩) from rfl))
private theorem rec14365 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 313 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(0),[9],[42],1200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[762]? = some (⟨313,(0),[9],[42],1200⟩) from rfl))
private theorem rec14368 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 313 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(1),[9],[42],1201⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[765]? = some (⟨313,(1),[9],[42],1201⟩) from rfl))
private theorem rec14371 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 313 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(2),[9],[42],1202⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[768]? = some (⟨313,(2),[9],[42],1202⟩) from rfl))
private theorem rec14374 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 313 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨313,(3),[9],[42],1203⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[771]? = some (⟨313,(3),[9],[42],1203⟩) from rfl))
private theorem rec14378 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(0),[9],[42],1485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[775]? = some (⟨315,(0),[9],[42],1485⟩) from rfl))
private theorem rec14381 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(1),[9],[42],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[778]? = some (⟨315,(1),[9],[42],1486⟩) from rfl))
private theorem rec14384 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(2),[9],[42],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[781]? = some (⟨315,(2),[9],[42],1487⟩) from rfl))
private theorem rec14387 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(3),[9],[42],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[784]? = some (⟨315,(3),[9],[42],1488⟩) from rfl))
private theorem rec14390 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(4),[9],[42],1489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[787]? = some (⟨315,(4),[9],[42],1489⟩) from rfl))
private theorem rec14393 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(5),[9],[42],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[790]? = some (⟨315,(5),[9],[42],1486⟩) from rfl))
private theorem rec14396 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(6),[9],[42],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[793]? = some (⟨315,(6),[9],[42],1487⟩) from rfl))
private theorem rec14399 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(7),[9],[42],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[796]? = some (⟨315,(7),[9],[42],1488⟩) from rfl))
private theorem rec14402 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(8),[9],[42],1485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[799]? = some (⟨315,(8),[9],[42],1485⟩) from rfl))
private theorem rec14405 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(9),[9],[42],1490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[802]? = some (⟨315,(9),[9],[42],1490⟩) from rfl))
private theorem rec14408 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(10),[9],[42],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[805]? = some (⟨315,(10),[9],[42],1487⟩) from rfl))
private theorem rec14411 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(11),[9],[42],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[808]? = some (⟨315,(11),[9],[42],1488⟩) from rfl))
private theorem rec14414 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(12),[9],[42],1491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[811]? = some (⟨315,(12),[9],[42],1491⟩) from rfl))
private theorem rec14417 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(13),[9],[42],1486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[814]? = some (⟨315,(13),[9],[42],1486⟩) from rfl))
private theorem rec14420 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(14),[9],[42],1487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[817]? = some (⟨315,(14),[9],[42],1487⟩) from rfl))
private theorem rec14423 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 315 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨315,(15),[9],[42],1488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[820]? = some (⟨315,(15),[9],[42],1488⟩) from rfl))
private theorem rec14426 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(0),[9],[42],1211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[823]? = some (⟨317,(0),[9],[42],1211⟩) from rfl))
private theorem rec14429 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(1),[9],[42],1212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[826]? = some (⟨317,(1),[9],[42],1212⟩) from rfl))
private theorem rec14432 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(2),[9],[42],1213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[829]? = some (⟨317,(2),[9],[42],1213⟩) from rfl))
private theorem rec14435 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(3),[9],[42],1214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[832]? = some (⟨317,(3),[9],[42],1214⟩) from rfl))
private theorem rec14438 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(4),[9],[42],1215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[835]? = some (⟨317,(4),[9],[42],1215⟩) from rfl))
private theorem rec14441 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(5),[9],[42],1216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[838]? = some (⟨317,(5),[9],[42],1216⟩) from rfl))
private theorem rec14444 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(6),[9],[42],1217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[841]? = some (⟨317,(6),[9],[42],1217⟩) from rfl))
private theorem rec14447 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(7),[9],[42],1218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[844]? = some (⟨317,(7),[9],[42],1218⟩) from rfl))
private theorem rec14450 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(8),[9],[42],1492⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[847]? = some (⟨317,(8),[9],[42],1492⟩) from rfl))
private theorem rec14453 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(9),[9],[42],1493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[850]? = some (⟨317,(9),[9],[42],1493⟩) from rfl))
private theorem rec14456 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(10),[9],[42],1494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[853]? = some (⟨317,(10),[9],[42],1494⟩) from rfl))
private theorem rec14459 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(11),[9],[42],1495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[856]? = some (⟨317,(11),[9],[42],1495⟩) from rfl))
private theorem rec14462 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(12),[9],[42],1496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[859]? = some (⟨317,(12),[9],[42],1496⟩) from rfl))
private theorem rec14465 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(13),[9],[42],1493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[862]? = some (⟨317,(13),[9],[42],1493⟩) from rfl))
private theorem rec14468 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(14),[9],[42],1494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[865]? = some (⟨317,(14),[9],[42],1494⟩) from rfl))
private theorem rec14471 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 317 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨317,(15),[9],[42],1495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[868]? = some (⟨317,(15),[9],[42],1495⟩) from rfl))
private theorem rec14474 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(0),[9],[42],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[871]? = some (⟨318,(0),[9],[42],882⟩) from rfl))
private theorem rec14477 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(1),[9],[42],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[874]? = some (⟨318,(1),[9],[42],1497⟩) from rfl))
private theorem rec14480 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(2),[9],[42],1498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[877]? = some (⟨318,(2),[9],[42],1498⟩) from rfl))
private theorem rec14483 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(3),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[880]? = some (⟨318,(3),[9],[42],101⟩) from rfl))
private theorem rec14486 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(4),[9],[42],1498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[883]? = some (⟨318,(4),[9],[42],1498⟩) from rfl))
private theorem rec14489 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(5),[9],[42],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[886]? = some (⟨318,(5),[9],[42],882⟩) from rfl))
private theorem rec14492 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(6),[9],[42],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[889]? = some (⟨318,(6),[9],[42],1497⟩) from rfl))
private theorem rec14495 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(7),[9],[42],1499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[892]? = some (⟨318,(7),[9],[42],1499⟩) from rfl))
private theorem rec14498 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(8),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[895]? = some (⟨318,(8),[9],[42],101⟩) from rfl))
private theorem rec14501 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(9),[9],[42],1499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[898]? = some (⟨318,(9),[9],[42],1499⟩) from rfl))
private theorem rec14504 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(10),[9],[42],1500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[901]? = some (⟨318,(10),[9],[42],1500⟩) from rfl))
private theorem rec14507 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(11),[9],[42],1501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[904]? = some (⟨318,(11),[9],[42],1501⟩) from rfl))
private theorem rec14510 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(12),[9],[42],1502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[907]? = some (⟨318,(12),[9],[42],1502⟩) from rfl))
private theorem rec14513 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(13),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[910]? = some (⟨318,(13),[9],[42],101⟩) from rfl))
private theorem rec14516 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(14),[9],[42],1502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[913]? = some (⟨318,(14),[9],[42],1502⟩) from rfl))
private theorem rec14519 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(15),[9],[42],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[916]? = some (⟨318,(15),[9],[42],882⟩) from rfl))
private theorem rec14522 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(16),[9],[42],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[919]? = some (⟨318,(16),[9],[42],1497⟩) from rfl))
private theorem rec14525 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(17),[9],[42],1503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[922]? = some (⟨318,(17),[9],[42],1503⟩) from rfl))
private theorem rec14528 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(18),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[925]? = some (⟨318,(18),[9],[42],101⟩) from rfl))
private theorem rec14531 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 318 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨318,(19),[9],[42],1503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[928]? = some (⟨318,(19),[9],[42],1503⟩) from rfl))
private theorem rec14534 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(0),[9],[42],1231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[931]? = some (⟨319,(0),[9],[42],1231⟩) from rfl))
private theorem rec14537 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(1),[9],[42],1229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[934]? = some (⟨319,(1),[9],[42],1229⟩) from rfl))
private theorem rec14540 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(2),[9],[42],1228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[937]? = some (⟨319,(2),[9],[42],1228⟩) from rfl))
private theorem rec14543 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(3),[9],[42],1230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[940]? = some (⟨319,(3),[9],[42],1230⟩) from rfl))
private theorem rec14546 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(4),[9],[42],1231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[943]? = some (⟨319,(4),[9],[42],1231⟩) from rfl))
private theorem rec14549 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(5),[9],[42],1232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[946]? = some (⟨319,(5),[9],[42],1232⟩) from rfl))
private theorem rec14552 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(6),[9],[42],1504⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[949]? = some (⟨319,(6),[9],[42],1504⟩) from rfl))
private theorem rec14555 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(7),[9],[42],1505⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[952]? = some (⟨319,(7),[9],[42],1505⟩) from rfl))
private theorem rec14558 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(8),[9],[42],1235⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[955]? = some (⟨319,(8),[9],[42],1235⟩) from rfl))
private theorem rec14561 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(9),[9],[42],1236⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[958]? = some (⟨319,(9),[9],[42],1236⟩) from rfl))
private theorem rec14564 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(10),[9],[42],1506⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[961]? = some (⟨319,(10),[9],[42],1506⟩) from rfl))
private theorem rec14567 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(11),[9],[42],1507⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[964]? = some (⟨319,(11),[9],[42],1507⟩) from rfl))
private theorem rec14570 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(12),[9],[42],1239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[967]? = some (⟨319,(12),[9],[42],1239⟩) from rfl))
private theorem rec14573 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(13),[9],[42],1240⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[970]? = some (⟨319,(13),[9],[42],1240⟩) from rfl))
private theorem rec14576 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(14),[9],[42],1508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[973]? = some (⟨319,(14),[9],[42],1508⟩) from rfl))
private theorem rec14579 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(15),[9],[42],1508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[976]? = some (⟨319,(15),[9],[42],1508⟩) from rfl))
private theorem rec14582 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(16),[9],[42],1242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[979]? = some (⟨319,(16),[9],[42],1242⟩) from rfl))
private theorem rec14585 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(17),[9],[42],1243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[982]? = some (⟨319,(17),[9],[42],1243⟩) from rfl))
private theorem rec14588 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(18),[9],[42],1509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[985]? = some (⟨319,(18),[9],[42],1509⟩) from rfl))
private theorem rec14591 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 319 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨319,(19),[9],[42],1509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[988]? = some (⟨319,(19),[9],[42],1509⟩) from rfl))
private theorem rec14594 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(0),[9],[42],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[991]? = some (⟨321,(0),[9],[42],882⟩) from rfl))
private theorem rec14597 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(1),[9],[42],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[994]? = some (⟨321,(1),[9],[42],1497⟩) from rfl))
private theorem rec14600 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(2),[9],[42],1245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[997]? = some (⟨321,(2),[9],[42],1245⟩) from rfl))
private theorem rec14603 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(3),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1000]? = some (⟨321,(3),[9],[42],101⟩) from rfl))
private theorem rec14606 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(4),[9],[42],1245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1003]? = some (⟨321,(4),[9],[42],1245⟩) from rfl))
private theorem rec14609 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(5),[9],[42],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1006]? = some (⟨321,(5),[9],[42],882⟩) from rfl))
private theorem rec14612 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(6),[9],[42],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1009]? = some (⟨321,(6),[9],[42],1497⟩) from rfl))
private theorem rec14615 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(7),[9],[42],1510⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1012]? = some (⟨321,(7),[9],[42],1510⟩) from rfl))
private theorem rec14618 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(8),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1015]? = some (⟨321,(8),[9],[42],101⟩) from rfl))
private theorem rec14621 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(9),[9],[42],1510⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1018]? = some (⟨321,(9),[9],[42],1510⟩) from rfl))
private theorem rec14624 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(10),[9],[42],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1021]? = some (⟨321,(10),[9],[42],882⟩) from rfl))
private theorem rec14627 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(11),[9],[42],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1024]? = some (⟨321,(11),[9],[42],1497⟩) from rfl))
private theorem rec14630 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(12),[9],[42],1511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1027]? = some (⟨321,(12),[9],[42],1511⟩) from rfl))
private theorem rec14633 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(13),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1030]? = some (⟨321,(13),[9],[42],101⟩) from rfl))
private theorem rec14636 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(14),[9],[42],1511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1033]? = some (⟨321,(14),[9],[42],1511⟩) from rfl))
private theorem rec14639 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(15),[9],[42],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1036]? = some (⟨321,(15),[9],[42],625⟩) from rfl))
private theorem rec14642 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(16),[9],[42],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1039]? = some (⟨321,(16),[9],[42],626⟩) from rfl))
private theorem rec14645 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(17),[9],[42],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1042]? = some (⟨321,(17),[9],[42],286⟩) from rfl))
private theorem rec14648 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(18),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1045]? = some (⟨321,(18),[9],[42],101⟩) from rfl))
private theorem rec14651 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(19),[9],[42],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1048]? = some (⟨321,(19),[9],[42],286⟩) from rfl))
private theorem rec14654 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(20),[9],[42],882⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1051]? = some (⟨321,(20),[9],[42],882⟩) from rfl))
private theorem rec14657 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(21),[9],[42],1497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1054]? = some (⟨321,(21),[9],[42],1497⟩) from rfl))
private theorem rec14660 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(22),[9],[42],1512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1057]? = some (⟨321,(22),[9],[42],1512⟩) from rfl))
private theorem rec14663 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(23),[9],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1060]? = some (⟨321,(23),[9],[42],101⟩) from rfl))
private theorem rec14666 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 321 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨321,(24),[9],[42],1512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1063]? = some (⟨321,(24),[9],[42],1512⟩) from rfl))
private theorem rec16512 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(0),[9],[42],1675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[304]? = some (⟨582,(0),[9],[42],1675⟩) from rfl))
private theorem rec16514 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(1),[9],[42],1676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[306]? = some (⟨582,(1),[9],[42],1676⟩) from rfl))
private theorem rec16516 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(2),[9],[42],1675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[308]? = some (⟨582,(2),[9],[42],1675⟩) from rfl))
private theorem rec16518 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(3),[9],[42],1677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[310]? = some (⟨582,(3),[9],[42],1677⟩) from rfl))
private theorem rec16520 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(4),[9],[42],1410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[312]? = some (⟨582,(4),[9],[42],1410⟩) from rfl))
private theorem rec16522 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(5),[9],[42],1675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[314]? = some (⟨582,(5),[9],[42],1675⟩) from rfl))
private theorem rec16524 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(6),[9],[42],1676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[316]? = some (⟨582,(6),[9],[42],1676⟩) from rfl))
private theorem rec16526 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(7),[9],[42],1675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[318]? = some (⟨582,(7),[9],[42],1675⟩) from rfl))
private theorem rec16528 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(8),[9],[42],1677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[320]? = some (⟨582,(8),[9],[42],1677⟩) from rfl))
private theorem rec16530 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 582 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨582,(9),[9],[42],1410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[322]? = some (⟨582,(9),[9],[42],1410⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 9).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 32).take 16, section14Recorded section14Catalog 9 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 9 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 9).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(581,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(582,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(583,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(584,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(585,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 32).take 16 = [⟨4,32,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨4,33,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,34,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,35,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,36,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨4,37,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,38,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,39,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨4,40,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨4,41,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨4,42,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨4,43,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨4,44,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨4,45,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨4,46,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨4,47,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec13316 9 32 (by decide) (by decide)
  · left
    exact rec13316 9 33 (by decide) (by decide)
  · left
    exact rec13320 9 34 (by decide) (by decide)
  · left
    exact rec13321 9 35 (by decide) (by decide)
  · left
    exact rec13316 9 36 (by decide) (by decide)
  · left
    exact rec13316 9 37 (by decide) (by decide)
  · left
    exact rec13322 9 38 (by decide) (by decide)
  · left
    exact rec13321 9 39 (by decide) (by decide)
  · left
    exact rec13316 9 40 (by decide) (by decide)
  · left
    exact rec13316 9 41 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(581,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(582,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(583,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(584,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(585,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 581)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 262)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13331 9 42 (by decide) (by decide)
      · right
        exact rec13333 9 42 (by decide) (by decide)
      · right
        exact rec13335 9 42 (by decide) (by decide)
      · right
        exact rec13337 9 42 (by decide) (by decide)
      · right
        exact rec13339 9 42 (by decide) (by decide)
      · right
        exact rec13341 9 42 (by decide) (by decide)
      · right
        exact rec13343 9 42 (by decide) (by decide)
      · right
        exact rec13345 9 42 (by decide) (by decide)
      · right
        exact rec13347 9 42 (by decide) (by decide)
      · right
        exact rec13349 9 42 (by decide) (by decide)
      · right
        exact rec13351 9 42 (by decide) (by decide)
      · right
        exact rec13353 9 42 (by decide) (by decide)
      · right
        exact rec13355 9 42 (by decide) (by decide)
      · right
        exact rec13357 9 42 (by decide) (by decide)
      · right
        exact rec13359 9 42 (by decide) (by decide)
      · right
        exact rec13361 9 42 (by decide) (by decide)
      · right
        exact rec13363 9 42 (by decide) (by decide)
      · right
        exact rec13365 9 42 (by decide) (by decide)
      · right
        exact rec13367 9 42 (by decide) (by decide)
      · right
        exact rec13369 9 42 (by decide) (by decide)
      · right
        exact rec13371 9 42 (by decide) (by decide)
      · right
        exact rec13373 9 42 (by decide) (by decide)
      · right
        exact rec13375 9 42 (by decide) (by decide)
      · right
        exact rec13377 9 42 (by decide) (by decide)
      · right
        exact rec13379 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 263)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 582)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16512 9 42 (by decide) (by decide)
      · right
        exact rec16514 9 42 (by decide) (by decide)
      · right
        exact rec16516 9 42 (by decide) (by decide)
      · right
        exact rec16518 9 42 (by decide) (by decide)
      · right
        exact rec16520 9 42 (by decide) (by decide)
      · right
        exact rec16522 9 42 (by decide) (by decide)
      · right
        exact rec16524 9 42 (by decide) (by decide)
      · right
        exact rec16526 9 42 (by decide) (by decide)
      · right
        exact rec16528 9 42 (by decide) (by decide)
      · right
        exact rec16530 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 583)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 266)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 267)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13432 9 42 (by decide) (by decide)
      · right
        exact rec13435 9 42 (by decide) (by decide)
      · right
        exact rec13438 9 42 (by decide) (by decide)
      · right
        exact rec13441 9 42 (by decide) (by decide)
      · right
        exact rec13444 9 42 (by decide) (by decide)
      · right
        exact rec13447 9 42 (by decide) (by decide)
      · right
        exact rec13450 9 42 (by decide) (by decide)
      · right
        exact rec13453 9 42 (by decide) (by decide)
      · right
        exact rec13456 9 42 (by decide) (by decide)
      · right
        exact rec13459 9 42 (by decide) (by decide)
      · right
        exact rec13462 9 42 (by decide) (by decide)
      · right
        exact rec13465 9 42 (by decide) (by decide)
      · right
        exact rec13468 9 42 (by decide) (by decide)
      · right
        exact rec13471 9 42 (by decide) (by decide)
      · right
        exact rec13474 9 42 (by decide) (by decide)
      · right
        exact rec13477 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 268)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 269)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 270)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13480 9 42 (by decide) (by decide)
      · right
        exact rec13483 9 42 (by decide) (by decide)
      · right
        exact rec13486 9 42 (by decide) (by decide)
      · right
        exact rec13489 9 42 (by decide) (by decide)
      · right
        exact rec13492 9 42 (by decide) (by decide)
      · right
        exact rec13495 9 42 (by decide) (by decide)
      · right
        exact rec13498 9 42 (by decide) (by decide)
      · right
        exact rec13501 9 42 (by decide) (by decide)
      · right
        exact rec13504 9 42 (by decide) (by decide)
      · right
        exact rec13507 9 42 (by decide) (by decide)
      · right
        exact rec13510 9 42 (by decide) (by decide)
      · right
        exact rec13513 9 42 (by decide) (by decide)
      · right
        exact rec13516 9 42 (by decide) (by decide)
      · right
        exact rec13519 9 42 (by decide) (by decide)
      · right
        exact rec13522 9 42 (by decide) (by decide)
      · right
        exact rec13525 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 271)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 272)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 273)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13528 9 42 (by decide) (by decide)
      · right
        exact rec13531 9 42 (by decide) (by decide)
      · right
        exact rec13534 9 42 (by decide) (by decide)
      · right
        exact rec13537 9 42 (by decide) (by decide)
      · right
        exact rec13540 9 42 (by decide) (by decide)
      · right
        exact rec13543 9 42 (by decide) (by decide)
      · right
        exact rec13546 9 42 (by decide) (by decide)
      · right
        exact rec13549 9 42 (by decide) (by decide)
      · right
        exact rec13552 9 42 (by decide) (by decide)
      · right
        exact rec13555 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 274)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 275)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13558 9 42 (by decide) (by decide)
      · right
        exact rec13561 9 42 (by decide) (by decide)
      · right
        exact rec13564 9 42 (by decide) (by decide)
      · right
        exact rec13567 9 42 (by decide) (by decide)
      · right
        exact rec13570 9 42 (by decide) (by decide)
      · right
        exact rec13573 9 42 (by decide) (by decide)
      · right
        exact rec13576 9 42 (by decide) (by decide)
      · right
        exact rec13579 9 42 (by decide) (by decide)
      · right
        exact rec13582 9 42 (by decide) (by decide)
      · right
        exact rec13585 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 276)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 277)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 278)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13588 9 42 (by decide) (by decide)
      · right
        exact rec13591 9 42 (by decide) (by decide)
      · right
        exact rec13594 9 42 (by decide) (by decide)
      · right
        exact rec13597 9 42 (by decide) (by decide)
      · right
        exact rec13600 9 42 (by decide) (by decide)
      · right
        exact rec13603 9 42 (by decide) (by decide)
      · right
        exact rec13606 9 42 (by decide) (by decide)
      · right
        exact rec13609 9 42 (by decide) (by decide)
      · right
        exact rec13612 9 42 (by decide) (by decide)
      · right
        exact rec13615 9 42 (by decide) (by decide)
      · right
        exact rec13618 9 42 (by decide) (by decide)
      · right
        exact rec13621 9 42 (by decide) (by decide)
      · right
        exact rec13624 9 42 (by decide) (by decide)
      · right
        exact rec13627 9 42 (by decide) (by decide)
      · right
        exact rec13630 9 42 (by decide) (by decide)
      · right
        exact rec13633 9 42 (by decide) (by decide)
      · right
        exact rec13636 9 42 (by decide) (by decide)
      · right
        exact rec13639 9 42 (by decide) (by decide)
      · right
        exact rec13642 9 42 (by decide) (by decide)
      · right
        exact rec13645 9 42 (by decide) (by decide)
      · right
        exact rec13648 9 42 (by decide) (by decide)
      · right
        exact rec13651 9 42 (by decide) (by decide)
      · right
        exact rec13654 9 42 (by decide) (by decide)
      · right
        exact rec13657 9 42 (by decide) (by decide)
      · right
        exact rec13660 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 279)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 280)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13663 9 42 (by decide) (by decide)
      · right
        exact rec13666 9 42 (by decide) (by decide)
      · right
        exact rec13669 9 42 (by decide) (by decide)
      · right
        exact rec13672 9 42 (by decide) (by decide)
      · right
        exact rec13675 9 42 (by decide) (by decide)
      · right
        exact rec13678 9 42 (by decide) (by decide)
      · right
        exact rec13681 9 42 (by decide) (by decide)
      · right
        exact rec13684 9 42 (by decide) (by decide)
      · right
        exact rec13687 9 42 (by decide) (by decide)
      · right
        exact rec13690 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 281)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 282)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 283)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13693 9 42 (by decide) (by decide)
      · right
        exact rec13696 9 42 (by decide) (by decide)
      · right
        exact rec13699 9 42 (by decide) (by decide)
      · right
        exact rec13702 9 42 (by decide) (by decide)
      · right
        exact rec13705 9 42 (by decide) (by decide)
      · right
        exact rec13708 9 42 (by decide) (by decide)
      · right
        exact rec13711 9 42 (by decide) (by decide)
      · right
        exact rec13714 9 42 (by decide) (by decide)
      · right
        exact rec13717 9 42 (by decide) (by decide)
      · right
        exact rec13720 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 284)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 285)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13723 9 42 (by decide) (by decide)
      · right
        exact rec13726 9 42 (by decide) (by decide)
      · right
        exact rec13729 9 42 (by decide) (by decide)
      · right
        exact rec13732 9 42 (by decide) (by decide)
      · right
        exact rec13735 9 42 (by decide) (by decide)
      · right
        exact rec13738 9 42 (by decide) (by decide)
      · right
        exact rec13741 9 42 (by decide) (by decide)
      · right
        exact rec13744 9 42 (by decide) (by decide)
      · right
        exact rec13747 9 42 (by decide) (by decide)
      · right
        exact rec13750 9 42 (by decide) (by decide)
      · right
        exact rec13753 9 42 (by decide) (by decide)
      · right
        exact rec13756 9 42 (by decide) (by decide)
      · right
        exact rec13759 9 42 (by decide) (by decide)
      · right
        exact rec13762 9 42 (by decide) (by decide)
      · right
        exact rec13765 9 42 (by decide) (by decide)
      · right
        exact rec13768 9 42 (by decide) (by decide)
      · right
        exact rec13771 9 42 (by decide) (by decide)
      · right
        exact rec13774 9 42 (by decide) (by decide)
      · right
        exact rec13777 9 42 (by decide) (by decide)
      · right
        exact rec13780 9 42 (by decide) (by decide)
      · right
        exact rec13783 9 42 (by decide) (by decide)
      · right
        exact rec13786 9 42 (by decide) (by decide)
      · right
        exact rec13789 9 42 (by decide) (by decide)
      · right
        exact rec13792 9 42 (by decide) (by decide)
      · right
        exact rec13795 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 286)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 287)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 288)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13798 9 42 (by decide) (by decide)
      · right
        exact rec13801 9 42 (by decide) (by decide)
      · right
        exact rec13804 9 42 (by decide) (by decide)
      · right
        exact rec13807 9 42 (by decide) (by decide)
      · right
        exact rec13810 9 42 (by decide) (by decide)
      · right
        exact rec13813 9 42 (by decide) (by decide)
      · right
        exact rec13816 9 42 (by decide) (by decide)
      · right
        exact rec13819 9 42 (by decide) (by decide)
      · right
        exact rec13822 9 42 (by decide) (by decide)
      · right
        exact rec13825 9 42 (by decide) (by decide)
      · right
        exact rec13828 9 42 (by decide) (by decide)
      · right
        exact rec13831 9 42 (by decide) (by decide)
      · right
        exact rec13834 9 42 (by decide) (by decide)
      · right
        exact rec13837 9 42 (by decide) (by decide)
      · right
        exact rec13840 9 42 (by decide) (by decide)
      · right
        exact rec13843 9 42 (by decide) (by decide)
      · right
        exact rec13846 9 42 (by decide) (by decide)
      · right
        exact rec13849 9 42 (by decide) (by decide)
      · right
        exact rec13852 9 42 (by decide) (by decide)
      · right
        exact rec13855 9 42 (by decide) (by decide)
      · right
        exact rec13858 9 42 (by decide) (by decide)
      · right
        exact rec13861 9 42 (by decide) (by decide)
      · right
        exact rec13864 9 42 (by decide) (by decide)
      · right
        exact rec13867 9 42 (by decide) (by decide)
      · right
        exact rec13870 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 289)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 290)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13873 9 42 (by decide) (by decide)
      · right
        exact rec13876 9 42 (by decide) (by decide)
      · right
        exact rec13879 9 42 (by decide) (by decide)
      · right
        exact rec13882 9 42 (by decide) (by decide)
      · right
        exact rec13885 9 42 (by decide) (by decide)
      · right
        exact rec13888 9 42 (by decide) (by decide)
      · right
        exact rec13891 9 42 (by decide) (by decide)
      · right
        exact rec13894 9 42 (by decide) (by decide)
      · right
        exact rec13897 9 42 (by decide) (by decide)
      · right
        exact rec13900 9 42 (by decide) (by decide)
      · right
        exact rec13903 9 42 (by decide) (by decide)
      · right
        exact rec13906 9 42 (by decide) (by decide)
      · right
        exact rec13909 9 42 (by decide) (by decide)
      · right
        exact rec13912 9 42 (by decide) (by decide)
      · right
        exact rec13915 9 42 (by decide) (by decide)
      · right
        exact rec13918 9 42 (by decide) (by decide)
      · right
        exact rec13921 9 42 (by decide) (by decide)
      · right
        exact rec13924 9 42 (by decide) (by decide)
      · right
        exact rec13927 9 42 (by decide) (by decide)
      · right
        exact rec13930 9 42 (by decide) (by decide)
      · right
        exact rec13933 9 42 (by decide) (by decide)
      · right
        exact rec13936 9 42 (by decide) (by decide)
      · right
        exact rec13939 9 42 (by decide) (by decide)
      · right
        exact rec13942 9 42 (by decide) (by decide)
      · right
        exact rec13945 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 291)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 292)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 293)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13948 9 42 (by decide) (by decide)
      · right
        exact rec13951 9 42 (by decide) (by decide)
      · right
        exact rec13954 9 42 (by decide) (by decide)
      · right
        exact rec13957 9 42 (by decide) (by decide)
      · right
        exact rec13960 9 42 (by decide) (by decide)
      · right
        exact rec13963 9 42 (by decide) (by decide)
      · right
        exact rec13966 9 42 (by decide) (by decide)
      · right
        exact rec13969 9 42 (by decide) (by decide)
      · right
        exact rec13972 9 42 (by decide) (by decide)
      · right
        exact rec13975 9 42 (by decide) (by decide)
      · right
        exact rec13978 9 42 (by decide) (by decide)
      · right
        exact rec13981 9 42 (by decide) (by decide)
      · right
        exact rec13984 9 42 (by decide) (by decide)
      · right
        exact rec13987 9 42 (by decide) (by decide)
      · right
        exact rec13990 9 42 (by decide) (by decide)
      · right
        exact rec13993 9 42 (by decide) (by decide)
      · right
        exact rec13996 9 42 (by decide) (by decide)
      · right
        exact rec13999 9 42 (by decide) (by decide)
      · right
        exact rec14002 9 42 (by decide) (by decide)
      · right
        exact rec14005 9 42 (by decide) (by decide)
      · right
        exact rec14008 9 42 (by decide) (by decide)
      · right
        exact rec14011 9 42 (by decide) (by decide)
      · right
        exact rec14014 9 42 (by decide) (by decide)
      · right
        exact rec14017 9 42 (by decide) (by decide)
      · right
        exact rec14020 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 294)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 295)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14023 9 42 (by decide) (by decide)
      · right
        exact rec14026 9 42 (by decide) (by decide)
      · right
        exact rec14029 9 42 (by decide) (by decide)
      · right
        exact rec14032 9 42 (by decide) (by decide)
      · right
        exact rec14035 9 42 (by decide) (by decide)
      · right
        exact rec14038 9 42 (by decide) (by decide)
      · right
        exact rec14041 9 42 (by decide) (by decide)
      · right
        exact rec14044 9 42 (by decide) (by decide)
      · right
        exact rec14047 9 42 (by decide) (by decide)
      · right
        exact rec14050 9 42 (by decide) (by decide)
      · right
        exact rec14053 9 42 (by decide) (by decide)
      · right
        exact rec14056 9 42 (by decide) (by decide)
      · right
        exact rec14059 9 42 (by decide) (by decide)
      · right
        exact rec14062 9 42 (by decide) (by decide)
      · right
        exact rec14065 9 42 (by decide) (by decide)
      · right
        exact rec14068 9 42 (by decide) (by decide)
      · right
        exact rec14071 9 42 (by decide) (by decide)
      · right
        exact rec14074 9 42 (by decide) (by decide)
      · right
        exact rec14077 9 42 (by decide) (by decide)
      · right
        exact rec14080 9 42 (by decide) (by decide)
      · right
        exact rec14083 9 42 (by decide) (by decide)
      · right
        exact rec14086 9 42 (by decide) (by decide)
      · right
        exact rec14089 9 42 (by decide) (by decide)
      · right
        exact rec14092 9 42 (by decide) (by decide)
      · right
        exact rec14095 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 296)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 297)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14098 9 42 (by decide) (by decide)
      · right
        exact rec14101 9 42 (by decide) (by decide)
      · right
        exact rec14104 9 42 (by decide) (by decide)
      · right
        exact rec14107 9 42 (by decide) (by decide)
      · right
        exact rec14110 9 42 (by decide) (by decide)
      · right
        exact rec14113 9 42 (by decide) (by decide)
      · right
        exact rec14116 9 42 (by decide) (by decide)
      · right
        exact rec14119 9 42 (by decide) (by decide)
      · right
        exact rec14122 9 42 (by decide) (by decide)
      · right
        exact rec14125 9 42 (by decide) (by decide)
      · right
        exact rec14128 9 42 (by decide) (by decide)
      · right
        exact rec14131 9 42 (by decide) (by decide)
      · right
        exact rec14134 9 42 (by decide) (by decide)
      · right
        exact rec14137 9 42 (by decide) (by decide)
      · right
        exact rec14140 9 42 (by decide) (by decide)
      · right
        exact rec14143 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 298)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 299)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 300)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14146 9 42 (by decide) (by decide)
      · right
        exact rec14149 9 42 (by decide) (by decide)
      · right
        exact rec14152 9 42 (by decide) (by decide)
      · right
        exact rec14155 9 42 (by decide) (by decide)
      · right
        exact rec14158 9 42 (by decide) (by decide)
      · right
        exact rec14161 9 42 (by decide) (by decide)
      · right
        exact rec14164 9 42 (by decide) (by decide)
      · right
        exact rec14167 9 42 (by decide) (by decide)
      · right
        exact rec14170 9 42 (by decide) (by decide)
      · right
        exact rec14173 9 42 (by decide) (by decide)
      · right
        exact rec14176 9 42 (by decide) (by decide)
      · right
        exact rec14179 9 42 (by decide) (by decide)
      · right
        exact rec14182 9 42 (by decide) (by decide)
      · right
        exact rec14185 9 42 (by decide) (by decide)
      · right
        exact rec14188 9 42 (by decide) (by decide)
      · right
        exact rec14191 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 301)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 302)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14194 9 42 (by decide) (by decide)
      · right
        exact rec14197 9 42 (by decide) (by decide)
      · right
        exact rec14200 9 42 (by decide) (by decide)
      · right
        exact rec14203 9 42 (by decide) (by decide)
      · right
        exact rec14206 9 42 (by decide) (by decide)
      · right
        exact rec14209 9 42 (by decide) (by decide)
      · right
        exact rec14212 9 42 (by decide) (by decide)
      · right
        exact rec14215 9 42 (by decide) (by decide)
      · right
        exact rec14218 9 42 (by decide) (by decide)
      · right
        exact rec14221 9 42 (by decide) (by decide)
      · right
        exact rec14224 9 42 (by decide) (by decide)
      · right
        exact rec14227 9 42 (by decide) (by decide)
      · right
        exact rec14230 9 42 (by decide) (by decide)
      · right
        exact rec14233 9 42 (by decide) (by decide)
      · right
        exact rec14236 9 42 (by decide) (by decide)
      · right
        exact rec14239 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 303)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 304)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 305)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14242 9 42 (by decide) (by decide)
      · right
        exact rec14245 9 42 (by decide) (by decide)
      · right
        exact rec14248 9 42 (by decide) (by decide)
      · right
        exact rec14251 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 584)).length = 5 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 307)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14254 9 42 (by decide) (by decide)
      · right
        exact rec14257 9 42 (by decide) (by decide)
      · right
        exact rec14260 9 42 (by decide) (by decide)
      · right
        exact rec14263 9 42 (by decide) (by decide)
      · right
        exact rec14266 9 42 (by decide) (by decide)
      · right
        exact rec14269 9 42 (by decide) (by decide)
      · right
        exact rec14272 9 42 (by decide) (by decide)
      · right
        exact rec14275 9 42 (by decide) (by decide)
      · right
        exact rec14278 9 42 (by decide) (by decide)
      · right
        exact rec14281 9 42 (by decide) (by decide)
      · right
        exact rec14284 9 42 (by decide) (by decide)
      · right
        exact rec14287 9 42 (by decide) (by decide)
      · right
        exact rec14290 9 42 (by decide) (by decide)
      · right
        exact rec14293 9 42 (by decide) (by decide)
      · right
        exact rec14296 9 42 (by decide) (by decide)
      · right
        exact rec14299 9 42 (by decide) (by decide)
      · right
        exact rec14302 9 42 (by decide) (by decide)
      · right
        exact rec14305 9 42 (by decide) (by decide)
      · right
        exact rec14308 9 42 (by decide) (by decide)
      · right
        exact rec14311 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 308)).length = 20 := by decide +kernel
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
      · right
        exact rec14314 9 42 (by decide) (by decide)
      · right
        exact rec14317 9 42 (by decide) (by decide)
      · right
        exact rec14320 9 42 (by decide) (by decide)
      · right
        exact rec14323 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 309)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14326 9 42 (by decide) (by decide)
      · right
        exact rec14329 9 42 (by decide) (by decide)
      · right
        exact rec14332 9 42 (by decide) (by decide)
      · right
        exact rec14335 9 42 (by decide) (by decide)
      · right
        exact rec14338 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 310)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 311)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14341 9 42 (by decide) (by decide)
      · right
        exact rec14344 9 42 (by decide) (by decide)
      · right
        exact rec14347 9 42 (by decide) (by decide)
      · right
        exact rec14350 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 312)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14353 9 42 (by decide) (by decide)
      · right
        exact rec14356 9 42 (by decide) (by decide)
      · right
        exact rec14359 9 42 (by decide) (by decide)
      · right
        exact rec14362 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 313)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14365 9 42 (by decide) (by decide)
      · right
        exact rec14368 9 42 (by decide) (by decide)
      · right
        exact rec14371 9 42 (by decide) (by decide)
      · right
        exact rec14374 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 314)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 315)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14378 9 42 (by decide) (by decide)
      · right
        exact rec14381 9 42 (by decide) (by decide)
      · right
        exact rec14384 9 42 (by decide) (by decide)
      · right
        exact rec14387 9 42 (by decide) (by decide)
      · right
        exact rec14390 9 42 (by decide) (by decide)
      · right
        exact rec14393 9 42 (by decide) (by decide)
      · right
        exact rec14396 9 42 (by decide) (by decide)
      · right
        exact rec14399 9 42 (by decide) (by decide)
      · right
        exact rec14402 9 42 (by decide) (by decide)
      · right
        exact rec14405 9 42 (by decide) (by decide)
      · right
        exact rec14408 9 42 (by decide) (by decide)
      · right
        exact rec14411 9 42 (by decide) (by decide)
      · right
        exact rec14414 9 42 (by decide) (by decide)
      · right
        exact rec14417 9 42 (by decide) (by decide)
      · right
        exact rec14420 9 42 (by decide) (by decide)
      · right
        exact rec14423 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 316)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 317)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14426 9 42 (by decide) (by decide)
      · right
        exact rec14429 9 42 (by decide) (by decide)
      · right
        exact rec14432 9 42 (by decide) (by decide)
      · right
        exact rec14435 9 42 (by decide) (by decide)
      · right
        exact rec14438 9 42 (by decide) (by decide)
      · right
        exact rec14441 9 42 (by decide) (by decide)
      · right
        exact rec14444 9 42 (by decide) (by decide)
      · right
        exact rec14447 9 42 (by decide) (by decide)
      · right
        exact rec14450 9 42 (by decide) (by decide)
      · right
        exact rec14453 9 42 (by decide) (by decide)
      · right
        exact rec14456 9 42 (by decide) (by decide)
      · right
        exact rec14459 9 42 (by decide) (by decide)
      · right
        exact rec14462 9 42 (by decide) (by decide)
      · right
        exact rec14465 9 42 (by decide) (by decide)
      · right
        exact rec14468 9 42 (by decide) (by decide)
      · right
        exact rec14471 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 318)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14474 9 42 (by decide) (by decide)
      · right
        exact rec14477 9 42 (by decide) (by decide)
      · right
        exact rec14480 9 42 (by decide) (by decide)
      · right
        exact rec14483 9 42 (by decide) (by decide)
      · right
        exact rec14486 9 42 (by decide) (by decide)
      · right
        exact rec14489 9 42 (by decide) (by decide)
      · right
        exact rec14492 9 42 (by decide) (by decide)
      · right
        exact rec14495 9 42 (by decide) (by decide)
      · right
        exact rec14498 9 42 (by decide) (by decide)
      · right
        exact rec14501 9 42 (by decide) (by decide)
      · right
        exact rec14504 9 42 (by decide) (by decide)
      · right
        exact rec14507 9 42 (by decide) (by decide)
      · right
        exact rec14510 9 42 (by decide) (by decide)
      · right
        exact rec14513 9 42 (by decide) (by decide)
      · right
        exact rec14516 9 42 (by decide) (by decide)
      · right
        exact rec14519 9 42 (by decide) (by decide)
      · right
        exact rec14522 9 42 (by decide) (by decide)
      · right
        exact rec14525 9 42 (by decide) (by decide)
      · right
        exact rec14528 9 42 (by decide) (by decide)
      · right
        exact rec14531 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 319)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14534 9 42 (by decide) (by decide)
      · right
        exact rec14537 9 42 (by decide) (by decide)
      · right
        exact rec14540 9 42 (by decide) (by decide)
      · right
        exact rec14543 9 42 (by decide) (by decide)
      · right
        exact rec14546 9 42 (by decide) (by decide)
      · right
        exact rec14549 9 42 (by decide) (by decide)
      · right
        exact rec14552 9 42 (by decide) (by decide)
      · right
        exact rec14555 9 42 (by decide) (by decide)
      · right
        exact rec14558 9 42 (by decide) (by decide)
      · right
        exact rec14561 9 42 (by decide) (by decide)
      · right
        exact rec14564 9 42 (by decide) (by decide)
      · right
        exact rec14567 9 42 (by decide) (by decide)
      · right
        exact rec14570 9 42 (by decide) (by decide)
      · right
        exact rec14573 9 42 (by decide) (by decide)
      · right
        exact rec14576 9 42 (by decide) (by decide)
      · right
        exact rec14579 9 42 (by decide) (by decide)
      · right
        exact rec14582 9 42 (by decide) (by decide)
      · right
        exact rec14585 9 42 (by decide) (by decide)
      · right
        exact rec14588 9 42 (by decide) (by decide)
      · right
        exact rec14591 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 320)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 321)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14594 9 42 (by decide) (by decide)
      · right
        exact rec14597 9 42 (by decide) (by decide)
      · right
        exact rec14600 9 42 (by decide) (by decide)
      · right
        exact rec14603 9 42 (by decide) (by decide)
      · right
        exact rec14606 9 42 (by decide) (by decide)
      · right
        exact rec14609 9 42 (by decide) (by decide)
      · right
        exact rec14612 9 42 (by decide) (by decide)
      · right
        exact rec14615 9 42 (by decide) (by decide)
      · right
        exact rec14618 9 42 (by decide) (by decide)
      · right
        exact rec14621 9 42 (by decide) (by decide)
      · right
        exact rec14624 9 42 (by decide) (by decide)
      · right
        exact rec14627 9 42 (by decide) (by decide)
      · right
        exact rec14630 9 42 (by decide) (by decide)
      · right
        exact rec14633 9 42 (by decide) (by decide)
      · right
        exact rec14636 9 42 (by decide) (by decide)
      · right
        exact rec14639 9 42 (by decide) (by decide)
      · right
        exact rec14642 9 42 (by decide) (by decide)
      · right
        exact rec14645 9 42 (by decide) (by decide)
      · right
        exact rec14648 9 42 (by decide) (by decide)
      · right
        exact rec14651 9 42 (by decide) (by decide)
      · right
        exact rec14654 9 42 (by decide) (by decide)
      · right
        exact rec14657 9 42 (by decide) (by decide)
      · right
        exact rec14660 9 42 (by decide) (by decide)
      · right
        exact rec14663 9 42 (by decide) (by decide)
      · right
        exact rec14666 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 585)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 323)).length = 10 := by decide +kernel
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
    exact rec13321 9 43 (by decide) (by decide)
  · left
    exact rec13316 9 44 (by decide) (by decide)
  · left
    exact rec13316 9 45 (by decide) (by decide)
  · left
    exact rec13323 9 46 (by decide) (by decide)
  · left
    exact rec13321 9 47 (by decide) (by decide)
end Section14Coverage_9_7_p32_48

#print axioms solution
