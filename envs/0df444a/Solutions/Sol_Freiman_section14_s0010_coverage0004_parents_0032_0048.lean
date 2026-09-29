-- Prove2me | solution 1 for Freiman.section14_s0010_coverage0004_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:06:39.577837+00:00
-- url     : https://prove2.me/submissions/32e68765-059c-4e47-b4ef-5a7ac2b6d67f

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
namespace Section14Coverage_10_4_p32_48
private theorem rec5604 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[229]? = some (⟨82,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) from rfl))
private theorem rec5608 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[9,10],[34],389⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[233]? = some (⟨82,(-1),[9,10],[34],389⟩) from rfl))
private theorem rec5609 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35, 39, 43, 47] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[9,10],[35,39,43,47],391⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[234]? = some (⟨82,(-1),[9,10],[35,39,43,47],391⟩) from rfl))
private theorem rec5610 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[9,10],[38],392⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[235]? = some (⟨82,(-1),[9,10],[38],392⟩) from rfl))
private theorem rec5611 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 82 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨82,(-1),[9,10],[46],629⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[236]? = some (⟨82,(-1),[9,10],[46],629⟩) from rfl))
private theorem rec5619 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(0),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[244]? = some (⟨84,(0),[9,10],[42],3⟩) from rfl))
private theorem rec5621 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(1),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[246]? = some (⟨84,(1),[9,10],[42],3⟩) from rfl))
private theorem rec5623 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(2),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[248]? = some (⟨84,(2),[9,10],[42],3⟩) from rfl))
private theorem rec5625 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(3),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[250]? = some (⟨84,(3),[9,10],[42],3⟩) from rfl))
private theorem rec5627 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(4),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[252]? = some (⟨84,(4),[9,10],[42],3⟩) from rfl))
private theorem rec5629 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(5),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[254]? = some (⟨84,(5),[9,10],[42],3⟩) from rfl))
private theorem rec5631 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(6),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[256]? = some (⟨84,(6),[9,10],[42],3⟩) from rfl))
private theorem rec5633 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(7),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[258]? = some (⟨84,(7),[9,10],[42],3⟩) from rfl))
private theorem rec5635 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(8),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[260]? = some (⟨84,(8),[9,10],[42],3⟩) from rfl))
private theorem rec5637 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(9),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[262]? = some (⟨84,(9),[9,10],[42],3⟩) from rfl))
private theorem rec5639 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(10),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[264]? = some (⟨84,(10),[9,10],[42],3⟩) from rfl))
private theorem rec5641 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(11),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[266]? = some (⟨84,(11),[9,10],[42],3⟩) from rfl))
private theorem rec5643 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(12),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[268]? = some (⟨84,(12),[9,10],[42],3⟩) from rfl))
private theorem rec5645 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(13),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[270]? = some (⟨84,(13),[9,10],[42],3⟩) from rfl))
private theorem rec5647 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(14),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[272]? = some (⟨84,(14),[9,10],[42],3⟩) from rfl))
private theorem rec5649 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(15),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[274]? = some (⟨84,(15),[9,10],[42],3⟩) from rfl))
private theorem rec5651 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(16),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[276]? = some (⟨84,(16),[9,10],[42],3⟩) from rfl))
private theorem rec5653 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(17),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[278]? = some (⟨84,(17),[9,10],[42],3⟩) from rfl))
private theorem rec5655 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(18),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[280]? = some (⟨84,(18),[9,10],[42],3⟩) from rfl))
private theorem rec5657 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(19),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[282]? = some (⟨84,(19),[9,10],[42],3⟩) from rfl))
private theorem rec5659 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(20),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[284]? = some (⟨84,(20),[9,10],[42],3⟩) from rfl))
private theorem rec5661 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(21),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[286]? = some (⟨84,(21),[9,10],[42],3⟩) from rfl))
private theorem rec5663 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(22),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[288]? = some (⟨84,(22),[9,10],[42],3⟩) from rfl))
private theorem rec5665 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(23),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[290]? = some (⟨84,(23),[9,10],[42],3⟩) from rfl))
private theorem rec5667 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 84 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨84,(24),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[292]? = some (⟨84,(24),[9,10],[42],3⟩) from rfl))
private theorem rec5720 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(0),[9,10],[42],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[345]? = some (⟨89,(0),[9,10],[42],400⟩) from rfl))
private theorem rec5723 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(1),[9,10],[42],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[348]? = some (⟨89,(1),[9,10],[42],401⟩) from rfl))
private theorem rec5726 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(2),[9,10],[42],402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[351]? = some (⟨89,(2),[9,10],[42],402⟩) from rfl))
private theorem rec5729 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(3),[9,10],[42],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[354]? = some (⟨89,(3),[9,10],[42],403⟩) from rfl))
private theorem rec5732 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(4),[9,10],[42],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[357]? = some (⟨89,(4),[9,10],[42],400⟩) from rfl))
private theorem rec5735 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(5),[9,10],[42],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[360]? = some (⟨89,(5),[9,10],[42],401⟩) from rfl))
private theorem rec5738 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(6),[9,10],[42],404⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[363]? = some (⟨89,(6),[9,10],[42],404⟩) from rfl))
private theorem rec5741 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(7),[9,10],[42],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[366]? = some (⟨89,(7),[9,10],[42],403⟩) from rfl))
private theorem rec5744 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(8),[9,10],[42],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[369]? = some (⟨89,(8),[9,10],[42],400⟩) from rfl))
private theorem rec5747 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(9),[9,10],[42],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[372]? = some (⟨89,(9),[9,10],[42],401⟩) from rfl))
private theorem rec5750 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(10),[9,10],[42],402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[375]? = some (⟨89,(10),[9,10],[42],402⟩) from rfl))
private theorem rec5753 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(11),[9,10],[42],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[378]? = some (⟨89,(11),[9,10],[42],403⟩) from rfl))
private theorem rec5756 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(12),[9,10],[42],400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[381]? = some (⟨89,(12),[9,10],[42],400⟩) from rfl))
private theorem rec5759 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(13),[9,10],[42],401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[384]? = some (⟨89,(13),[9,10],[42],401⟩) from rfl))
private theorem rec5762 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(14),[9,10],[42],405⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[387]? = some (⟨89,(14),[9,10],[42],405⟩) from rfl))
private theorem rec5765 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 89 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨89,(15),[9,10],[42],403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[390]? = some (⟨89,(15),[9,10],[42],403⟩) from rfl))
private theorem rec5768 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(0),[9,10],[42],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[393]? = some (⟨92,(0),[9,10],[42],406⟩) from rfl))
private theorem rec5771 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(1),[9,10],[42],407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[396]? = some (⟨92,(1),[9,10],[42],407⟩) from rfl))
private theorem rec5774 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(2),[9,10],[42],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[399]? = some (⟨92,(2),[9,10],[42],406⟩) from rfl))
private theorem rec5777 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(3),[9,10],[42],408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[402]? = some (⟨92,(3),[9,10],[42],408⟩) from rfl))
private theorem rec5780 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(4),[9,10],[42],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[405]? = some (⟨92,(4),[9,10],[42],409⟩) from rfl))
private theorem rec5783 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(5),[9,10],[42],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[408]? = some (⟨92,(5),[9,10],[42],409⟩) from rfl))
private theorem rec5786 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(6),[9,10],[42],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[411]? = some (⟨92,(6),[9,10],[42],409⟩) from rfl))
private theorem rec5789 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(7),[9,10],[42],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[414]? = some (⟨92,(7),[9,10],[42],409⟩) from rfl))
private theorem rec5792 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(8),[9,10],[42],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[417]? = some (⟨92,(8),[9,10],[42],410⟩) from rfl))
private theorem rec5795 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(9),[9,10],[42],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[420]? = some (⟨92,(9),[9,10],[42],410⟩) from rfl))
private theorem rec5798 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(10),[9,10],[42],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[423]? = some (⟨92,(10),[9,10],[42],410⟩) from rfl))
private theorem rec5801 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(11),[9,10],[42],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[426]? = some (⟨92,(11),[9,10],[42],410⟩) from rfl))
private theorem rec5804 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(12),[9,10],[42],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[429]? = some (⟨92,(12),[9,10],[42],411⟩) from rfl))
private theorem rec5807 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(13),[9,10],[42],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[432]? = some (⟨92,(13),[9,10],[42],411⟩) from rfl))
private theorem rec5810 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(14),[9,10],[42],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[435]? = some (⟨92,(14),[9,10],[42],411⟩) from rfl))
private theorem rec5813 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 92 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨92,(15),[9,10],[42],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[438]? = some (⟨92,(15),[9,10],[42],411⟩) from rfl))
private theorem rec5816 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(0),[9,10],[42],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[441]? = some (⟨95,(0),[9,10],[42],412⟩) from rfl))
private theorem rec5819 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(1),[9,10],[42],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[444]? = some (⟨95,(1),[9,10],[42],412⟩) from rfl))
private theorem rec5822 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(2),[9,10],[42],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[447]? = some (⟨95,(2),[9,10],[42],412⟩) from rfl))
private theorem rec5825 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(3),[9,10],[42],412⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[450]? = some (⟨95,(3),[9,10],[42],412⟩) from rfl))
private theorem rec5828 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(4),[9,10],[42],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[453]? = some (⟨95,(4),[9,10],[42],413⟩) from rfl))
private theorem rec5831 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(5),[9,10],[42],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[456]? = some (⟨95,(5),[9,10],[42],413⟩) from rfl))
private theorem rec5834 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(6),[9,10],[42],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[459]? = some (⟨95,(6),[9,10],[42],413⟩) from rfl))
private theorem rec5837 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(7),[9,10],[42],413⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[462]? = some (⟨95,(7),[9,10],[42],413⟩) from rfl))
private theorem rec5840 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(8),[9,10],[42],414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[465]? = some (⟨95,(8),[9,10],[42],414⟩) from rfl))
private theorem rec5843 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(9),[9,10],[42],415⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[468]? = some (⟨95,(9),[9,10],[42],415⟩) from rfl))
private theorem rec5846 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(10),[9,10],[42],414⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[471]? = some (⟨95,(10),[9,10],[42],414⟩) from rfl))
private theorem rec5849 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(11),[9,10],[42],416⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[474]? = some (⟨95,(11),[9,10],[42],416⟩) from rfl))
private theorem rec5852 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(12),[9,10],[42],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[477]? = some (⟨95,(12),[9,10],[42],417⟩) from rfl))
private theorem rec5855 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(13),[9,10],[42],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[480]? = some (⟨95,(13),[9,10],[42],417⟩) from rfl))
private theorem rec5858 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(14),[9,10],[42],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[483]? = some (⟨95,(14),[9,10],[42],417⟩) from rfl))
private theorem rec5861 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 95 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨95,(15),[9,10],[42],417⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[486]? = some (⟨95,(15),[9,10],[42],417⟩) from rfl))
private theorem rec5864 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(0),[9,10],[42],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[489]? = some (⟨96,(0),[9,10],[42],418⟩) from rfl))
private theorem rec5867 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(1),[9,10],[42],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[492]? = some (⟨96,(1),[9,10],[42],419⟩) from rfl))
private theorem rec5870 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(2),[9,10],[42],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[495]? = some (⟨96,(2),[9,10],[42],420⟩) from rfl))
private theorem rec5873 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(3),[9,10],[42],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[498]? = some (⟨96,(3),[9,10],[42],421⟩) from rfl))
private theorem rec5876 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(4),[9,10],[42],422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[501]? = some (⟨96,(4),[9,10],[42],422⟩) from rfl))
private theorem rec5879 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(5),[9,10],[42],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[504]? = some (⟨96,(5),[9,10],[42],419⟩) from rfl))
private theorem rec5882 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(6),[9,10],[42],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[507]? = some (⟨96,(6),[9,10],[42],420⟩) from rfl))
private theorem rec5885 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(7),[9,10],[42],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[510]? = some (⟨96,(7),[9,10],[42],421⟩) from rfl))
private theorem rec5888 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(8),[9,10],[42],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[513]? = some (⟨96,(8),[9,10],[42],418⟩) from rfl))
private theorem rec5891 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(9),[9,10],[42],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[516]? = some (⟨96,(9),[9,10],[42],419⟩) from rfl))
private theorem rec5894 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(10),[9,10],[42],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[519]? = some (⟨96,(10),[9,10],[42],420⟩) from rfl))
private theorem rec5897 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(11),[9,10],[42],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[522]? = some (⟨96,(11),[9,10],[42],421⟩) from rfl))
private theorem rec5900 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(12),[9,10],[42],423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[525]? = some (⟨96,(12),[9,10],[42],423⟩) from rfl))
private theorem rec5903 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(13),[9,10],[42],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[528]? = some (⟨96,(13),[9,10],[42],419⟩) from rfl))
private theorem rec5906 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(14),[9,10],[42],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[531]? = some (⟨96,(14),[9,10],[42],420⟩) from rfl))
private theorem rec5909 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 96 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨96,(15),[9,10],[42],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[534]? = some (⟨96,(15),[9,10],[42],421⟩) from rfl))
private theorem rec5912 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 100 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(0),[9,10],[42],424⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[537]? = some (⟨100,(0),[9,10],[42],424⟩) from rfl))
private theorem rec5915 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 100 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(1),[9,10],[42],425⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[540]? = some (⟨100,(1),[9,10],[42],425⟩) from rfl))
private theorem rec5918 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 100 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(2),[9,10],[42],426⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[543]? = some (⟨100,(2),[9,10],[42],426⟩) from rfl))
private theorem rec5921 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 100 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨100,(3),[9,10],[42],427⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[546]? = some (⟨100,(3),[9,10],[42],427⟩) from rfl))
private theorem rec5924 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(0),[9,10],[42],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[549]? = some (⟨101,(0),[9,10],[42],428⟩) from rfl))
private theorem rec5927 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(1),[9,10],[42],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[552]? = some (⟨101,(1),[9,10],[42],429⟩) from rfl))
private theorem rec5930 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(2),[9,10],[42],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[555]? = some (⟨101,(2),[9,10],[42],430⟩) from rfl))
private theorem rec5933 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(3),[9,10],[42],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[558]? = some (⟨101,(3),[9,10],[42],431⟩) from rfl))
private theorem rec5936 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(4),[9,10],[42],432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[561]? = some (⟨101,(4),[9,10],[42],432⟩) from rfl))
private theorem rec5939 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(5),[9,10],[42],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[564]? = some (⟨101,(5),[9,10],[42],429⟩) from rfl))
private theorem rec5942 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(6),[9,10],[42],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[567]? = some (⟨101,(6),[9,10],[42],430⟩) from rfl))
private theorem rec5945 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(7),[9,10],[42],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[570]? = some (⟨101,(7),[9,10],[42],431⟩) from rfl))
private theorem rec5948 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(8),[9,10],[42],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[573]? = some (⟨101,(8),[9,10],[42],428⟩) from rfl))
private theorem rec5951 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(9),[9,10],[42],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[576]? = some (⟨101,(9),[9,10],[42],429⟩) from rfl))
private theorem rec5954 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(10),[9,10],[42],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[579]? = some (⟨101,(10),[9,10],[42],430⟩) from rfl))
private theorem rec5957 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(11),[9,10],[42],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[582]? = some (⟨101,(11),[9,10],[42],431⟩) from rfl))
private theorem rec5960 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(12),[9,10],[42],433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[585]? = some (⟨101,(12),[9,10],[42],433⟩) from rfl))
private theorem rec5963 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(13),[9,10],[42],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[588]? = some (⟨101,(13),[9,10],[42],429⟩) from rfl))
private theorem rec5966 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(14),[9,10],[42],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[591]? = some (⟨101,(14),[9,10],[42],430⟩) from rfl))
private theorem rec5969 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 101 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨101,(15),[9,10],[42],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[594]? = some (⟨101,(15),[9,10],[42],431⟩) from rfl))
private theorem rec5972 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(0),[9,10],[42],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[597]? = some (⟨104,(0),[9,10],[42],434⟩) from rfl))
private theorem rec5975 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(1),[9,10],[42],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[600]? = some (⟨104,(1),[9,10],[42],434⟩) from rfl))
private theorem rec5978 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(2),[9,10],[42],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[603]? = some (⟨104,(2),[9,10],[42],434⟩) from rfl))
private theorem rec5981 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(3),[9,10],[42],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[606]? = some (⟨104,(3),[9,10],[42],434⟩) from rfl))
private theorem rec5984 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(4),[9,10],[42],434⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[609]? = some (⟨104,(4),[9,10],[42],434⟩) from rfl))
private theorem rec5987 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(5),[9,10],[42],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[612]? = some (⟨104,(5),[9,10],[42],435⟩) from rfl))
private theorem rec5990 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(6),[9,10],[42],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[615]? = some (⟨104,(6),[9,10],[42],435⟩) from rfl))
private theorem rec5993 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(7),[9,10],[42],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[618]? = some (⟨104,(7),[9,10],[42],435⟩) from rfl))
private theorem rec5996 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(8),[9,10],[42],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[621]? = some (⟨104,(8),[9,10],[42],435⟩) from rfl))
private theorem rec5999 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(9),[9,10],[42],435⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[624]? = some (⟨104,(9),[9,10],[42],435⟩) from rfl))
private theorem rec6002 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(10),[9,10],[42],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[627]? = some (⟨104,(10),[9,10],[42],436⟩) from rfl))
private theorem rec6005 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(11),[9,10],[42],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[630]? = some (⟨104,(11),[9,10],[42],437⟩) from rfl))
private theorem rec6008 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(12),[9,10],[42],438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[633]? = some (⟨104,(12),[9,10],[42],438⟩) from rfl))
private theorem rec6011 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(13),[9,10],[42],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[636]? = some (⟨104,(13),[9,10],[42],437⟩) from rfl))
private theorem rec6014 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(14),[9,10],[42],439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[639]? = some (⟨104,(14),[9,10],[42],439⟩) from rfl))
private theorem rec6017 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(15),[9,10],[42],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[642]? = some (⟨104,(15),[9,10],[42],436⟩) from rfl))
private theorem rec6020 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(16),[9,10],[42],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[645]? = some (⟨104,(16),[9,10],[42],440⟩) from rfl))
private theorem rec6023 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(17),[9,10],[42],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[648]? = some (⟨104,(17),[9,10],[42],440⟩) from rfl))
private theorem rec6026 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(18),[9,10],[42],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[651]? = some (⟨104,(18),[9,10],[42],440⟩) from rfl))
private theorem rec6029 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(19),[9,10],[42],440⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[654]? = some (⟨104,(19),[9,10],[42],440⟩) from rfl))
private theorem rec6032 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(20),[9,10],[42],436⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[657]? = some (⟨104,(20),[9,10],[42],436⟩) from rfl))
private theorem rec6035 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(21),[9,10],[42],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[660]? = some (⟨104,(21),[9,10],[42],437⟩) from rfl))
private theorem rec6038 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(22),[9,10],[42],438⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[663]? = some (⟨104,(22),[9,10],[42],438⟩) from rfl))
private theorem rec6041 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(23),[9,10],[42],437⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[666]? = some (⟨104,(23),[9,10],[42],437⟩) from rfl))
private theorem rec6044 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 104 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨104,(24),[9,10],[42],439⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[669]? = some (⟨104,(24),[9,10],[42],439⟩) from rfl))
private theorem rec6047 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(0),[9,10],[42],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[672]? = some (⟨106,(0),[9,10],[42],441⟩) from rfl))
private theorem rec6050 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(1),[9,10],[42],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[675]? = some (⟨106,(1),[9,10],[42],442⟩) from rfl))
private theorem rec6053 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(2),[9,10],[42],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[678]? = some (⟨106,(2),[9,10],[42],441⟩) from rfl))
private theorem rec6056 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(3),[9,10],[42],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[681]? = some (⟨106,(3),[9,10],[42],443⟩) from rfl))
private theorem rec6059 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(4),[9,10],[42],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[684]? = some (⟨106,(4),[9,10],[42],444⟩) from rfl))
private theorem rec6062 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(5),[9,10],[42],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[687]? = some (⟨106,(5),[9,10],[42],441⟩) from rfl))
private theorem rec6065 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(6),[9,10],[42],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[690]? = some (⟨106,(6),[9,10],[42],442⟩) from rfl))
private theorem rec6068 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(7),[9,10],[42],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[693]? = some (⟨106,(7),[9,10],[42],441⟩) from rfl))
private theorem rec6071 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(8),[9,10],[42],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[696]? = some (⟨106,(8),[9,10],[42],443⟩) from rfl))
private theorem rec6074 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(9),[9,10],[42],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[699]? = some (⟨106,(9),[9,10],[42],444⟩) from rfl))
private theorem rec6077 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(10),[9,10],[42],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[702]? = some (⟨106,(10),[9,10],[42],445⟩) from rfl))
private theorem rec6080 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(11),[9,10],[42],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[705]? = some (⟨106,(11),[9,10],[42],445⟩) from rfl))
private theorem rec6083 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(12),[9,10],[42],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[708]? = some (⟨106,(12),[9,10],[42],445⟩) from rfl))
private theorem rec6086 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(13),[9,10],[42],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[711]? = some (⟨106,(13),[9,10],[42],445⟩) from rfl))
private theorem rec6089 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(14),[9,10],[42],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[714]? = some (⟨106,(14),[9,10],[42],444⟩) from rfl))
private theorem rec6092 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(15),[9,10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[717]? = some (⟨106,(15),[9,10],[42],446⟩) from rfl))
private theorem rec6095 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(16),[9,10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[720]? = some (⟨106,(16),[9,10],[42],446⟩) from rfl))
private theorem rec6098 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(17),[9,10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[723]? = some (⟨106,(17),[9,10],[42],446⟩) from rfl))
private theorem rec6101 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(18),[9,10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[726]? = some (⟨106,(18),[9,10],[42],446⟩) from rfl))
private theorem rec6104 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(19),[9,10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[729]? = some (⟨106,(19),[9,10],[42],446⟩) from rfl))
private theorem rec6107 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(20),[9,10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[732]? = some (⟨106,(20),[9,10],[42],447⟩) from rfl))
private theorem rec6110 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(21),[9,10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[735]? = some (⟨106,(21),[9,10],[42],447⟩) from rfl))
private theorem rec6113 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(22),[9,10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[738]? = some (⟨106,(22),[9,10],[42],447⟩) from rfl))
private theorem rec6116 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(23),[9,10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[741]? = some (⟨106,(23),[9,10],[42],447⟩) from rfl))
private theorem rec6119 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 106 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨106,(24),[9,10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[744]? = some (⟨106,(24),[9,10],[42],447⟩) from rfl))
private theorem rec6122 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(0),[9,10],[42],448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[747]? = some (⟨109,(0),[9,10],[42],448⟩) from rfl))
private theorem rec6125 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(1),[9,10],[42],448⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[750]? = some (⟨109,(1),[9,10],[42],448⟩) from rfl))
private theorem rec6128 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(2),[9,10],[42],449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[753]? = some (⟨109,(2),[9,10],[42],449⟩) from rfl))
private theorem rec6131 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(3),[9,10],[42],449⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[756]? = some (⟨109,(3),[9,10],[42],449⟩) from rfl))
private theorem rec6134 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(4),[9,10],[42],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[759]? = some (⟨109,(4),[9,10],[42],450⟩) from rfl))
private theorem rec6137 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(5),[9,10],[42],451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[762]? = some (⟨109,(5),[9,10],[42],451⟩) from rfl))
private theorem rec6140 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(6),[9,10],[42],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[765]? = some (⟨109,(6),[9,10],[42],450⟩) from rfl))
private theorem rec6143 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(7),[9,10],[42],452⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[768]? = some (⟨109,(7),[9,10],[42],452⟩) from rfl))
private theorem rec6146 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(8),[9,10],[42],450⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[771]? = some (⟨109,(8),[9,10],[42],450⟩) from rfl))
private theorem rec6149 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 109 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨109,(9),[9,10],[42],451⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[774]? = some (⟨109,(9),[9,10],[42],451⟩) from rfl))
private theorem rec6152 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(0),[9,10],[42],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[777]? = some (⟨111,(0),[9,10],[42],453⟩) from rfl))
private theorem rec6155 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(1),[9,10],[42],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[780]? = some (⟨111,(1),[9,10],[42],454⟩) from rfl))
private theorem rec6158 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(2),[9,10],[42],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[783]? = some (⟨111,(2),[9,10],[42],453⟩) from rfl))
private theorem rec6161 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(3),[9,10],[42],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[786]? = some (⟨111,(3),[9,10],[42],455⟩) from rfl))
private theorem rec6164 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(4),[9,10],[42],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[789]? = some (⟨111,(4),[9,10],[42],456⟩) from rfl))
private theorem rec6167 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(5),[9,10],[42],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[792]? = some (⟨111,(5),[9,10],[42],453⟩) from rfl))
private theorem rec6170 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(6),[9,10],[42],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[795]? = some (⟨111,(6),[9,10],[42],454⟩) from rfl))
private theorem rec6173 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(7),[9,10],[42],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[798]? = some (⟨111,(7),[9,10],[42],453⟩) from rfl))
private theorem rec6176 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(8),[9,10],[42],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[801]? = some (⟨111,(8),[9,10],[42],455⟩) from rfl))
private theorem rec6179 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(9),[9,10],[42],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[804]? = some (⟨111,(9),[9,10],[42],456⟩) from rfl))
private theorem rec6182 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(10),[9,10],[42],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[807]? = some (⟨111,(10),[9,10],[42],457⟩) from rfl))
private theorem rec6185 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(11),[9,10],[42],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[810]? = some (⟨111,(11),[9,10],[42],457⟩) from rfl))
private theorem rec6188 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(12),[9,10],[42],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[813]? = some (⟨111,(12),[9,10],[42],457⟩) from rfl))
private theorem rec6191 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(13),[9,10],[42],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[816]? = some (⟨111,(13),[9,10],[42],457⟩) from rfl))
private theorem rec6194 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(14),[9,10],[42],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[819]? = some (⟨111,(14),[9,10],[42],456⟩) from rfl))
private theorem rec6197 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(15),[9,10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[822]? = some (⟨111,(15),[9,10],[42],458⟩) from rfl))
private theorem rec6200 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(16),[9,10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[825]? = some (⟨111,(16),[9,10],[42],458⟩) from rfl))
private theorem rec6203 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(17),[9,10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[828]? = some (⟨111,(17),[9,10],[42],458⟩) from rfl))
private theorem rec6206 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(18),[9,10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[831]? = some (⟨111,(18),[9,10],[42],458⟩) from rfl))
private theorem rec6209 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(19),[9,10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[834]? = some (⟨111,(19),[9,10],[42],458⟩) from rfl))
private theorem rec6212 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(20),[9,10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[837]? = some (⟨111,(20),[9,10],[42],459⟩) from rfl))
private theorem rec6215 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(21),[9,10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[840]? = some (⟨111,(21),[9,10],[42],459⟩) from rfl))
private theorem rec6218 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(22),[9,10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[843]? = some (⟨111,(22),[9,10],[42],459⟩) from rfl))
private theorem rec6221 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(23),[9,10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[846]? = some (⟨111,(23),[9,10],[42],459⟩) from rfl))
private theorem rec6224 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 111 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨111,(24),[9,10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[849]? = some (⟨111,(24),[9,10],[42],459⟩) from rfl))
private theorem rec6227 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(0),[9,10],[42],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[852]? = some (⟨114,(0),[9,10],[42],460⟩) from rfl))
private theorem rec6230 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(1),[9,10],[42],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[855]? = some (⟨114,(1),[9,10],[42],460⟩) from rfl))
private theorem rec6233 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(2),[9,10],[42],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[858]? = some (⟨114,(2),[9,10],[42],460⟩) from rfl))
private theorem rec6236 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(3),[9,10],[42],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[861]? = some (⟨114,(3),[9,10],[42],460⟩) from rfl))
private theorem rec6239 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(4),[9,10],[42],460⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[864]? = some (⟨114,(4),[9,10],[42],460⟩) from rfl))
private theorem rec6242 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(5),[9,10],[42],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[867]? = some (⟨114,(5),[9,10],[42],461⟩) from rfl))
private theorem rec6245 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(6),[9,10],[42],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[870]? = some (⟨114,(6),[9,10],[42],461⟩) from rfl))
private theorem rec6248 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(7),[9,10],[42],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[873]? = some (⟨114,(7),[9,10],[42],461⟩) from rfl))
private theorem rec6251 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(8),[9,10],[42],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[876]? = some (⟨114,(8),[9,10],[42],461⟩) from rfl))
private theorem rec6254 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(9),[9,10],[42],461⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[879]? = some (⟨114,(9),[9,10],[42],461⟩) from rfl))
private theorem rec6257 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(10),[9,10],[42],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[882]? = some (⟨114,(10),[9,10],[42],462⟩) from rfl))
private theorem rec6260 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(11),[9,10],[42],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[885]? = some (⟨114,(11),[9,10],[42],463⟩) from rfl))
private theorem rec6263 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(12),[9,10],[42],464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[888]? = some (⟨114,(12),[9,10],[42],464⟩) from rfl))
private theorem rec6266 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(13),[9,10],[42],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[891]? = some (⟨114,(13),[9,10],[42],463⟩) from rfl))
private theorem rec6269 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(14),[9,10],[42],465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[894]? = some (⟨114,(14),[9,10],[42],465⟩) from rfl))
private theorem rec6272 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(15),[9,10],[42],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[897]? = some (⟨114,(15),[9,10],[42],462⟩) from rfl))
private theorem rec6275 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(16),[9,10],[42],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[900]? = some (⟨114,(16),[9,10],[42],466⟩) from rfl))
private theorem rec6278 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(17),[9,10],[42],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[903]? = some (⟨114,(17),[9,10],[42],466⟩) from rfl))
private theorem rec6281 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(18),[9,10],[42],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[906]? = some (⟨114,(18),[9,10],[42],466⟩) from rfl))
private theorem rec6284 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(19),[9,10],[42],466⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[909]? = some (⟨114,(19),[9,10],[42],466⟩) from rfl))
private theorem rec6287 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(20),[9,10],[42],462⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[912]? = some (⟨114,(20),[9,10],[42],462⟩) from rfl))
private theorem rec6290 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(21),[9,10],[42],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[915]? = some (⟨114,(21),[9,10],[42],463⟩) from rfl))
private theorem rec6293 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(22),[9,10],[42],464⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[918]? = some (⟨114,(22),[9,10],[42],464⟩) from rfl))
private theorem rec6296 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(23),[9,10],[42],463⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[921]? = some (⟨114,(23),[9,10],[42],463⟩) from rfl))
private theorem rec6299 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 114 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨114,(24),[9,10],[42],465⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[924]? = some (⟨114,(24),[9,10],[42],465⟩) from rfl))
private theorem rec6302 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(0),[9,10],[42],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[927]? = some (⟨116,(0),[9,10],[42],467⟩) from rfl))
private theorem rec6305 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(1),[9,10],[42],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[930]? = some (⟨116,(1),[9,10],[42],468⟩) from rfl))
private theorem rec6308 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(2),[9,10],[42],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[933]? = some (⟨116,(2),[9,10],[42],467⟩) from rfl))
private theorem rec6311 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(3),[9,10],[42],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[936]? = some (⟨116,(3),[9,10],[42],469⟩) from rfl))
private theorem rec6314 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(4),[9,10],[42],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[939]? = some (⟨116,(4),[9,10],[42],470⟩) from rfl))
private theorem rec6317 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(5),[9,10],[42],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[942]? = some (⟨116,(5),[9,10],[42],467⟩) from rfl))
private theorem rec6320 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(6),[9,10],[42],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[945]? = some (⟨116,(6),[9,10],[42],468⟩) from rfl))
private theorem rec6323 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(7),[9,10],[42],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[948]? = some (⟨116,(7),[9,10],[42],467⟩) from rfl))
private theorem rec6326 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(8),[9,10],[42],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[951]? = some (⟨116,(8),[9,10],[42],469⟩) from rfl))
private theorem rec6329 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(9),[9,10],[42],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[954]? = some (⟨116,(9),[9,10],[42],470⟩) from rfl))
private theorem rec6332 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(10),[9,10],[42],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[957]? = some (⟨116,(10),[9,10],[42],471⟩) from rfl))
private theorem rec6335 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(11),[9,10],[42],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[960]? = some (⟨116,(11),[9,10],[42],471⟩) from rfl))
private theorem rec6338 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(12),[9,10],[42],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[963]? = some (⟨116,(12),[9,10],[42],471⟩) from rfl))
private theorem rec6341 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(13),[9,10],[42],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[966]? = some (⟨116,(13),[9,10],[42],471⟩) from rfl))
private theorem rec6344 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(14),[9,10],[42],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[969]? = some (⟨116,(14),[9,10],[42],470⟩) from rfl))
private theorem rec6347 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(15),[9,10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[972]? = some (⟨116,(15),[9,10],[42],472⟩) from rfl))
private theorem rec6350 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(16),[9,10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[975]? = some (⟨116,(16),[9,10],[42],472⟩) from rfl))
private theorem rec6353 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(17),[9,10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[978]? = some (⟨116,(17),[9,10],[42],472⟩) from rfl))
private theorem rec6356 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(18),[9,10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[981]? = some (⟨116,(18),[9,10],[42],472⟩) from rfl))
private theorem rec6359 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(19),[9,10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[984]? = some (⟨116,(19),[9,10],[42],472⟩) from rfl))
private theorem rec6362 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(20),[9,10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[987]? = some (⟨116,(20),[9,10],[42],473⟩) from rfl))
private theorem rec6365 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(21),[9,10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[990]? = some (⟨116,(21),[9,10],[42],473⟩) from rfl))
private theorem rec6368 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(22),[9,10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[993]? = some (⟨116,(22),[9,10],[42],473⟩) from rfl))
private theorem rec6371 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(23),[9,10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[996]? = some (⟨116,(23),[9,10],[42],473⟩) from rfl))
private theorem rec6374 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 116 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨116,(24),[9,10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[999]? = some (⟨116,(24),[9,10],[42],473⟩) from rfl))
private theorem rec6377 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(0),[9,10],[42],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1002]? = some (⟨119,(0),[9,10],[42],474⟩) from rfl))
private theorem rec6380 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(1),[9,10],[42],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1005]? = some (⟨119,(1),[9,10],[42],474⟩) from rfl))
private theorem rec6383 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(2),[9,10],[42],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1008]? = some (⟨119,(2),[9,10],[42],474⟩) from rfl))
private theorem rec6387 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(3),[10],[42],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1012]? = some (⟨119,(3),[10],[42],474⟩) from rfl))
private theorem rec6390 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(4),[9,10],[42],474⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1015]? = some (⟨119,(4),[9,10],[42],474⟩) from rfl))
private theorem rec6393 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(5),[9,10],[42],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1018]? = some (⟨119,(5),[9,10],[42],475⟩) from rfl))
private theorem rec6396 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(6),[9,10],[42],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1021]? = some (⟨119,(6),[9,10],[42],475⟩) from rfl))
private theorem rec6399 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(7),[9,10],[42],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1024]? = some (⟨119,(7),[9,10],[42],475⟩) from rfl))
private theorem rec6403 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(8),[10],[42],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1028]? = some (⟨119,(8),[10],[42],475⟩) from rfl))
private theorem rec6406 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(9),[9,10],[42],475⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1031]? = some (⟨119,(9),[9,10],[42],475⟩) from rfl))
private theorem rec6409 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(10),[9,10],[42],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1034]? = some (⟨119,(10),[9,10],[42],476⟩) from rfl))
private theorem rec6412 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(11),[9,10],[42],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1037]? = some (⟨119,(11),[9,10],[42],477⟩) from rfl))
private theorem rec6415 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(12),[9,10],[42],478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1040]? = some (⟨119,(12),[9,10],[42],478⟩) from rfl))
private theorem rec6419 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(13),[10],[42],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1044]? = some (⟨119,(13),[10],[42],477⟩) from rfl))
private theorem rec6422 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(14),[9,10],[42],479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1047]? = some (⟨119,(14),[9,10],[42],479⟩) from rfl))
private theorem rec6425 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(15),[9,10],[42],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1050]? = some (⟨119,(15),[9,10],[42],476⟩) from rfl))
private theorem rec6428 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(16),[9,10],[42],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1053]? = some (⟨119,(16),[9,10],[42],480⟩) from rfl))
private theorem rec6431 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(17),[9,10],[42],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1056]? = some (⟨119,(17),[9,10],[42],480⟩) from rfl))
private theorem rec6435 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(18),[10],[42],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1060]? = some (⟨119,(18),[10],[42],480⟩) from rfl))
private theorem rec6438 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(19),[9,10],[42],480⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1063]? = some (⟨119,(19),[9,10],[42],480⟩) from rfl))
private theorem rec6441 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(20),[9,10],[42],476⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1066]? = some (⟨119,(20),[9,10],[42],476⟩) from rfl))
private theorem rec6444 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(21),[9,10],[42],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1069]? = some (⟨119,(21),[9,10],[42],477⟩) from rfl))
private theorem rec6447 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(22),[9,10],[42],478⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1072]? = some (⟨119,(22),[9,10],[42],478⟩) from rfl))
private theorem rec6451 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(23),[10],[42],477⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1076]? = some (⟨119,(23),[10],[42],477⟩) from rfl))
private theorem rec6454 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 119 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨119,(24),[9,10],[42],479⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1079]? = some (⟨119,(24),[9,10],[42],479⟩) from rfl))
private theorem rec6457 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(0),[9,10],[42],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1082]? = some (⟨121,(0),[9,10],[42],481⟩) from rfl))
private theorem rec6460 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(1),[9,10],[42],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1085]? = some (⟨121,(1),[9,10],[42],482⟩) from rfl))
private theorem rec6463 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(2),[9,10],[42],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1088]? = some (⟨121,(2),[9,10],[42],481⟩) from rfl))
private theorem rec6466 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(3),[9,10],[42],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1091]? = some (⟨121,(3),[9,10],[42],483⟩) from rfl))
private theorem rec6469 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(4),[9,10],[42],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1094]? = some (⟨121,(4),[9,10],[42],484⟩) from rfl))
private theorem rec6472 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(5),[9,10],[42],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1097]? = some (⟨121,(5),[9,10],[42],481⟩) from rfl))
private theorem rec6475 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(6),[9,10],[42],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1100]? = some (⟨121,(6),[9,10],[42],482⟩) from rfl))
private theorem rec6478 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(7),[9,10],[42],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1103]? = some (⟨121,(7),[9,10],[42],481⟩) from rfl))
private theorem rec6481 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(8),[9,10],[42],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1106]? = some (⟨121,(8),[9,10],[42],483⟩) from rfl))
private theorem rec6484 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(9),[9,10],[42],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1109]? = some (⟨121,(9),[9,10],[42],484⟩) from rfl))
private theorem rec6487 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(10),[9,10],[42],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1112]? = some (⟨121,(10),[9,10],[42],485⟩) from rfl))
private theorem rec6490 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(11),[9,10],[42],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1115]? = some (⟨121,(11),[9,10],[42],485⟩) from rfl))
private theorem rec6493 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(12),[9,10],[42],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1118]? = some (⟨121,(12),[9,10],[42],485⟩) from rfl))
private theorem rec6496 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(13),[9,10],[42],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1121]? = some (⟨121,(13),[9,10],[42],485⟩) from rfl))
private theorem rec6499 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(14),[9,10],[42],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1124]? = some (⟨121,(14),[9,10],[42],484⟩) from rfl))
private theorem rec6502 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(15),[9,10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1127]? = some (⟨121,(15),[9,10],[42],486⟩) from rfl))
private theorem rec6505 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(16),[9,10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1130]? = some (⟨121,(16),[9,10],[42],486⟩) from rfl))
private theorem rec6508 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(17),[9,10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1133]? = some (⟨121,(17),[9,10],[42],486⟩) from rfl))
private theorem rec6511 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(18),[9,10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1136]? = some (⟨121,(18),[9,10],[42],486⟩) from rfl))
private theorem rec6514 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(19),[9,10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1139]? = some (⟨121,(19),[9,10],[42],486⟩) from rfl))
private theorem rec6517 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(20),[9,10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1142]? = some (⟨121,(20),[9,10],[42],487⟩) from rfl))
private theorem rec6520 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(21),[9,10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1145]? = some (⟨121,(21),[9,10],[42],487⟩) from rfl))
private theorem rec6523 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(22),[9,10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1148]? = some (⟨121,(22),[9,10],[42],487⟩) from rfl))
private theorem rec6526 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(23),[9,10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1151]? = some (⟨121,(23),[9,10],[42],487⟩) from rfl))
private theorem rec6529 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 121 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨121,(24),[9,10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1154]? = some (⟨121,(24),[9,10],[42],487⟩) from rfl))
private theorem rec6532 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(0),[9,10],[42],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[0]? = some (⟨124,(0),[9,10],[42],488⟩) from rfl))
private theorem rec6535 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(1),[9,10],[42],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[3]? = some (⟨124,(1),[9,10],[42],489⟩) from rfl))
private theorem rec6538 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(2),[9,10],[42],490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[6]? = some (⟨124,(2),[9,10],[42],490⟩) from rfl))
private theorem rec6541 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(3),[9,10],[42],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[9]? = some (⟨124,(3),[9,10],[42],491⟩) from rfl))
private theorem rec6544 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(4),[9,10],[42],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[12]? = some (⟨124,(4),[9,10],[42],488⟩) from rfl))
private theorem rec6547 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(5),[9,10],[42],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[15]? = some (⟨124,(5),[9,10],[42],489⟩) from rfl))
private theorem rec6550 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(6),[9,10],[42],492⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[18]? = some (⟨124,(6),[9,10],[42],492⟩) from rfl))
private theorem rec6553 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(7),[9,10],[42],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[21]? = some (⟨124,(7),[9,10],[42],491⟩) from rfl))
private theorem rec6556 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(8),[9,10],[42],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[24]? = some (⟨124,(8),[9,10],[42],488⟩) from rfl))
private theorem rec6559 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(9),[9,10],[42],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[27]? = some (⟨124,(9),[9,10],[42],489⟩) from rfl))
private theorem rec6562 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(10),[9,10],[42],490⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[30]? = some (⟨124,(10),[9,10],[42],490⟩) from rfl))
private theorem rec6565 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(11),[9,10],[42],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[33]? = some (⟨124,(11),[9,10],[42],491⟩) from rfl))
private theorem rec6568 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(12),[9,10],[42],488⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[36]? = some (⟨124,(12),[9,10],[42],488⟩) from rfl))
private theorem rec6571 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(13),[9,10],[42],489⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[39]? = some (⟨124,(13),[9,10],[42],489⟩) from rfl))
private theorem rec6574 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(14),[9,10],[42],493⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[42]? = some (⟨124,(14),[9,10],[42],493⟩) from rfl))
private theorem rec6577 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 124 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨124,(15),[9,10],[42],491⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[45]? = some (⟨124,(15),[9,10],[42],491⟩) from rfl))
private theorem rec6580 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(0),[9,10],[42],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[48]? = some (⟨127,(0),[9,10],[42],494⟩) from rfl))
private theorem rec6583 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(1),[9,10],[42],495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[51]? = some (⟨127,(1),[9,10],[42],495⟩) from rfl))
private theorem rec6586 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(2),[9,10],[42],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[54]? = some (⟨127,(2),[9,10],[42],494⟩) from rfl))
private theorem rec6589 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(3),[9,10],[42],496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[57]? = some (⟨127,(3),[9,10],[42],496⟩) from rfl))
private theorem rec6592 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(4),[9,10],[42],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[60]? = some (⟨127,(4),[9,10],[42],497⟩) from rfl))
private theorem rec6595 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(5),[9,10],[42],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[63]? = some (⟨127,(5),[9,10],[42],497⟩) from rfl))
private theorem rec6598 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(6),[9,10],[42],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[66]? = some (⟨127,(6),[9,10],[42],497⟩) from rfl))
private theorem rec6601 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(7),[9,10],[42],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[69]? = some (⟨127,(7),[9,10],[42],497⟩) from rfl))
private theorem rec6604 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(8),[9,10],[42],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[72]? = some (⟨127,(8),[9,10],[42],498⟩) from rfl))
private theorem rec6607 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(9),[9,10],[42],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[75]? = some (⟨127,(9),[9,10],[42],498⟩) from rfl))
private theorem rec6610 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(10),[9,10],[42],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[78]? = some (⟨127,(10),[9,10],[42],498⟩) from rfl))
private theorem rec6613 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(11),[9,10],[42],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[81]? = some (⟨127,(11),[9,10],[42],498⟩) from rfl))
private theorem rec6616 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(12),[9,10],[42],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[84]? = some (⟨127,(12),[9,10],[42],499⟩) from rfl))
private theorem rec6619 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(13),[9,10],[42],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[87]? = some (⟨127,(13),[9,10],[42],499⟩) from rfl))
private theorem rec6622 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(14),[9,10],[42],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[90]? = some (⟨127,(14),[9,10],[42],499⟩) from rfl))
private theorem rec6625 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 127 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨127,(15),[9,10],[42],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[93]? = some (⟨127,(15),[9,10],[42],499⟩) from rfl))
private theorem rec6628 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(0),[9,10],[42],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[96]? = some (⟨129,(0),[9,10],[42],500⟩) from rfl))
private theorem rec6631 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(1),[9,10],[42],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[99]? = some (⟨129,(1),[9,10],[42],501⟩) from rfl))
private theorem rec6634 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(2),[9,10],[42],502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[102]? = some (⟨129,(2),[9,10],[42],502⟩) from rfl))
private theorem rec6637 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(3),[9,10],[42],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[105]? = some (⟨129,(3),[9,10],[42],503⟩) from rfl))
private theorem rec6640 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(4),[9,10],[42],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[108]? = some (⟨129,(4),[9,10],[42],500⟩) from rfl))
private theorem rec6643 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(5),[9,10],[42],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[111]? = some (⟨129,(5),[9,10],[42],501⟩) from rfl))
private theorem rec6646 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(6),[9,10],[42],504⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[114]? = some (⟨129,(6),[9,10],[42],504⟩) from rfl))
private theorem rec6649 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(7),[9,10],[42],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[117]? = some (⟨129,(7),[9,10],[42],503⟩) from rfl))
private theorem rec6652 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(8),[9,10],[42],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[120]? = some (⟨129,(8),[9,10],[42],500⟩) from rfl))
private theorem rec6655 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(9),[9,10],[42],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[123]? = some (⟨129,(9),[9,10],[42],501⟩) from rfl))
private theorem rec6658 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(10),[9,10],[42],502⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[126]? = some (⟨129,(10),[9,10],[42],502⟩) from rfl))
private theorem rec6661 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(11),[9,10],[42],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[129]? = some (⟨129,(11),[9,10],[42],503⟩) from rfl))
private theorem rec6664 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(12),[9,10],[42],500⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[132]? = some (⟨129,(12),[9,10],[42],500⟩) from rfl))
private theorem rec6667 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(13),[9,10],[42],501⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[135]? = some (⟨129,(13),[9,10],[42],501⟩) from rfl))
private theorem rec6670 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(14),[9,10],[42],505⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[138]? = some (⟨129,(14),[9,10],[42],505⟩) from rfl))
private theorem rec6673 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 129 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨129,(15),[9,10],[42],503⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[141]? = some (⟨129,(15),[9,10],[42],503⟩) from rfl))
private theorem rec6676 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 132 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(0),[9,10],[42],506⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[144]? = some (⟨132,(0),[9,10],[42],506⟩) from rfl))
private theorem rec6679 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 132 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(1),[9,10],[42],507⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[147]? = some (⟨132,(1),[9,10],[42],507⟩) from rfl))
private theorem rec6682 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 132 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(2),[9,10],[42],508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[150]? = some (⟨132,(2),[9,10],[42],508⟩) from rfl))
private theorem rec6685 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 132 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨132,(3),[9,10],[42],509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[153]? = some (⟨132,(3),[9,10],[42],509⟩) from rfl))
private theorem rec6689 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(0),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[157]? = some (⟨134,(0),[9,10],[42],3⟩) from rfl))
private theorem rec6692 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(1),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[160]? = some (⟨134,(1),[9,10],[42],3⟩) from rfl))
private theorem rec6695 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(2),[9,10],[42],510⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[163]? = some (⟨134,(2),[9,10],[42],510⟩) from rfl))
private theorem rec6698 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(3),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[166]? = some (⟨134,(3),[9,10],[42],29⟩) from rfl))
private theorem rec6701 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(4),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[169]? = some (⟨134,(4),[9,10],[42],3⟩) from rfl))
private theorem rec6704 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(5),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[172]? = some (⟨134,(5),[9,10],[42],3⟩) from rfl))
private theorem rec6707 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(6),[9,10],[42],511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[175]? = some (⟨134,(6),[9,10],[42],511⟩) from rfl))
private theorem rec6710 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(7),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[178]? = some (⟨134,(7),[9,10],[42],29⟩) from rfl))
private theorem rec6713 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(8),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[181]? = some (⟨134,(8),[9,10],[42],3⟩) from rfl))
private theorem rec6716 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(9),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[184]? = some (⟨134,(9),[9,10],[42],3⟩) from rfl))
private theorem rec6719 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(10),[9,10],[42],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[187]? = some (⟨134,(10),[9,10],[42],512⟩) from rfl))
private theorem rec6722 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(11),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[190]? = some (⟨134,(11),[9,10],[42],29⟩) from rfl))
private theorem rec6725 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(12),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[193]? = some (⟨134,(12),[9,10],[42],3⟩) from rfl))
private theorem rec6728 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(13),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[196]? = some (⟨134,(13),[9,10],[42],3⟩) from rfl))
private theorem rec6731 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(14),[9,10],[42],513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[199]? = some (⟨134,(14),[9,10],[42],513⟩) from rfl))
private theorem rec6734 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(15),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[202]? = some (⟨134,(15),[9,10],[42],29⟩) from rfl))
private theorem rec6737 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(16),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[205]? = some (⟨134,(16),[9,10],[42],3⟩) from rfl))
private theorem rec6740 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(17),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[208]? = some (⟨134,(17),[9,10],[42],3⟩) from rfl))
private theorem rec6743 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(18),[9,10],[42],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[211]? = some (⟨134,(18),[9,10],[42],514⟩) from rfl))
private theorem rec6746 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 134 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨134,(19),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[214]? = some (⟨134,(19),[9,10],[42],29⟩) from rfl))
private theorem rec6749 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(0),[9,10],[42],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[217]? = some (⟨135,(0),[9,10],[42],515⟩) from rfl))
private theorem rec6752 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(1),[9,10],[42],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[220]? = some (⟨135,(1),[9,10],[42],515⟩) from rfl))
private theorem rec6755 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(2),[9,10],[42],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[223]? = some (⟨135,(2),[9,10],[42],516⟩) from rfl))
private theorem rec6758 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(3),[9,10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[226]? = some (⟨135,(3),[9,10],[42],517⟩) from rfl))
private theorem rec6761 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(4),[9,10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[229]? = some (⟨135,(4),[9,10],[42],518⟩) from rfl))
private theorem rec6764 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(5),[9,10],[42],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[232]? = some (⟨135,(5),[9,10],[42],515⟩) from rfl))
private theorem rec6767 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(6),[9,10],[42],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[235]? = some (⟨135,(6),[9,10],[42],515⟩) from rfl))
private theorem rec6770 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(7),[9,10],[42],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[238]? = some (⟨135,(7),[9,10],[42],516⟩) from rfl))
private theorem rec6773 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(8),[9,10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[241]? = some (⟨135,(8),[9,10],[42],517⟩) from rfl))
private theorem rec6776 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(9),[9,10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[244]? = some (⟨135,(9),[9,10],[42],518⟩) from rfl))
private theorem rec6779 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(10),[9,10],[42],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[247]? = some (⟨135,(10),[9,10],[42],519⟩) from rfl))
private theorem rec6782 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(11),[9,10],[42],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[250]? = some (⟨135,(11),[9,10],[42],519⟩) from rfl))
private theorem rec6785 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(12),[9,10],[42],520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[253]? = some (⟨135,(12),[9,10],[42],520⟩) from rfl))
private theorem rec6788 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(13),[9,10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[256]? = some (⟨135,(13),[9,10],[42],517⟩) from rfl))
private theorem rec6791 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(14),[9,10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[259]? = some (⟨135,(14),[9,10],[42],518⟩) from rfl))
private theorem rec6794 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(15),[9,10],[42],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[262]? = some (⟨135,(15),[9,10],[42],521⟩) from rfl))
private theorem rec6797 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(16),[9,10],[42],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[265]? = some (⟨135,(16),[9,10],[42],521⟩) from rfl))
private theorem rec6800 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(17),[9,10],[42],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[268]? = some (⟨135,(17),[9,10],[42],521⟩) from rfl))
private theorem rec6804 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(18),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[272]? = some (⟨135,(18),[10],[42],517⟩) from rfl))
private theorem rec6808 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(19),[9,10],[42],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[276]? = some (⟨135,(19),[9,10],[42],521⟩) from rfl))
private theorem rec6811 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(20),[9,10],[42],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[279]? = some (⟨135,(20),[9,10],[42],522⟩) from rfl))
private theorem rec6814 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(21),[9,10],[42],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[282]? = some (⟨135,(21),[9,10],[42],522⟩) from rfl))
private theorem rec6817 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(22),[9,10],[42],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[285]? = some (⟨135,(22),[9,10],[42],522⟩) from rfl))
private theorem rec6820 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(23),[9,10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[288]? = some (⟨135,(23),[9,10],[42],517⟩) from rfl))
private theorem rec6825 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 135 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨135,(24),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[293]? = some (⟨135,(24),[10],[42],518⟩) from rfl))
private theorem rec6829 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(0),[9,10],[42],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[297]? = some (⟨136,(0),[9,10],[42],524⟩) from rfl))
private theorem rec6832 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(1),[9,10],[42],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[300]? = some (⟨136,(1),[9,10],[42],524⟩) from rfl))
private theorem rec6835 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(2),[9,10],[42],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[303]? = some (⟨136,(2),[9,10],[42],524⟩) from rfl))
private theorem rec6838 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(3),[9,10],[42],524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[306]? = some (⟨136,(3),[9,10],[42],524⟩) from rfl))
private theorem rec6841 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(4),[9,10],[42],525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[309]? = some (⟨136,(4),[9,10],[42],525⟩) from rfl))
private theorem rec6844 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(5),[9,10],[42],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[312]? = some (⟨136,(5),[9,10],[42],523⟩) from rfl))
private theorem rec6848 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(6),[9,10],[42],527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[316]? = some (⟨136,(6),[9,10],[42],527⟩) from rfl))
private theorem rec6851 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(7),[9,10],[42],527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[319]? = some (⟨136,(7),[9,10],[42],527⟩) from rfl))
private theorem rec6854 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(8),[9,10],[42],527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[322]? = some (⟨136,(8),[9,10],[42],527⟩) from rfl))
private theorem rec6857 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(9),[9,10],[42],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[325]? = some (⟨136,(9),[9,10],[42],528⟩) from rfl))
private theorem rec6860 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(10),[9,10],[42],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[328]? = some (⟨136,(10),[9,10],[42],523⟩) from rfl))
private theorem rec6863 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(11),[9,10],[42],526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[331]? = some (⟨136,(11),[9,10],[42],526⟩) from rfl))
private theorem rec6866 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(12),[9,10],[42],529⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[334]? = some (⟨136,(12),[9,10],[42],529⟩) from rfl))
private theorem rec6869 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(13),[9,10],[42],530⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[337]? = some (⟨136,(13),[9,10],[42],530⟩) from rfl))
private theorem rec6872 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(14),[9,10],[42],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[340]? = some (⟨136,(14),[9,10],[42],531⟩) from rfl))
private theorem rec6875 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(15),[9,10],[42],523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[343]? = some (⟨136,(15),[9,10],[42],523⟩) from rfl))
private theorem rec6878 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(16),[9,10],[42],526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[346]? = some (⟨136,(16),[9,10],[42],526⟩) from rfl))
private theorem rec6881 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(17),[9,10],[42],532⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[349]? = some (⟨136,(17),[9,10],[42],532⟩) from rfl))
private theorem rec6884 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(18),[9,10],[42],533⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[352]? = some (⟨136,(18),[9,10],[42],533⟩) from rfl))
private theorem rec6887 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(19),[9,10],[42],534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[355]? = some (⟨136,(19),[9,10],[42],534⟩) from rfl))
private theorem rec6890 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(20),[9,10],[42],535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[358]? = some (⟨136,(20),[9,10],[42],535⟩) from rfl))
private theorem rec6893 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(21),[9,10],[42],536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[361]? = some (⟨136,(21),[9,10],[42],536⟩) from rfl))
private theorem rec6896 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(22),[9,10],[42],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[364]? = some (⟨136,(22),[9,10],[42],537⟩) from rfl))
private theorem rec6899 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(23),[9,10],[42],538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[367]? = some (⟨136,(23),[9,10],[42],538⟩) from rfl))
private theorem rec6903 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 136 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨136,(24),[9,10],[42],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[371]? = some (⟨136,(24),[9,10],[42],531⟩) from rfl))
private theorem rec6906 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(0),[9,10],[42],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[374]? = some (⟨138,(0),[9,10],[42],539⟩) from rfl))
private theorem rec6909 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(1),[9,10],[42],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[377]? = some (⟨138,(1),[9,10],[42],539⟩) from rfl))
private theorem rec6912 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(2),[9,10],[42],540⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[380]? = some (⟨138,(2),[9,10],[42],540⟩) from rfl))
private theorem rec6915 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(3),[9,10],[42],541⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[383]? = some (⟨138,(3),[9,10],[42],541⟩) from rfl))
private theorem rec6918 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(4),[9,10],[42],542⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[386]? = some (⟨138,(4),[9,10],[42],542⟩) from rfl))
private theorem rec6922 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(5),[9,10],[42],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[390]? = some (⟨138,(5),[9,10],[42],543⟩) from rfl))
private theorem rec6926 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(6),[9,10],[42],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[394]? = some (⟨138,(6),[9,10],[42],543⟩) from rfl))
private theorem rec6930 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(7),[9,10],[42],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[398]? = some (⟨138,(7),[9,10],[42],544⟩) from rfl))
private theorem rec6934 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(8),[9,10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[402]? = some (⟨138,(8),[9,10],[42],517⟩) from rfl))
private theorem rec6938 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(9),[9,10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[406]? = some (⟨138,(9),[9,10],[42],518⟩) from rfl))
private theorem rec6941 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(10),[9,10],[42],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[409]? = some (⟨138,(10),[9,10],[42],545⟩) from rfl))
private theorem rec6944 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(11),[9,10],[42],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[412]? = some (⟨138,(11),[9,10],[42],545⟩) from rfl))
private theorem rec6947 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(12),[9,10],[42],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[415]? = some (⟨138,(12),[9,10],[42],544⟩) from rfl))
private theorem rec6950 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(13),[9,10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[418]? = some (⟨138,(13),[9,10],[42],517⟩) from rfl))
private theorem rec6953 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(14),[9,10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[421]? = some (⟨138,(14),[9,10],[42],518⟩) from rfl))
private theorem rec6956 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(15),[9,10],[42],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[424]? = some (⟨138,(15),[9,10],[42],546⟩) from rfl))
private theorem rec6959 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(16),[9,10],[42],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[427]? = some (⟨138,(16),[9,10],[42],546⟩) from rfl))
private theorem rec6962 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(17),[9,10],[42],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[430]? = some (⟨138,(17),[9,10],[42],544⟩) from rfl))
private theorem rec6965 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(18),[9,10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[433]? = some (⟨138,(18),[9,10],[42],517⟩) from rfl))
private theorem rec6968 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(19),[9,10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[436]? = some (⟨138,(19),[9,10],[42],518⟩) from rfl))
private theorem rec6971 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(20),[9,10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[439]? = some (⟨138,(20),[9,10],[42],547⟩) from rfl))
private theorem rec6974 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(21),[9,10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[442]? = some (⟨138,(21),[9,10],[42],547⟩) from rfl))
private theorem rec6977 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(22),[9,10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[445]? = some (⟨138,(22),[9,10],[42],547⟩) from rfl))
private theorem rec6980 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(23),[9,10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[448]? = some (⟨138,(23),[9,10],[42],517⟩) from rfl))
private theorem rec6983 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 138 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨138,(24),[9,10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[451]? = some (⟨138,(24),[9,10],[42],518⟩) from rfl))
private theorem rec6986 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(0),[9,10],[42],548⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[454]? = some (⟨139,(0),[9,10],[42],548⟩) from rfl))
private theorem rec6989 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(1),[9,10],[42],549⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[457]? = some (⟨139,(1),[9,10],[42],549⟩) from rfl))
private theorem rec6992 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(2),[9,10],[42],548⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[460]? = some (⟨139,(2),[9,10],[42],548⟩) from rfl))
private theorem rec6995 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(3),[9,10],[42],550⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[463]? = some (⟨139,(3),[9,10],[42],550⟩) from rfl))
private theorem rec6998 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(4),[9,10],[42],551⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[466]? = some (⟨139,(4),[9,10],[42],551⟩) from rfl))
private theorem rec7002 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(5),[9,10],[42],552⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[470]? = some (⟨139,(5),[9,10],[42],552⟩) from rfl))
private theorem rec7006 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(6),[9,10],[42],553⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[474]? = some (⟨139,(6),[9,10],[42],553⟩) from rfl))
private theorem rec7010 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(7),[9,10],[42],554⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[478]? = some (⟨139,(7),[9,10],[42],554⟩) from rfl))
private theorem rec7013 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(8),[9,10],[42],555⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[481]? = some (⟨139,(8),[9,10],[42],555⟩) from rfl))
private theorem rec7016 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(9),[9,10],[42],556⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[484]? = some (⟨139,(9),[9,10],[42],556⟩) from rfl))
private theorem rec7019 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(10),[9,10],[42],557⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[487]? = some (⟨139,(10),[9,10],[42],557⟩) from rfl))
private theorem rec7022 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(11),[9,10],[42],558⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[490]? = some (⟨139,(11),[9,10],[42],558⟩) from rfl))
private theorem rec7025 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(12),[9,10],[42],559⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[493]? = some (⟨139,(12),[9,10],[42],559⟩) from rfl))
private theorem rec7028 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(13),[9,10],[42],560⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[496]? = some (⟨139,(13),[9,10],[42],560⟩) from rfl))
private theorem rec7031 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(14),[9,10],[42],561⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[499]? = some (⟨139,(14),[9,10],[42],561⟩) from rfl))
private theorem rec7034 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(15),[9,10],[42],562⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[502]? = some (⟨139,(15),[9,10],[42],562⟩) from rfl))
private theorem rec7037 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(16),[9,10],[42],555⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[505]? = some (⟨139,(16),[9,10],[42],555⟩) from rfl))
private theorem rec7040 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(17),[9,10],[42],556⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[508]? = some (⟨139,(17),[9,10],[42],556⟩) from rfl))
private theorem rec7043 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(18),[9,10],[42],557⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[511]? = some (⟨139,(18),[9,10],[42],557⟩) from rfl))
private theorem rec7046 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 139 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨139,(19),[9,10],[42],558⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[514]? = some (⟨139,(19),[9,10],[42],558⟩) from rfl))
private theorem rec7049 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 140 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(0),[9,10],[42],563⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[517]? = some (⟨140,(0),[9,10],[42],563⟩) from rfl))
private theorem rec7052 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 140 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(1),[9,10],[42],564⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[520]? = some (⟨140,(1),[9,10],[42],564⟩) from rfl))
private theorem rec7055 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 140 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(2),[9,10],[42],565⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[523]? = some (⟨140,(2),[9,10],[42],565⟩) from rfl))
private theorem rec7060 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 140 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(3),[10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[528]? = some (⟨140,(3),[10],[42],547⟩) from rfl))
private theorem rec7063 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 140 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(4),[9,10],[42],566⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[531]? = some (⟨140,(4),[9,10],[42],566⟩) from rfl))
private theorem rec7066 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 140 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(5),[9,10],[42],564⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[534]? = some (⟨140,(5),[9,10],[42],564⟩) from rfl))
private theorem rec7071 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 140 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(6),[10],[42],567⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[539]? = some (⟨140,(6),[10],[42],567⟩) from rfl))
private theorem rec7075 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 140 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨140,(7),[9,10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[543]? = some (⟨140,(7),[9,10],[42],547⟩) from rfl))
private theorem rec7078 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(0),[9,10],[42],568⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[546]? = some (⟨142,(0),[9,10],[42],568⟩) from rfl))
private theorem rec7081 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(1),[9,10],[42],569⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[549]? = some (⟨142,(1),[9,10],[42],569⟩) from rfl))
private theorem rec7084 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(2),[9,10],[42],570⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[552]? = some (⟨142,(2),[9,10],[42],570⟩) from rfl))
private theorem rec7087 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(3),[9,10],[42],571⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[555]? = some (⟨142,(3),[9,10],[42],571⟩) from rfl))
private theorem rec7090 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(4),[9,10],[42],572⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[558]? = some (⟨142,(4),[9,10],[42],572⟩) from rfl))
private theorem rec7093 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(5),[9,10],[42],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[561]? = some (⟨142,(5),[9,10],[42],573⟩) from rfl))
private theorem rec7096 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(6),[9,10],[42],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[564]? = some (⟨142,(6),[9,10],[42],573⟩) from rfl))
private theorem rec7099 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(7),[9,10],[42],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[567]? = some (⟨142,(7),[9,10],[42],573⟩) from rfl))
private theorem rec7102 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(8),[9,10],[42],574⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[570]? = some (⟨142,(8),[9,10],[42],574⟩) from rfl))
private theorem rec7105 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(9),[9,10],[42],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[573]? = some (⟨142,(9),[9,10],[42],575⟩) from rfl))
private theorem rec7108 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(10),[9,10],[42],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[576]? = some (⟨142,(10),[9,10],[42],575⟩) from rfl))
private theorem rec7111 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(11),[9,10],[42],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[579]? = some (⟨142,(11),[9,10],[42],575⟩) from rfl))
private theorem rec7114 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(12),[9,10],[42],576⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[582]? = some (⟨142,(12),[9,10],[42],576⟩) from rfl))
private theorem rec7117 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(13),[9,10],[42],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[585]? = some (⟨142,(13),[9,10],[42],577⟩) from rfl))
private theorem rec7120 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(14),[9,10],[42],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[588]? = some (⟨142,(14),[9,10],[42],577⟩) from rfl))
private theorem rec7123 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 142 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨142,(15),[9,10],[42],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[591]? = some (⟨142,(15),[9,10],[42],577⟩) from rfl))
private theorem rec7126 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(0),[9,10],[42],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[594]? = some (⟨143,(0),[9,10],[42],578⟩) from rfl))
private theorem rec7129 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(1),[9,10],[42],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[597]? = some (⟨143,(1),[9,10],[42],579⟩) from rfl))
private theorem rec7132 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(2),[9,10],[42],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[600]? = some (⟨143,(2),[9,10],[42],580⟩) from rfl))
private theorem rec7135 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(3),[9,10],[42],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[603]? = some (⟨143,(3),[9,10],[42],581⟩) from rfl))
private theorem rec7138 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(4),[9,10],[42],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[606]? = some (⟨143,(4),[9,10],[42],582⟩) from rfl))
private theorem rec7141 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(5),[9,10],[42],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[609]? = some (⟨143,(5),[9,10],[42],583⟩) from rfl))
private theorem rec7144 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(6),[9,10],[42],584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[612]? = some (⟨143,(6),[9,10],[42],584⟩) from rfl))
private theorem rec7147 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(7),[9,10],[42],585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[615]? = some (⟨143,(7),[9,10],[42],585⟩) from rfl))
private theorem rec7150 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(8),[9,10],[42],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[618]? = some (⟨143,(8),[9,10],[42],578⟩) from rfl))
private theorem rec7153 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(9),[9,10],[42],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[621]? = some (⟨143,(9),[9,10],[42],579⟩) from rfl))
private theorem rec7156 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(10),[9,10],[42],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[624]? = some (⟨143,(10),[9,10],[42],580⟩) from rfl))
private theorem rec7159 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(11),[9,10],[42],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[627]? = some (⟨143,(11),[9,10],[42],581⟩) from rfl))
private theorem rec7162 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(12),[9,10],[42],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[630]? = some (⟨143,(12),[9,10],[42],586⟩) from rfl))
private theorem rec7165 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(13),[9,10],[42],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[633]? = some (⟨143,(13),[9,10],[42],587⟩) from rfl))
private theorem rec7168 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(14),[9,10],[42],588⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[636]? = some (⟨143,(14),[9,10],[42],588⟩) from rfl))
private theorem rec7171 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 143 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨143,(15),[9,10],[42],589⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[639]? = some (⟨143,(15),[9,10],[42],589⟩) from rfl))
private theorem rec7174 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 144 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(0),[9,10],[42],590⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[642]? = some (⟨144,(0),[9,10],[42],590⟩) from rfl))
private theorem rec7177 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 144 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(1),[9,10],[42],591⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[645]? = some (⟨144,(1),[9,10],[42],591⟩) from rfl))
private theorem rec7180 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 144 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(2),[9,10],[42],590⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[648]? = some (⟨144,(2),[9,10],[42],590⟩) from rfl))
private theorem rec7183 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 144 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨144,(3),[9,10],[42],592⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[651]? = some (⟨144,(3),[9,10],[42],592⟩) from rfl))
private theorem rec7186 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(0),[9,10],[42],593⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[654]? = some (⟨145,(0),[9,10],[42],593⟩) from rfl))
private theorem rec7189 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(1),[9,10],[42],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[657]? = some (⟨145,(1),[9,10],[42],594⟩) from rfl))
private theorem rec7193 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(2),[9,10],[42],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[661]? = some (⟨145,(2),[9,10],[42],595⟩) from rfl))
private theorem rec7197 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(3),[10],[42],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[665]? = some (⟨145,(3),[10],[42],596⟩) from rfl))
private theorem rec7200 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(4),[9,10],[42],597⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[668]? = some (⟨145,(4),[9,10],[42],597⟩) from rfl))
private theorem rec7203 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(5),[9,10],[42],598⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[671]? = some (⟨145,(5),[9,10],[42],598⟩) from rfl))
private theorem rec7206 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(6),[9,10],[42],599⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[674]? = some (⟨145,(6),[9,10],[42],599⟩) from rfl))
private theorem rec7209 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(7),[9,10],[42],600⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[677]? = some (⟨145,(7),[9,10],[42],600⟩) from rfl))
private theorem rec7212 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(8),[9,10],[42],593⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[680]? = some (⟨145,(8),[9,10],[42],593⟩) from rfl))
private theorem rec7215 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(9),[9,10],[42],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[683]? = some (⟨145,(9),[9,10],[42],594⟩) from rfl))
private theorem rec7218 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(10),[9,10],[42],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[686]? = some (⟨145,(10),[9,10],[42],595⟩) from rfl))
private theorem rec7221 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(11),[9,10],[42],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[689]? = some (⟨145,(11),[9,10],[42],596⟩) from rfl))
private theorem rec7224 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(12),[9,10],[42],601⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[692]? = some (⟨145,(12),[9,10],[42],601⟩) from rfl))
private theorem rec7227 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(13),[9,10],[42],602⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[695]? = some (⟨145,(13),[9,10],[42],602⟩) from rfl))
private theorem rec7230 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(14),[9,10],[42],603⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[698]? = some (⟨145,(14),[9,10],[42],603⟩) from rfl))
private theorem rec7233 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 145 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨145,(15),[9,10],[42],604⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[701]? = some (⟨145,(15),[9,10],[42],604⟩) from rfl))
private theorem rec7237 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(0),[10],[42],605⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[705]? = some (⟨146,(0),[10],[42],605⟩) from rfl))
private theorem rec7241 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(1),[10],[42],606⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[709]? = some (⟨146,(1),[10],[42],606⟩) from rfl))
private theorem rec7244 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(2),[9,10],[42],607⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[712]? = some (⟨146,(2),[9,10],[42],607⟩) from rfl))
private theorem rec7248 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(3),[10],[42],608⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[716]? = some (⟨146,(3),[10],[42],608⟩) from rfl))
private theorem rec7251 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(4),[9,10],[42],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[719]? = some (⟨146,(4),[9,10],[42],609⟩) from rfl))
private theorem rec7254 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(5),[9,10],[42],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[722]? = some (⟨146,(5),[9,10],[42],610⟩) from rfl))
private theorem rec7257 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(6),[9,10],[42],611⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[725]? = some (⟨146,(6),[9,10],[42],611⟩) from rfl))
private theorem rec7260 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(7),[9,10],[42],612⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[728]? = some (⟨146,(7),[9,10],[42],612⟩) from rfl))
private theorem rec7263 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(8),[9,10],[42],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[731]? = some (⟨146,(8),[9,10],[42],613⟩) from rfl))
private theorem rec7266 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(9),[9,10],[42],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[734]? = some (⟨146,(9),[9,10],[42],614⟩) from rfl))
private theorem rec7269 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(10),[9,10],[42],615⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[737]? = some (⟨146,(10),[9,10],[42],615⟩) from rfl))
private theorem rec7272 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(11),[9,10],[42],616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[740]? = some (⟨146,(11),[9,10],[42],616⟩) from rfl))
private theorem rec7275 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(12),[9,10],[42],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[743]? = some (⟨146,(12),[9,10],[42],617⟩) from rfl))
private theorem rec7278 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(13),[9,10],[42],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[746]? = some (⟨146,(13),[9,10],[42],618⟩) from rfl))
private theorem rec7281 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(14),[9,10],[42],619⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[749]? = some (⟨146,(14),[9,10],[42],619⟩) from rfl))
private theorem rec7284 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 146 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨146,(15),[9,10],[42],620⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[752]? = some (⟨146,(15),[9,10],[42],620⟩) from rfl))
private theorem rec7287 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(0),[9,10],[42],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[755]? = some (⟨150,(0),[9,10],[42],387⟩) from rfl))
private theorem rec7290 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(1),[9,10],[42],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[758]? = some (⟨150,(1),[9,10],[42],621⟩) from rfl))
private theorem rec7293 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(2),[9,10],[42],622⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[761]? = some (⟨150,(2),[9,10],[42],622⟩) from rfl))
private theorem rec7296 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(3),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[764]? = some (⟨150,(3),[9,10],[42],101⟩) from rfl))
private theorem rec7299 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(4),[9,10],[42],622⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[767]? = some (⟨150,(4),[9,10],[42],622⟩) from rfl))
private theorem rec7302 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(5),[9,10],[42],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[770]? = some (⟨150,(5),[9,10],[42],387⟩) from rfl))
private theorem rec7305 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(6),[9,10],[42],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[773]? = some (⟨150,(6),[9,10],[42],621⟩) from rfl))
private theorem rec7308 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(7),[9,10],[42],623⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[776]? = some (⟨150,(7),[9,10],[42],623⟩) from rfl))
private theorem rec7311 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(8),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[779]? = some (⟨150,(8),[9,10],[42],101⟩) from rfl))
private theorem rec7314 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(9),[9,10],[42],623⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[782]? = some (⟨150,(9),[9,10],[42],623⟩) from rfl))
private theorem rec7317 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(10),[9,10],[42],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[785]? = some (⟨150,(10),[9,10],[42],387⟩) from rfl))
private theorem rec7320 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(11),[9,10],[42],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[788]? = some (⟨150,(11),[9,10],[42],621⟩) from rfl))
private theorem rec7323 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(12),[9,10],[42],624⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[791]? = some (⟨150,(12),[9,10],[42],624⟩) from rfl))
private theorem rec7326 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(13),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[794]? = some (⟨150,(13),[9,10],[42],101⟩) from rfl))
private theorem rec7329 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(14),[9,10],[42],624⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[797]? = some (⟨150,(14),[9,10],[42],624⟩) from rfl))
private theorem rec7332 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(15),[9,10],[42],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[800]? = some (⟨150,(15),[9,10],[42],625⟩) from rfl))
private theorem rec7335 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(16),[9,10],[42],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[803]? = some (⟨150,(16),[9,10],[42],626⟩) from rfl))
private theorem rec7338 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(17),[9,10],[42],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[806]? = some (⟨150,(17),[9,10],[42],286⟩) from rfl))
private theorem rec7341 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(18),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[809]? = some (⟨150,(18),[9,10],[42],101⟩) from rfl))
private theorem rec7344 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(19),[9,10],[42],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[812]? = some (⟨150,(19),[9,10],[42],286⟩) from rfl))
private theorem rec7347 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(20),[9,10],[42],387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[815]? = some (⟨150,(20),[9,10],[42],387⟩) from rfl))
private theorem rec7350 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(21),[9,10],[42],621⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[818]? = some (⟨150,(21),[9,10],[42],621⟩) from rfl))
private theorem rec7353 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(22),[9,10],[42],627⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[821]? = some (⟨150,(22),[9,10],[42],627⟩) from rfl))
private theorem rec7356 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(23),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[824]? = some (⟨150,(23),[9,10],[42],101⟩) from rfl))
private theorem rec7359 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 150 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨150,(24),[9,10],[42],627⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[827]? = some (⟨150,(24),[9,10],[42],627⟩) from rfl))
private theorem rec16414 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(0),[9,10],[42],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[206]? = some (⟨562,(0),[9,10],[42],1649⟩) from rfl))
private theorem rec16416 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(1),[9,10],[42],1666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[208]? = some (⟨562,(1),[9,10],[42],1666⟩) from rfl))
private theorem rec16418 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(2),[9,10],[42],1667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[210]? = some (⟨562,(2),[9,10],[42],1667⟩) from rfl))
private theorem rec16420 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(3),[9,10],[42],1668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[212]? = some (⟨562,(3),[9,10],[42],1668⟩) from rfl))
private theorem rec16422 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(4),[9,10],[42],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[214]? = some (⟨562,(4),[9,10],[42],396⟩) from rfl))
private theorem rec16424 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(5),[9,10],[42],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[216]? = some (⟨562,(5),[9,10],[42],1649⟩) from rfl))
private theorem rec16426 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(6),[9,10],[42],1666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[218]? = some (⟨562,(6),[9,10],[42],1666⟩) from rfl))
private theorem rec16428 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(7),[9,10],[42],1667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[220]? = some (⟨562,(7),[9,10],[42],1667⟩) from rfl))
private theorem rec16430 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(8),[9,10],[42],1668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[222]? = some (⟨562,(8),[9,10],[42],1668⟩) from rfl))
private theorem rec16432 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 562 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨562,(9),[9,10],[42],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[224]? = some (⟨562,(9),[9,10],[42],396⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 4).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 32).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 10).plans.drop 4).take 1 = [⟨5,82,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(561,⟨([1],[]),true,([1],[]),false,false,[]⟩),(84,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(85,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(562,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(563,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(88,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(89,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(90,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(91,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(92,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(93,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(94,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(95,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(96,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(97,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(98,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(99,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(100,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(101,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(102,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(103,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(104,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(105,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(106,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(107,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(108,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(109,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(110,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(111,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(112,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(113,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(114,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(115,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(116,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(117,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(118,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(119,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(120,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(121,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(122,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(123,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(124,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(125,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(126,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(127,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(128,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(129,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(130,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(131,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(132,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(564,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(134,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(135,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(136,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(137,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(138,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(139,⟨([3,2],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(140,⟨([3,1,1],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(141,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(142,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(143,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(144,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(145,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(146,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(565,⟨([1],[]),true,([],[]),true,false,[]⟩),(152,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec5604 10 32 (by decide) (by decide)
  · left
    exact rec5604 10 33 (by decide) (by decide)
  · left
    exact rec5608 10 34 (by decide) (by decide)
  · left
    exact rec5609 10 35 (by decide) (by decide)
  · left
    exact rec5604 10 36 (by decide) (by decide)
  · left
    exact rec5604 10 37 (by decide) (by decide)
  · left
    exact rec5610 10 38 (by decide) (by decide)
  · left
    exact rec5609 10 39 (by decide) (by decide)
  · left
    exact rec5604 10 40 (by decide) (by decide)
  · left
    exact rec5604 10 41 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(561,⟨([1],[]),true,([1],[]),false,false,[]⟩),(84,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(85,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(562,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(563,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(88,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(89,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(90,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(91,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(92,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(93,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(94,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(95,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(96,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(97,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(98,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(99,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(100,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(101,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(102,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(103,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(104,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(105,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(106,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(107,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(108,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(109,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(110,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(111,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(112,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(113,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(114,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(115,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(116,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(117,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(118,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(119,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(120,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(121,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(122,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(123,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(124,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(125,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(126,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(127,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(128,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(129,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(130,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(131,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(132,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(564,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(134,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(135,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(136,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(137,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(138,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(139,⟨([3,2],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(140,⟨([3,1,1],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(141,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(142,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(143,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(144,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(145,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(146,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(565,⟨([1],[]),true,([],[]),true,false,[]⟩),(152,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 561)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 84)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5619 10 42 (by decide) (by decide)
      · right
        exact rec5621 10 42 (by decide) (by decide)
      · right
        exact rec5623 10 42 (by decide) (by decide)
      · right
        exact rec5625 10 42 (by decide) (by decide)
      · right
        exact rec5627 10 42 (by decide) (by decide)
      · right
        exact rec5629 10 42 (by decide) (by decide)
      · right
        exact rec5631 10 42 (by decide) (by decide)
      · right
        exact rec5633 10 42 (by decide) (by decide)
      · right
        exact rec5635 10 42 (by decide) (by decide)
      · right
        exact rec5637 10 42 (by decide) (by decide)
      · right
        exact rec5639 10 42 (by decide) (by decide)
      · right
        exact rec5641 10 42 (by decide) (by decide)
      · right
        exact rec5643 10 42 (by decide) (by decide)
      · right
        exact rec5645 10 42 (by decide) (by decide)
      · right
        exact rec5647 10 42 (by decide) (by decide)
      · right
        exact rec5649 10 42 (by decide) (by decide)
      · right
        exact rec5651 10 42 (by decide) (by decide)
      · right
        exact rec5653 10 42 (by decide) (by decide)
      · right
        exact rec5655 10 42 (by decide) (by decide)
      · right
        exact rec5657 10 42 (by decide) (by decide)
      · right
        exact rec5659 10 42 (by decide) (by decide)
      · right
        exact rec5661 10 42 (by decide) (by decide)
      · right
        exact rec5663 10 42 (by decide) (by decide)
      · right
        exact rec5665 10 42 (by decide) (by decide)
      · right
        exact rec5667 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 85)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 562)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16414 10 42 (by decide) (by decide)
      · right
        exact rec16416 10 42 (by decide) (by decide)
      · right
        exact rec16418 10 42 (by decide) (by decide)
      · right
        exact rec16420 10 42 (by decide) (by decide)
      · right
        exact rec16422 10 42 (by decide) (by decide)
      · right
        exact rec16424 10 42 (by decide) (by decide)
      · right
        exact rec16426 10 42 (by decide) (by decide)
      · right
        exact rec16428 10 42 (by decide) (by decide)
      · right
        exact rec16430 10 42 (by decide) (by decide)
      · right
        exact rec16432 10 42 (by decide) (by decide)
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
        exact rec5720 10 42 (by decide) (by decide)
      · right
        exact rec5723 10 42 (by decide) (by decide)
      · right
        exact rec5726 10 42 (by decide) (by decide)
      · right
        exact rec5729 10 42 (by decide) (by decide)
      · right
        exact rec5732 10 42 (by decide) (by decide)
      · right
        exact rec5735 10 42 (by decide) (by decide)
      · right
        exact rec5738 10 42 (by decide) (by decide)
      · right
        exact rec5741 10 42 (by decide) (by decide)
      · right
        exact rec5744 10 42 (by decide) (by decide)
      · right
        exact rec5747 10 42 (by decide) (by decide)
      · right
        exact rec5750 10 42 (by decide) (by decide)
      · right
        exact rec5753 10 42 (by decide) (by decide)
      · right
        exact rec5756 10 42 (by decide) (by decide)
      · right
        exact rec5759 10 42 (by decide) (by decide)
      · right
        exact rec5762 10 42 (by decide) (by decide)
      · right
        exact rec5765 10 42 (by decide) (by decide)
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
        exact rec5768 10 42 (by decide) (by decide)
      · right
        exact rec5771 10 42 (by decide) (by decide)
      · right
        exact rec5774 10 42 (by decide) (by decide)
      · right
        exact rec5777 10 42 (by decide) (by decide)
      · right
        exact rec5780 10 42 (by decide) (by decide)
      · right
        exact rec5783 10 42 (by decide) (by decide)
      · right
        exact rec5786 10 42 (by decide) (by decide)
      · right
        exact rec5789 10 42 (by decide) (by decide)
      · right
        exact rec5792 10 42 (by decide) (by decide)
      · right
        exact rec5795 10 42 (by decide) (by decide)
      · right
        exact rec5798 10 42 (by decide) (by decide)
      · right
        exact rec5801 10 42 (by decide) (by decide)
      · right
        exact rec5804 10 42 (by decide) (by decide)
      · right
        exact rec5807 10 42 (by decide) (by decide)
      · right
        exact rec5810 10 42 (by decide) (by decide)
      · right
        exact rec5813 10 42 (by decide) (by decide)
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
        exact rec5816 10 42 (by decide) (by decide)
      · right
        exact rec5819 10 42 (by decide) (by decide)
      · right
        exact rec5822 10 42 (by decide) (by decide)
      · right
        exact rec5825 10 42 (by decide) (by decide)
      · right
        exact rec5828 10 42 (by decide) (by decide)
      · right
        exact rec5831 10 42 (by decide) (by decide)
      · right
        exact rec5834 10 42 (by decide) (by decide)
      · right
        exact rec5837 10 42 (by decide) (by decide)
      · right
        exact rec5840 10 42 (by decide) (by decide)
      · right
        exact rec5843 10 42 (by decide) (by decide)
      · right
        exact rec5846 10 42 (by decide) (by decide)
      · right
        exact rec5849 10 42 (by decide) (by decide)
      · right
        exact rec5852 10 42 (by decide) (by decide)
      · right
        exact rec5855 10 42 (by decide) (by decide)
      · right
        exact rec5858 10 42 (by decide) (by decide)
      · right
        exact rec5861 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 96)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5864 10 42 (by decide) (by decide)
      · right
        exact rec5867 10 42 (by decide) (by decide)
      · right
        exact rec5870 10 42 (by decide) (by decide)
      · right
        exact rec5873 10 42 (by decide) (by decide)
      · right
        exact rec5876 10 42 (by decide) (by decide)
      · right
        exact rec5879 10 42 (by decide) (by decide)
      · right
        exact rec5882 10 42 (by decide) (by decide)
      · right
        exact rec5885 10 42 (by decide) (by decide)
      · right
        exact rec5888 10 42 (by decide) (by decide)
      · right
        exact rec5891 10 42 (by decide) (by decide)
      · right
        exact rec5894 10 42 (by decide) (by decide)
      · right
        exact rec5897 10 42 (by decide) (by decide)
      · right
        exact rec5900 10 42 (by decide) (by decide)
      · right
        exact rec5903 10 42 (by decide) (by decide)
      · right
        exact rec5906 10 42 (by decide) (by decide)
      · right
        exact rec5909 10 42 (by decide) (by decide)
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
        exact rec5912 10 42 (by decide) (by decide)
      · right
        exact rec5915 10 42 (by decide) (by decide)
      · right
        exact rec5918 10 42 (by decide) (by decide)
      · right
        exact rec5921 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 101)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5924 10 42 (by decide) (by decide)
      · right
        exact rec5927 10 42 (by decide) (by decide)
      · right
        exact rec5930 10 42 (by decide) (by decide)
      · right
        exact rec5933 10 42 (by decide) (by decide)
      · right
        exact rec5936 10 42 (by decide) (by decide)
      · right
        exact rec5939 10 42 (by decide) (by decide)
      · right
        exact rec5942 10 42 (by decide) (by decide)
      · right
        exact rec5945 10 42 (by decide) (by decide)
      · right
        exact rec5948 10 42 (by decide) (by decide)
      · right
        exact rec5951 10 42 (by decide) (by decide)
      · right
        exact rec5954 10 42 (by decide) (by decide)
      · right
        exact rec5957 10 42 (by decide) (by decide)
      · right
        exact rec5960 10 42 (by decide) (by decide)
      · right
        exact rec5963 10 42 (by decide) (by decide)
      · right
        exact rec5966 10 42 (by decide) (by decide)
      · right
        exact rec5969 10 42 (by decide) (by decide)
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
        exact rec5972 10 42 (by decide) (by decide)
      · right
        exact rec5975 10 42 (by decide) (by decide)
      · right
        exact rec5978 10 42 (by decide) (by decide)
      · right
        exact rec5981 10 42 (by decide) (by decide)
      · right
        exact rec5984 10 42 (by decide) (by decide)
      · right
        exact rec5987 10 42 (by decide) (by decide)
      · right
        exact rec5990 10 42 (by decide) (by decide)
      · right
        exact rec5993 10 42 (by decide) (by decide)
      · right
        exact rec5996 10 42 (by decide) (by decide)
      · right
        exact rec5999 10 42 (by decide) (by decide)
      · right
        exact rec6002 10 42 (by decide) (by decide)
      · right
        exact rec6005 10 42 (by decide) (by decide)
      · right
        exact rec6008 10 42 (by decide) (by decide)
      · right
        exact rec6011 10 42 (by decide) (by decide)
      · right
        exact rec6014 10 42 (by decide) (by decide)
      · right
        exact rec6017 10 42 (by decide) (by decide)
      · right
        exact rec6020 10 42 (by decide) (by decide)
      · right
        exact rec6023 10 42 (by decide) (by decide)
      · right
        exact rec6026 10 42 (by decide) (by decide)
      · right
        exact rec6029 10 42 (by decide) (by decide)
      · right
        exact rec6032 10 42 (by decide) (by decide)
      · right
        exact rec6035 10 42 (by decide) (by decide)
      · right
        exact rec6038 10 42 (by decide) (by decide)
      · right
        exact rec6041 10 42 (by decide) (by decide)
      · right
        exact rec6044 10 42 (by decide) (by decide)
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
        exact rec6047 10 42 (by decide) (by decide)
      · right
        exact rec6050 10 42 (by decide) (by decide)
      · right
        exact rec6053 10 42 (by decide) (by decide)
      · right
        exact rec6056 10 42 (by decide) (by decide)
      · right
        exact rec6059 10 42 (by decide) (by decide)
      · right
        exact rec6062 10 42 (by decide) (by decide)
      · right
        exact rec6065 10 42 (by decide) (by decide)
      · right
        exact rec6068 10 42 (by decide) (by decide)
      · right
        exact rec6071 10 42 (by decide) (by decide)
      · right
        exact rec6074 10 42 (by decide) (by decide)
      · right
        exact rec6077 10 42 (by decide) (by decide)
      · right
        exact rec6080 10 42 (by decide) (by decide)
      · right
        exact rec6083 10 42 (by decide) (by decide)
      · right
        exact rec6086 10 42 (by decide) (by decide)
      · right
        exact rec6089 10 42 (by decide) (by decide)
      · right
        exact rec6092 10 42 (by decide) (by decide)
      · right
        exact rec6095 10 42 (by decide) (by decide)
      · right
        exact rec6098 10 42 (by decide) (by decide)
      · right
        exact rec6101 10 42 (by decide) (by decide)
      · right
        exact rec6104 10 42 (by decide) (by decide)
      · right
        exact rec6107 10 42 (by decide) (by decide)
      · right
        exact rec6110 10 42 (by decide) (by decide)
      · right
        exact rec6113 10 42 (by decide) (by decide)
      · right
        exact rec6116 10 42 (by decide) (by decide)
      · right
        exact rec6119 10 42 (by decide) (by decide)
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
        exact rec6122 10 42 (by decide) (by decide)
      · right
        exact rec6125 10 42 (by decide) (by decide)
      · right
        exact rec6128 10 42 (by decide) (by decide)
      · right
        exact rec6131 10 42 (by decide) (by decide)
      · right
        exact rec6134 10 42 (by decide) (by decide)
      · right
        exact rec6137 10 42 (by decide) (by decide)
      · right
        exact rec6140 10 42 (by decide) (by decide)
      · right
        exact rec6143 10 42 (by decide) (by decide)
      · right
        exact rec6146 10 42 (by decide) (by decide)
      · right
        exact rec6149 10 42 (by decide) (by decide)
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
        exact rec6152 10 42 (by decide) (by decide)
      · right
        exact rec6155 10 42 (by decide) (by decide)
      · right
        exact rec6158 10 42 (by decide) (by decide)
      · right
        exact rec6161 10 42 (by decide) (by decide)
      · right
        exact rec6164 10 42 (by decide) (by decide)
      · right
        exact rec6167 10 42 (by decide) (by decide)
      · right
        exact rec6170 10 42 (by decide) (by decide)
      · right
        exact rec6173 10 42 (by decide) (by decide)
      · right
        exact rec6176 10 42 (by decide) (by decide)
      · right
        exact rec6179 10 42 (by decide) (by decide)
      · right
        exact rec6182 10 42 (by decide) (by decide)
      · right
        exact rec6185 10 42 (by decide) (by decide)
      · right
        exact rec6188 10 42 (by decide) (by decide)
      · right
        exact rec6191 10 42 (by decide) (by decide)
      · right
        exact rec6194 10 42 (by decide) (by decide)
      · right
        exact rec6197 10 42 (by decide) (by decide)
      · right
        exact rec6200 10 42 (by decide) (by decide)
      · right
        exact rec6203 10 42 (by decide) (by decide)
      · right
        exact rec6206 10 42 (by decide) (by decide)
      · right
        exact rec6209 10 42 (by decide) (by decide)
      · right
        exact rec6212 10 42 (by decide) (by decide)
      · right
        exact rec6215 10 42 (by decide) (by decide)
      · right
        exact rec6218 10 42 (by decide) (by decide)
      · right
        exact rec6221 10 42 (by decide) (by decide)
      · right
        exact rec6224 10 42 (by decide) (by decide)
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
        exact rec6227 10 42 (by decide) (by decide)
      · right
        exact rec6230 10 42 (by decide) (by decide)
      · right
        exact rec6233 10 42 (by decide) (by decide)
      · right
        exact rec6236 10 42 (by decide) (by decide)
      · right
        exact rec6239 10 42 (by decide) (by decide)
      · right
        exact rec6242 10 42 (by decide) (by decide)
      · right
        exact rec6245 10 42 (by decide) (by decide)
      · right
        exact rec6248 10 42 (by decide) (by decide)
      · right
        exact rec6251 10 42 (by decide) (by decide)
      · right
        exact rec6254 10 42 (by decide) (by decide)
      · right
        exact rec6257 10 42 (by decide) (by decide)
      · right
        exact rec6260 10 42 (by decide) (by decide)
      · right
        exact rec6263 10 42 (by decide) (by decide)
      · right
        exact rec6266 10 42 (by decide) (by decide)
      · right
        exact rec6269 10 42 (by decide) (by decide)
      · right
        exact rec6272 10 42 (by decide) (by decide)
      · right
        exact rec6275 10 42 (by decide) (by decide)
      · right
        exact rec6278 10 42 (by decide) (by decide)
      · right
        exact rec6281 10 42 (by decide) (by decide)
      · right
        exact rec6284 10 42 (by decide) (by decide)
      · right
        exact rec6287 10 42 (by decide) (by decide)
      · right
        exact rec6290 10 42 (by decide) (by decide)
      · right
        exact rec6293 10 42 (by decide) (by decide)
      · right
        exact rec6296 10 42 (by decide) (by decide)
      · right
        exact rec6299 10 42 (by decide) (by decide)
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
        exact rec6302 10 42 (by decide) (by decide)
      · right
        exact rec6305 10 42 (by decide) (by decide)
      · right
        exact rec6308 10 42 (by decide) (by decide)
      · right
        exact rec6311 10 42 (by decide) (by decide)
      · right
        exact rec6314 10 42 (by decide) (by decide)
      · right
        exact rec6317 10 42 (by decide) (by decide)
      · right
        exact rec6320 10 42 (by decide) (by decide)
      · right
        exact rec6323 10 42 (by decide) (by decide)
      · right
        exact rec6326 10 42 (by decide) (by decide)
      · right
        exact rec6329 10 42 (by decide) (by decide)
      · right
        exact rec6332 10 42 (by decide) (by decide)
      · right
        exact rec6335 10 42 (by decide) (by decide)
      · right
        exact rec6338 10 42 (by decide) (by decide)
      · right
        exact rec6341 10 42 (by decide) (by decide)
      · right
        exact rec6344 10 42 (by decide) (by decide)
      · right
        exact rec6347 10 42 (by decide) (by decide)
      · right
        exact rec6350 10 42 (by decide) (by decide)
      · right
        exact rec6353 10 42 (by decide) (by decide)
      · right
        exact rec6356 10 42 (by decide) (by decide)
      · right
        exact rec6359 10 42 (by decide) (by decide)
      · right
        exact rec6362 10 42 (by decide) (by decide)
      · right
        exact rec6365 10 42 (by decide) (by decide)
      · right
        exact rec6368 10 42 (by decide) (by decide)
      · right
        exact rec6371 10 42 (by decide) (by decide)
      · right
        exact rec6374 10 42 (by decide) (by decide)
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
        exact rec6377 10 42 (by decide) (by decide)
      · right
        exact rec6380 10 42 (by decide) (by decide)
      · right
        exact rec6383 10 42 (by decide) (by decide)
      · right
        exact rec6387 10 42 (by decide) (by decide)
      · right
        exact rec6390 10 42 (by decide) (by decide)
      · right
        exact rec6393 10 42 (by decide) (by decide)
      · right
        exact rec6396 10 42 (by decide) (by decide)
      · right
        exact rec6399 10 42 (by decide) (by decide)
      · right
        exact rec6403 10 42 (by decide) (by decide)
      · right
        exact rec6406 10 42 (by decide) (by decide)
      · right
        exact rec6409 10 42 (by decide) (by decide)
      · right
        exact rec6412 10 42 (by decide) (by decide)
      · right
        exact rec6415 10 42 (by decide) (by decide)
      · right
        exact rec6419 10 42 (by decide) (by decide)
      · right
        exact rec6422 10 42 (by decide) (by decide)
      · right
        exact rec6425 10 42 (by decide) (by decide)
      · right
        exact rec6428 10 42 (by decide) (by decide)
      · right
        exact rec6431 10 42 (by decide) (by decide)
      · right
        exact rec6435 10 42 (by decide) (by decide)
      · right
        exact rec6438 10 42 (by decide) (by decide)
      · right
        exact rec6441 10 42 (by decide) (by decide)
      · right
        exact rec6444 10 42 (by decide) (by decide)
      · right
        exact rec6447 10 42 (by decide) (by decide)
      · right
        exact rec6451 10 42 (by decide) (by decide)
      · right
        exact rec6454 10 42 (by decide) (by decide)
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
        exact rec6457 10 42 (by decide) (by decide)
      · right
        exact rec6460 10 42 (by decide) (by decide)
      · right
        exact rec6463 10 42 (by decide) (by decide)
      · right
        exact rec6466 10 42 (by decide) (by decide)
      · right
        exact rec6469 10 42 (by decide) (by decide)
      · right
        exact rec6472 10 42 (by decide) (by decide)
      · right
        exact rec6475 10 42 (by decide) (by decide)
      · right
        exact rec6478 10 42 (by decide) (by decide)
      · right
        exact rec6481 10 42 (by decide) (by decide)
      · right
        exact rec6484 10 42 (by decide) (by decide)
      · right
        exact rec6487 10 42 (by decide) (by decide)
      · right
        exact rec6490 10 42 (by decide) (by decide)
      · right
        exact rec6493 10 42 (by decide) (by decide)
      · right
        exact rec6496 10 42 (by decide) (by decide)
      · right
        exact rec6499 10 42 (by decide) (by decide)
      · right
        exact rec6502 10 42 (by decide) (by decide)
      · right
        exact rec6505 10 42 (by decide) (by decide)
      · right
        exact rec6508 10 42 (by decide) (by decide)
      · right
        exact rec6511 10 42 (by decide) (by decide)
      · right
        exact rec6514 10 42 (by decide) (by decide)
      · right
        exact rec6517 10 42 (by decide) (by decide)
      · right
        exact rec6520 10 42 (by decide) (by decide)
      · right
        exact rec6523 10 42 (by decide) (by decide)
      · right
        exact rec6526 10 42 (by decide) (by decide)
      · right
        exact rec6529 10 42 (by decide) (by decide)
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
        exact rec6532 10 42 (by decide) (by decide)
      · right
        exact rec6535 10 42 (by decide) (by decide)
      · right
        exact rec6538 10 42 (by decide) (by decide)
      · right
        exact rec6541 10 42 (by decide) (by decide)
      · right
        exact rec6544 10 42 (by decide) (by decide)
      · right
        exact rec6547 10 42 (by decide) (by decide)
      · right
        exact rec6550 10 42 (by decide) (by decide)
      · right
        exact rec6553 10 42 (by decide) (by decide)
      · right
        exact rec6556 10 42 (by decide) (by decide)
      · right
        exact rec6559 10 42 (by decide) (by decide)
      · right
        exact rec6562 10 42 (by decide) (by decide)
      · right
        exact rec6565 10 42 (by decide) (by decide)
      · right
        exact rec6568 10 42 (by decide) (by decide)
      · right
        exact rec6571 10 42 (by decide) (by decide)
      · right
        exact rec6574 10 42 (by decide) (by decide)
      · right
        exact rec6577 10 42 (by decide) (by decide)
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
        exact rec6580 10 42 (by decide) (by decide)
      · right
        exact rec6583 10 42 (by decide) (by decide)
      · right
        exact rec6586 10 42 (by decide) (by decide)
      · right
        exact rec6589 10 42 (by decide) (by decide)
      · right
        exact rec6592 10 42 (by decide) (by decide)
      · right
        exact rec6595 10 42 (by decide) (by decide)
      · right
        exact rec6598 10 42 (by decide) (by decide)
      · right
        exact rec6601 10 42 (by decide) (by decide)
      · right
        exact rec6604 10 42 (by decide) (by decide)
      · right
        exact rec6607 10 42 (by decide) (by decide)
      · right
        exact rec6610 10 42 (by decide) (by decide)
      · right
        exact rec6613 10 42 (by decide) (by decide)
      · right
        exact rec6616 10 42 (by decide) (by decide)
      · right
        exact rec6619 10 42 (by decide) (by decide)
      · right
        exact rec6622 10 42 (by decide) (by decide)
      · right
        exact rec6625 10 42 (by decide) (by decide)
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
        exact rec6628 10 42 (by decide) (by decide)
      · right
        exact rec6631 10 42 (by decide) (by decide)
      · right
        exact rec6634 10 42 (by decide) (by decide)
      · right
        exact rec6637 10 42 (by decide) (by decide)
      · right
        exact rec6640 10 42 (by decide) (by decide)
      · right
        exact rec6643 10 42 (by decide) (by decide)
      · right
        exact rec6646 10 42 (by decide) (by decide)
      · right
        exact rec6649 10 42 (by decide) (by decide)
      · right
        exact rec6652 10 42 (by decide) (by decide)
      · right
        exact rec6655 10 42 (by decide) (by decide)
      · right
        exact rec6658 10 42 (by decide) (by decide)
      · right
        exact rec6661 10 42 (by decide) (by decide)
      · right
        exact rec6664 10 42 (by decide) (by decide)
      · right
        exact rec6667 10 42 (by decide) (by decide)
      · right
        exact rec6670 10 42 (by decide) (by decide)
      · right
        exact rec6673 10 42 (by decide) (by decide)
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
        exact rec6676 10 42 (by decide) (by decide)
      · right
        exact rec6679 10 42 (by decide) (by decide)
      · right
        exact rec6682 10 42 (by decide) (by decide)
      · right
        exact rec6685 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 564)).length = 5 := by decide +kernel
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
        exact rec6689 10 42 (by decide) (by decide)
      · right
        exact rec6692 10 42 (by decide) (by decide)
      · right
        exact rec6695 10 42 (by decide) (by decide)
      · right
        exact rec6698 10 42 (by decide) (by decide)
      · right
        exact rec6701 10 42 (by decide) (by decide)
      · right
        exact rec6704 10 42 (by decide) (by decide)
      · right
        exact rec6707 10 42 (by decide) (by decide)
      · right
        exact rec6710 10 42 (by decide) (by decide)
      · right
        exact rec6713 10 42 (by decide) (by decide)
      · right
        exact rec6716 10 42 (by decide) (by decide)
      · right
        exact rec6719 10 42 (by decide) (by decide)
      · right
        exact rec6722 10 42 (by decide) (by decide)
      · right
        exact rec6725 10 42 (by decide) (by decide)
      · right
        exact rec6728 10 42 (by decide) (by decide)
      · right
        exact rec6731 10 42 (by decide) (by decide)
      · right
        exact rec6734 10 42 (by decide) (by decide)
      · right
        exact rec6737 10 42 (by decide) (by decide)
      · right
        exact rec6740 10 42 (by decide) (by decide)
      · right
        exact rec6743 10 42 (by decide) (by decide)
      · right
        exact rec6746 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 135)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6749 10 42 (by decide) (by decide)
      · right
        exact rec6752 10 42 (by decide) (by decide)
      · right
        exact rec6755 10 42 (by decide) (by decide)
      · right
        exact rec6758 10 42 (by decide) (by decide)
      · right
        exact rec6761 10 42 (by decide) (by decide)
      · right
        exact rec6764 10 42 (by decide) (by decide)
      · right
        exact rec6767 10 42 (by decide) (by decide)
      · right
        exact rec6770 10 42 (by decide) (by decide)
      · right
        exact rec6773 10 42 (by decide) (by decide)
      · right
        exact rec6776 10 42 (by decide) (by decide)
      · right
        exact rec6779 10 42 (by decide) (by decide)
      · right
        exact rec6782 10 42 (by decide) (by decide)
      · right
        exact rec6785 10 42 (by decide) (by decide)
      · right
        exact rec6788 10 42 (by decide) (by decide)
      · right
        exact rec6791 10 42 (by decide) (by decide)
      · right
        exact rec6794 10 42 (by decide) (by decide)
      · right
        exact rec6797 10 42 (by decide) (by decide)
      · right
        exact rec6800 10 42 (by decide) (by decide)
      · right
        exact rec6804 10 42 (by decide) (by decide)
      · right
        exact rec6808 10 42 (by decide) (by decide)
      · right
        exact rec6811 10 42 (by decide) (by decide)
      · right
        exact rec6814 10 42 (by decide) (by decide)
      · right
        exact rec6817 10 42 (by decide) (by decide)
      · right
        exact rec6820 10 42 (by decide) (by decide)
      · right
        exact rec6825 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 136)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6829 10 42 (by decide) (by decide)
      · right
        exact rec6832 10 42 (by decide) (by decide)
      · right
        exact rec6835 10 42 (by decide) (by decide)
      · right
        exact rec6838 10 42 (by decide) (by decide)
      · right
        exact rec6841 10 42 (by decide) (by decide)
      · right
        exact rec6844 10 42 (by decide) (by decide)
      · right
        exact rec6848 10 42 (by decide) (by decide)
      · right
        exact rec6851 10 42 (by decide) (by decide)
      · right
        exact rec6854 10 42 (by decide) (by decide)
      · right
        exact rec6857 10 42 (by decide) (by decide)
      · right
        exact rec6860 10 42 (by decide) (by decide)
      · right
        exact rec6863 10 42 (by decide) (by decide)
      · right
        exact rec6866 10 42 (by decide) (by decide)
      · right
        exact rec6869 10 42 (by decide) (by decide)
      · right
        exact rec6872 10 42 (by decide) (by decide)
      · right
        exact rec6875 10 42 (by decide) (by decide)
      · right
        exact rec6878 10 42 (by decide) (by decide)
      · right
        exact rec6881 10 42 (by decide) (by decide)
      · right
        exact rec6884 10 42 (by decide) (by decide)
      · right
        exact rec6887 10 42 (by decide) (by decide)
      · right
        exact rec6890 10 42 (by decide) (by decide)
      · right
        exact rec6893 10 42 (by decide) (by decide)
      · right
        exact rec6896 10 42 (by decide) (by decide)
      · right
        exact rec6899 10 42 (by decide) (by decide)
      · right
        exact rec6903 10 42 (by decide) (by decide)
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
        exact rec6906 10 42 (by decide) (by decide)
      · right
        exact rec6909 10 42 (by decide) (by decide)
      · right
        exact rec6912 10 42 (by decide) (by decide)
      · right
        exact rec6915 10 42 (by decide) (by decide)
      · right
        exact rec6918 10 42 (by decide) (by decide)
      · right
        exact rec6922 10 42 (by decide) (by decide)
      · right
        exact rec6926 10 42 (by decide) (by decide)
      · right
        exact rec6930 10 42 (by decide) (by decide)
      · right
        exact rec6934 10 42 (by decide) (by decide)
      · right
        exact rec6938 10 42 (by decide) (by decide)
      · right
        exact rec6941 10 42 (by decide) (by decide)
      · right
        exact rec6944 10 42 (by decide) (by decide)
      · right
        exact rec6947 10 42 (by decide) (by decide)
      · right
        exact rec6950 10 42 (by decide) (by decide)
      · right
        exact rec6953 10 42 (by decide) (by decide)
      · right
        exact rec6956 10 42 (by decide) (by decide)
      · right
        exact rec6959 10 42 (by decide) (by decide)
      · right
        exact rec6962 10 42 (by decide) (by decide)
      · right
        exact rec6965 10 42 (by decide) (by decide)
      · right
        exact rec6968 10 42 (by decide) (by decide)
      · right
        exact rec6971 10 42 (by decide) (by decide)
      · right
        exact rec6974 10 42 (by decide) (by decide)
      · right
        exact rec6977 10 42 (by decide) (by decide)
      · right
        exact rec6980 10 42 (by decide) (by decide)
      · right
        exact rec6983 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 139)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec6986 10 42 (by decide) (by decide)
      · right
        exact rec6989 10 42 (by decide) (by decide)
      · right
        exact rec6992 10 42 (by decide) (by decide)
      · right
        exact rec6995 10 42 (by decide) (by decide)
      · right
        exact rec6998 10 42 (by decide) (by decide)
      · right
        exact rec7002 10 42 (by decide) (by decide)
      · right
        exact rec7006 10 42 (by decide) (by decide)
      · right
        exact rec7010 10 42 (by decide) (by decide)
      · right
        exact rec7013 10 42 (by decide) (by decide)
      · right
        exact rec7016 10 42 (by decide) (by decide)
      · right
        exact rec7019 10 42 (by decide) (by decide)
      · right
        exact rec7022 10 42 (by decide) (by decide)
      · right
        exact rec7025 10 42 (by decide) (by decide)
      · right
        exact rec7028 10 42 (by decide) (by decide)
      · right
        exact rec7031 10 42 (by decide) (by decide)
      · right
        exact rec7034 10 42 (by decide) (by decide)
      · right
        exact rec7037 10 42 (by decide) (by decide)
      · right
        exact rec7040 10 42 (by decide) (by decide)
      · right
        exact rec7043 10 42 (by decide) (by decide)
      · right
        exact rec7046 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 140)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7049 10 42 (by decide) (by decide)
      · right
        exact rec7052 10 42 (by decide) (by decide)
      · right
        exact rec7055 10 42 (by decide) (by decide)
      · right
        exact rec7060 10 42 (by decide) (by decide)
      · right
        exact rec7063 10 42 (by decide) (by decide)
      · right
        exact rec7066 10 42 (by decide) (by decide)
      · right
        exact rec7071 10 42 (by decide) (by decide)
      · right
        exact rec7075 10 42 (by decide) (by decide)
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
        exact rec7078 10 42 (by decide) (by decide)
      · right
        exact rec7081 10 42 (by decide) (by decide)
      · right
        exact rec7084 10 42 (by decide) (by decide)
      · right
        exact rec7087 10 42 (by decide) (by decide)
      · right
        exact rec7090 10 42 (by decide) (by decide)
      · right
        exact rec7093 10 42 (by decide) (by decide)
      · right
        exact rec7096 10 42 (by decide) (by decide)
      · right
        exact rec7099 10 42 (by decide) (by decide)
      · right
        exact rec7102 10 42 (by decide) (by decide)
      · right
        exact rec7105 10 42 (by decide) (by decide)
      · right
        exact rec7108 10 42 (by decide) (by decide)
      · right
        exact rec7111 10 42 (by decide) (by decide)
      · right
        exact rec7114 10 42 (by decide) (by decide)
      · right
        exact rec7117 10 42 (by decide) (by decide)
      · right
        exact rec7120 10 42 (by decide) (by decide)
      · right
        exact rec7123 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 143)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7126 10 42 (by decide) (by decide)
      · right
        exact rec7129 10 42 (by decide) (by decide)
      · right
        exact rec7132 10 42 (by decide) (by decide)
      · right
        exact rec7135 10 42 (by decide) (by decide)
      · right
        exact rec7138 10 42 (by decide) (by decide)
      · right
        exact rec7141 10 42 (by decide) (by decide)
      · right
        exact rec7144 10 42 (by decide) (by decide)
      · right
        exact rec7147 10 42 (by decide) (by decide)
      · right
        exact rec7150 10 42 (by decide) (by decide)
      · right
        exact rec7153 10 42 (by decide) (by decide)
      · right
        exact rec7156 10 42 (by decide) (by decide)
      · right
        exact rec7159 10 42 (by decide) (by decide)
      · right
        exact rec7162 10 42 (by decide) (by decide)
      · right
        exact rec7165 10 42 (by decide) (by decide)
      · right
        exact rec7168 10 42 (by decide) (by decide)
      · right
        exact rec7171 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 144)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7174 10 42 (by decide) (by decide)
      · right
        exact rec7177 10 42 (by decide) (by decide)
      · right
        exact rec7180 10 42 (by decide) (by decide)
      · right
        exact rec7183 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 145)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7186 10 42 (by decide) (by decide)
      · right
        exact rec7189 10 42 (by decide) (by decide)
      · right
        exact rec7193 10 42 (by decide) (by decide)
      · right
        exact rec7197 10 42 (by decide) (by decide)
      · right
        exact rec7200 10 42 (by decide) (by decide)
      · right
        exact rec7203 10 42 (by decide) (by decide)
      · right
        exact rec7206 10 42 (by decide) (by decide)
      · right
        exact rec7209 10 42 (by decide) (by decide)
      · right
        exact rec7212 10 42 (by decide) (by decide)
      · right
        exact rec7215 10 42 (by decide) (by decide)
      · right
        exact rec7218 10 42 (by decide) (by decide)
      · right
        exact rec7221 10 42 (by decide) (by decide)
      · right
        exact rec7224 10 42 (by decide) (by decide)
      · right
        exact rec7227 10 42 (by decide) (by decide)
      · right
        exact rec7230 10 42 (by decide) (by decide)
      · right
        exact rec7233 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 146)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7237 10 42 (by decide) (by decide)
      · right
        exact rec7241 10 42 (by decide) (by decide)
      · right
        exact rec7244 10 42 (by decide) (by decide)
      · right
        exact rec7248 10 42 (by decide) (by decide)
      · right
        exact rec7251 10 42 (by decide) (by decide)
      · right
        exact rec7254 10 42 (by decide) (by decide)
      · right
        exact rec7257 10 42 (by decide) (by decide)
      · right
        exact rec7260 10 42 (by decide) (by decide)
      · right
        exact rec7263 10 42 (by decide) (by decide)
      · right
        exact rec7266 10 42 (by decide) (by decide)
      · right
        exact rec7269 10 42 (by decide) (by decide)
      · right
        exact rec7272 10 42 (by decide) (by decide)
      · right
        exact rec7275 10 42 (by decide) (by decide)
      · right
        exact rec7278 10 42 (by decide) (by decide)
      · right
        exact rec7281 10 42 (by decide) (by decide)
      · right
        exact rec7284 10 42 (by decide) (by decide)
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
        exact rec7287 10 42 (by decide) (by decide)
      · right
        exact rec7290 10 42 (by decide) (by decide)
      · right
        exact rec7293 10 42 (by decide) (by decide)
      · right
        exact rec7296 10 42 (by decide) (by decide)
      · right
        exact rec7299 10 42 (by decide) (by decide)
      · right
        exact rec7302 10 42 (by decide) (by decide)
      · right
        exact rec7305 10 42 (by decide) (by decide)
      · right
        exact rec7308 10 42 (by decide) (by decide)
      · right
        exact rec7311 10 42 (by decide) (by decide)
      · right
        exact rec7314 10 42 (by decide) (by decide)
      · right
        exact rec7317 10 42 (by decide) (by decide)
      · right
        exact rec7320 10 42 (by decide) (by decide)
      · right
        exact rec7323 10 42 (by decide) (by decide)
      · right
        exact rec7326 10 42 (by decide) (by decide)
      · right
        exact rec7329 10 42 (by decide) (by decide)
      · right
        exact rec7332 10 42 (by decide) (by decide)
      · right
        exact rec7335 10 42 (by decide) (by decide)
      · right
        exact rec7338 10 42 (by decide) (by decide)
      · right
        exact rec7341 10 42 (by decide) (by decide)
      · right
        exact rec7344 10 42 (by decide) (by decide)
      · right
        exact rec7347 10 42 (by decide) (by decide)
      · right
        exact rec7350 10 42 (by decide) (by decide)
      · right
        exact rec7353 10 42 (by decide) (by decide)
      · right
        exact rec7356 10 42 (by decide) (by decide)
      · right
        exact rec7359 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 565)).length = 2 := by decide +kernel
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
    exact rec5609 10 43 (by decide) (by decide)
  · left
    exact rec5604 10 44 (by decide) (by decide)
  · left
    exact rec5604 10 45 (by decide) (by decide)
  · left
    exact rec5611 10 46 (by decide) (by decide)
  · left
    exact rec5609 10 47 (by decide) (by decide)
end Section14Coverage_10_4_p32_48

#print axioms solution
