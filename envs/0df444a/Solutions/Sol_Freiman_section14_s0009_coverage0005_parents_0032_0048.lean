-- Prove2me | solution 1 for Freiman.section14_s0009_coverage0005_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T19:29:30.127086+00:00
-- url     : https://prove2.me/submissions/3afcb987-f294-4e29-9eba-66cae8053861

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
namespace Section14Coverage_9_5_p32_48
private theorem rec7425 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[893]? = some (⟨153,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) from rfl))
private theorem rec7429 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[9,10],[34],634⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[897]? = some (⟨153,(-1),[9,10],[34],634⟩) from rfl))
private theorem rec7430 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35, 39, 43, 47] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[9,10],[35,39,43,47],636⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[898]? = some (⟨153,(-1),[9,10],[35,39,43,47],636⟩) from rfl))
private theorem rec7431 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[9,10],[38],637⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[899]? = some (⟨153,(-1),[9,10],[38],637⟩) from rfl))
private theorem rec7432 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[9,10],[46],879⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[900]? = some (⟨153,(-1),[9,10],[46],879⟩) from rfl))
private theorem rec7442 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(0),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[910]? = some (⟨155,(0),[9,10],[42],3⟩) from rfl))
private theorem rec7445 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(1),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[913]? = some (⟨155,(1),[9,10],[42],3⟩) from rfl))
private theorem rec7448 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(2),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[916]? = some (⟨155,(2),[9,10],[42],3⟩) from rfl))
private theorem rec7451 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(3),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[919]? = some (⟨155,(3),[9,10],[42],3⟩) from rfl))
private theorem rec7454 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(4),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[922]? = some (⟨155,(4),[9,10],[42],3⟩) from rfl))
private theorem rec7457 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(5),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[925]? = some (⟨155,(5),[9,10],[42],3⟩) from rfl))
private theorem rec7460 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(6),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[928]? = some (⟨155,(6),[9,10],[42],3⟩) from rfl))
private theorem rec7463 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(7),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[931]? = some (⟨155,(7),[9,10],[42],3⟩) from rfl))
private theorem rec7466 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(8),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[934]? = some (⟨155,(8),[9,10],[42],3⟩) from rfl))
private theorem rec7469 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(9),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[937]? = some (⟨155,(9),[9,10],[42],3⟩) from rfl))
private theorem rec7472 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(10),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[940]? = some (⟨155,(10),[9,10],[42],3⟩) from rfl))
private theorem rec7475 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(11),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[943]? = some (⟨155,(11),[9,10],[42],3⟩) from rfl))
private theorem rec7478 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(12),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[946]? = some (⟨155,(12),[9,10],[42],3⟩) from rfl))
private theorem rec7481 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(13),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[949]? = some (⟨155,(13),[9,10],[42],3⟩) from rfl))
private theorem rec7484 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(14),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[952]? = some (⟨155,(14),[9,10],[42],3⟩) from rfl))
private theorem rec7487 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(15),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[955]? = some (⟨155,(15),[9,10],[42],3⟩) from rfl))
private theorem rec7490 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(16),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[958]? = some (⟨155,(16),[9,10],[42],3⟩) from rfl))
private theorem rec7493 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(17),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[961]? = some (⟨155,(17),[9,10],[42],3⟩) from rfl))
private theorem rec7496 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(18),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[964]? = some (⟨155,(18),[9,10],[42],3⟩) from rfl))
private theorem rec7499 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(19),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[967]? = some (⟨155,(19),[9,10],[42],3⟩) from rfl))
private theorem rec7502 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(20),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[970]? = some (⟨155,(20),[9,10],[42],3⟩) from rfl))
private theorem rec7505 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(21),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[973]? = some (⟨155,(21),[9,10],[42],3⟩) from rfl))
private theorem rec7508 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(22),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[976]? = some (⟨155,(22),[9,10],[42],3⟩) from rfl))
private theorem rec7511 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(23),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[979]? = some (⟨155,(23),[9,10],[42],3⟩) from rfl))
private theorem rec7514 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 155 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(24),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[982]? = some (⟨155,(24),[9,10],[42],3⟩) from rfl))
private theorem rec7640 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(0),[9,10],[42],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1108]? = some (⟨160,(0),[9,10],[42],638⟩) from rfl))
private theorem rec7647 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(1),[9,10],[42],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1115]? = some (⟨160,(1),[9,10],[42],639⟩) from rfl))
private theorem rec7654 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(2),[9,10],[42],640⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1122]? = some (⟨160,(2),[9,10],[42],640⟩) from rfl))
private theorem rec7661 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(3),[9,10],[42],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1129]? = some (⟨160,(3),[9,10],[42],641⟩) from rfl))
private theorem rec7668 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(4),[9,10],[42],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1136]? = some (⟨160,(4),[9,10],[42],638⟩) from rfl))
private theorem rec7675 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(5),[9,10],[42],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1143]? = some (⟨160,(5),[9,10],[42],639⟩) from rfl))
private theorem rec7682 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(6),[9,10],[42],642⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1150]? = some (⟨160,(6),[9,10],[42],642⟩) from rfl))
private theorem rec7689 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(7),[9,10],[42],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[5]? = some (⟨160,(7),[9,10],[42],641⟩) from rfl))
private theorem rec7696 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(8),[9,10],[42],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[12]? = some (⟨160,(8),[9,10],[42],638⟩) from rfl))
private theorem rec7703 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(9),[9,10],[42],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[19]? = some (⟨160,(9),[9,10],[42],639⟩) from rfl))
private theorem rec7710 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(10),[9,10],[42],640⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[26]? = some (⟨160,(10),[9,10],[42],640⟩) from rfl))
private theorem rec7717 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(11),[9,10],[42],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[33]? = some (⟨160,(11),[9,10],[42],641⟩) from rfl))
private theorem rec7724 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(12),[9,10],[42],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[40]? = some (⟨160,(12),[9,10],[42],638⟩) from rfl))
private theorem rec7731 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(13),[9,10],[42],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[47]? = some (⟨160,(13),[9,10],[42],639⟩) from rfl))
private theorem rec7738 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(14),[9,10],[42],643⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[54]? = some (⟨160,(14),[9,10],[42],643⟩) from rfl))
private theorem rec7745 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 160 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(15),[9,10],[42],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[61]? = some (⟨160,(15),[9,10],[42],641⟩) from rfl))
private theorem rec7752 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(0),[9],[42],1279⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[68]? = some (⟨163,(0),[9],[42],1279⟩) from rfl))
private theorem rec7760 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(1),[9],[42],1280⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[76]? = some (⟨163,(1),[9],[42],1280⟩) from rfl))
private theorem rec7768 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(2),[9],[42],1279⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[84]? = some (⟨163,(2),[9],[42],1279⟩) from rfl))
private theorem rec7776 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(3),[9],[42],1281⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[92]? = some (⟨163,(3),[9],[42],1281⟩) from rfl))
private theorem rec7784 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(4),[9],[42],1282⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[100]? = some (⟨163,(4),[9],[42],1282⟩) from rfl))
private theorem rec7792 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(5),[9],[42],1282⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[108]? = some (⟨163,(5),[9],[42],1282⟩) from rfl))
private theorem rec7800 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(6),[9],[42],1282⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[116]? = some (⟨163,(6),[9],[42],1282⟩) from rfl))
private theorem rec7808 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(7),[9],[42],1282⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[124]? = some (⟨163,(7),[9],[42],1282⟩) from rfl))
private theorem rec7816 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(8),[9],[42],1283⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[132]? = some (⟨163,(8),[9],[42],1283⟩) from rfl))
private theorem rec7824 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(9),[9],[42],1283⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[140]? = some (⟨163,(9),[9],[42],1283⟩) from rfl))
private theorem rec7832 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(10),[9],[42],1283⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[148]? = some (⟨163,(10),[9],[42],1283⟩) from rfl))
private theorem rec7840 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(11),[9],[42],1283⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[156]? = some (⟨163,(11),[9],[42],1283⟩) from rfl))
private theorem rec7848 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(12),[9],[42],1284⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[164]? = some (⟨163,(12),[9],[42],1284⟩) from rfl))
private theorem rec7856 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(13),[9],[42],1284⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[172]? = some (⟨163,(13),[9],[42],1284⟩) from rfl))
private theorem rec7864 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(14),[9],[42],1284⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[180]? = some (⟨163,(14),[9],[42],1284⟩) from rfl))
private theorem rec7872 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(15),[9],[42],1284⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[188]? = some (⟨163,(15),[9],[42],1284⟩) from rfl))
private theorem rec7880 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(0),[9,10],[42],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[196]? = some (⟨166,(0),[9,10],[42],644⟩) from rfl))
private theorem rec7887 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(1),[9,10],[42],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[203]? = some (⟨166,(1),[9,10],[42],644⟩) from rfl))
private theorem rec7894 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(2),[9,10],[42],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[210]? = some (⟨166,(2),[9,10],[42],644⟩) from rfl))
private theorem rec7901 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(3),[9,10],[42],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[217]? = some (⟨166,(3),[9,10],[42],644⟩) from rfl))
private theorem rec7908 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(4),[9,10],[42],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[224]? = some (⟨166,(4),[9,10],[42],645⟩) from rfl))
private theorem rec7915 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(5),[9,10],[42],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[231]? = some (⟨166,(5),[9,10],[42],645⟩) from rfl))
private theorem rec7922 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(6),[9,10],[42],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[238]? = some (⟨166,(6),[9,10],[42],645⟩) from rfl))
private theorem rec7929 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(7),[9,10],[42],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[245]? = some (⟨166,(7),[9,10],[42],645⟩) from rfl))
private theorem rec7936 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(8),[9,10],[42],646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[252]? = some (⟨166,(8),[9,10],[42],646⟩) from rfl))
private theorem rec7943 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(9),[9,10],[42],647⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[259]? = some (⟨166,(9),[9,10],[42],647⟩) from rfl))
private theorem rec7950 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(10),[9,10],[42],646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[266]? = some (⟨166,(10),[9,10],[42],646⟩) from rfl))
private theorem rec7957 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(11),[9,10],[42],648⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[273]? = some (⟨166,(11),[9,10],[42],648⟩) from rfl))
private theorem rec7964 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(12),[9,10],[42],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[280]? = some (⟨166,(12),[9,10],[42],649⟩) from rfl))
private theorem rec7971 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(13),[9,10],[42],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[287]? = some (⟨166,(13),[9,10],[42],649⟩) from rfl))
private theorem rec7978 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(14),[9,10],[42],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[294]? = some (⟨166,(14),[9,10],[42],649⟩) from rfl))
private theorem rec7985 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 166 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(15),[9,10],[42],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[301]? = some (⟨166,(15),[9,10],[42],649⟩) from rfl))
private theorem rec7992 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(0),[9],[42],1285⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[308]? = some (⟨167,(0),[9],[42],1285⟩) from rfl))
private theorem rec8000 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(1),[9],[42],1286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[316]? = some (⟨167,(1),[9],[42],1286⟩) from rfl))
private theorem rec8008 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(2),[9],[42],1287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[324]? = some (⟨167,(2),[9],[42],1287⟩) from rfl))
private theorem rec8016 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(3),[9],[42],1288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[332]? = some (⟨167,(3),[9],[42],1288⟩) from rfl))
private theorem rec8024 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(4),[9],[42],1289⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[340]? = some (⟨167,(4),[9],[42],1289⟩) from rfl))
private theorem rec8032 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(5),[9],[42],1286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[348]? = some (⟨167,(5),[9],[42],1286⟩) from rfl))
private theorem rec8040 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(6),[9],[42],1287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[356]? = some (⟨167,(6),[9],[42],1287⟩) from rfl))
private theorem rec8048 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(7),[9],[42],1288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[364]? = some (⟨167,(7),[9],[42],1288⟩) from rfl))
private theorem rec8056 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(8),[9],[42],1285⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[372]? = some (⟨167,(8),[9],[42],1285⟩) from rfl))
private theorem rec8064 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(9),[9],[42],1286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[380]? = some (⟨167,(9),[9],[42],1286⟩) from rfl))
private theorem rec8072 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(10),[9],[42],1287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[388]? = some (⟨167,(10),[9],[42],1287⟩) from rfl))
private theorem rec8080 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(11),[9],[42],1288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[396]? = some (⟨167,(11),[9],[42],1288⟩) from rfl))
private theorem rec8088 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(12),[9],[42],1290⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[404]? = some (⟨167,(12),[9],[42],1290⟩) from rfl))
private theorem rec8096 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(13),[9],[42],1286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[412]? = some (⟨167,(13),[9],[42],1286⟩) from rfl))
private theorem rec8104 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(14),[9],[42],1287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[420]? = some (⟨167,(14),[9],[42],1287⟩) from rfl))
private theorem rec8112 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(15),[9],[42],1288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[428]? = some (⟨167,(15),[9],[42],1288⟩) from rfl))
private theorem rec8120 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 171 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(0),[9,10],[42],650⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[436]? = some (⟨171,(0),[9,10],[42],650⟩) from rfl))
private theorem rec8127 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 171 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(1),[9,10],[42],651⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[443]? = some (⟨171,(1),[9,10],[42],651⟩) from rfl))
private theorem rec8134 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 171 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(2),[9,10],[42],652⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[450]? = some (⟨171,(2),[9,10],[42],652⟩) from rfl))
private theorem rec8141 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 171 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(3),[9,10],[42],653⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[457]? = some (⟨171,(3),[9,10],[42],653⟩) from rfl))
private theorem rec8148 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(0),[9],[42],1291⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[464]? = some (⟨172,(0),[9],[42],1291⟩) from rfl))
private theorem rec8156 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(1),[9],[42],1292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[472]? = some (⟨172,(1),[9],[42],1292⟩) from rfl))
private theorem rec8164 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(2),[9],[42],1293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[480]? = some (⟨172,(2),[9],[42],1293⟩) from rfl))
private theorem rec8172 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(3),[9],[42],1294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[488]? = some (⟨172,(3),[9],[42],1294⟩) from rfl))
private theorem rec8180 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(4),[9],[42],1295⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[496]? = some (⟨172,(4),[9],[42],1295⟩) from rfl))
private theorem rec8188 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(5),[9],[42],1292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[504]? = some (⟨172,(5),[9],[42],1292⟩) from rfl))
private theorem rec8196 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(6),[9],[42],1293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[512]? = some (⟨172,(6),[9],[42],1293⟩) from rfl))
private theorem rec8204 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(7),[9],[42],1294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[520]? = some (⟨172,(7),[9],[42],1294⟩) from rfl))
private theorem rec8212 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(8),[9],[42],1291⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[528]? = some (⟨172,(8),[9],[42],1291⟩) from rfl))
private theorem rec8220 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(9),[9],[42],1292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[536]? = some (⟨172,(9),[9],[42],1292⟩) from rfl))
private theorem rec8228 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(10),[9],[42],1293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[544]? = some (⟨172,(10),[9],[42],1293⟩) from rfl))
private theorem rec8236 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(11),[9],[42],1294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[552]? = some (⟨172,(11),[9],[42],1294⟩) from rfl))
private theorem rec8244 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(12),[9],[42],1296⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[560]? = some (⟨172,(12),[9],[42],1296⟩) from rfl))
private theorem rec8252 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(13),[9],[42],1292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[568]? = some (⟨172,(13),[9],[42],1292⟩) from rfl))
private theorem rec8260 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(14),[9],[42],1293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[576]? = some (⟨172,(14),[9],[42],1293⟩) from rfl))
private theorem rec8268 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(15),[9],[42],1294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[584]? = some (⟨172,(15),[9],[42],1294⟩) from rfl))
private theorem rec8276 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(0),[9,10],[42],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[592]? = some (⟨175,(0),[9,10],[42],654⟩) from rfl))
private theorem rec8283 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(1),[9,10],[42],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[599]? = some (⟨175,(1),[9,10],[42],655⟩) from rfl))
private theorem rec8290 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(2),[9,10],[42],656⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[606]? = some (⟨175,(2),[9,10],[42],656⟩) from rfl))
private theorem rec8297 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(3),[9,10],[42],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[613]? = some (⟨175,(3),[9,10],[42],657⟩) from rfl))
private theorem rec8304 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(4),[9,10],[42],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[5]? = some (⟨175,(4),[9,10],[42],654⟩) from rfl))
private theorem rec8311 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(5),[9,10],[42],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[12]? = some (⟨175,(5),[9,10],[42],655⟩) from rfl))
private theorem rec8318 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(6),[9,10],[42],658⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[19]? = some (⟨175,(6),[9,10],[42],658⟩) from rfl))
private theorem rec8325 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(7),[9,10],[42],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[26]? = some (⟨175,(7),[9,10],[42],657⟩) from rfl))
private theorem rec8332 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(8),[9,10],[42],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[33]? = some (⟨175,(8),[9,10],[42],654⟩) from rfl))
private theorem rec8339 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(9),[9,10],[42],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[40]? = some (⟨175,(9),[9,10],[42],655⟩) from rfl))
private theorem rec8346 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(10),[9,10],[42],656⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[47]? = some (⟨175,(10),[9,10],[42],656⟩) from rfl))
private theorem rec8353 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(11),[9,10],[42],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[54]? = some (⟨175,(11),[9,10],[42],657⟩) from rfl))
private theorem rec8360 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(12),[9,10],[42],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[61]? = some (⟨175,(12),[9,10],[42],654⟩) from rfl))
private theorem rec8367 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(13),[9,10],[42],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[68]? = some (⟨175,(13),[9,10],[42],655⟩) from rfl))
private theorem rec8374 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(14),[9,10],[42],659⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[75]? = some (⟨175,(14),[9,10],[42],659⟩) from rfl))
private theorem rec8381 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 175 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(15),[9,10],[42],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[82]? = some (⟨175,(15),[9,10],[42],657⟩) from rfl))
private theorem rec8388 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(0),[9],[42],1297⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[89]? = some (⟨178,(0),[9],[42],1297⟩) from rfl))
private theorem rec8396 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(1),[9],[42],1298⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[97]? = some (⟨178,(1),[9],[42],1298⟩) from rfl))
private theorem rec8404 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(2),[9],[42],1297⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[105]? = some (⟨178,(2),[9],[42],1297⟩) from rfl))
private theorem rec8412 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(3),[9],[42],1299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[113]? = some (⟨178,(3),[9],[42],1299⟩) from rfl))
private theorem rec8420 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(4),[9],[42],1300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[121]? = some (⟨178,(4),[9],[42],1300⟩) from rfl))
private theorem rec8428 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(5),[9],[42],1300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[129]? = some (⟨178,(5),[9],[42],1300⟩) from rfl))
private theorem rec8436 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(6),[9],[42],1300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[137]? = some (⟨178,(6),[9],[42],1300⟩) from rfl))
private theorem rec8444 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(7),[9],[42],1300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[145]? = some (⟨178,(7),[9],[42],1300⟩) from rfl))
private theorem rec8452 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(8),[9],[42],1301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[153]? = some (⟨178,(8),[9],[42],1301⟩) from rfl))
private theorem rec8460 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(9),[9],[42],1301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[161]? = some (⟨178,(9),[9],[42],1301⟩) from rfl))
private theorem rec8468 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(10),[9],[42],1301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[169]? = some (⟨178,(10),[9],[42],1301⟩) from rfl))
private theorem rec8476 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(11),[9],[42],1301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[177]? = some (⟨178,(11),[9],[42],1301⟩) from rfl))
private theorem rec8484 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(12),[9],[42],1302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[185]? = some (⟨178,(12),[9],[42],1302⟩) from rfl))
private theorem rec8492 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(13),[9],[42],1302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[193]? = some (⟨178,(13),[9],[42],1302⟩) from rfl))
private theorem rec8500 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(14),[9],[42],1302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[201]? = some (⟨178,(14),[9],[42],1302⟩) from rfl))
private theorem rec8508 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(15),[9],[42],1302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[209]? = some (⟨178,(15),[9],[42],1302⟩) from rfl))
private theorem rec8516 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(0),[9,10],[42],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[217]? = some (⟨180,(0),[9,10],[42],666⟩) from rfl))
private theorem rec8523 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(1),[9,10],[42],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[224]? = some (⟨180,(1),[9,10],[42],667⟩) from rfl))
private theorem rec8530 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(2),[9,10],[42],668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[231]? = some (⟨180,(2),[9,10],[42],668⟩) from rfl))
private theorem rec8537 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(3),[9,10],[42],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[238]? = some (⟨180,(3),[9,10],[42],669⟩) from rfl))
private theorem rec8544 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(4),[9,10],[42],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[245]? = some (⟨180,(4),[9,10],[42],666⟩) from rfl))
private theorem rec8551 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(5),[9,10],[42],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[252]? = some (⟨180,(5),[9,10],[42],667⟩) from rfl))
private theorem rec8558 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(6),[9,10],[42],670⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[259]? = some (⟨180,(6),[9,10],[42],670⟩) from rfl))
private theorem rec8565 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(7),[9,10],[42],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[266]? = some (⟨180,(7),[9,10],[42],669⟩) from rfl))
private theorem rec8572 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(8),[9,10],[42],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[273]? = some (⟨180,(8),[9,10],[42],666⟩) from rfl))
private theorem rec8579 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(9),[9,10],[42],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[280]? = some (⟨180,(9),[9,10],[42],667⟩) from rfl))
private theorem rec8586 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(10),[9,10],[42],668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[287]? = some (⟨180,(10),[9,10],[42],668⟩) from rfl))
private theorem rec8593 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(11),[9,10],[42],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[294]? = some (⟨180,(11),[9,10],[42],669⟩) from rfl))
private theorem rec8600 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(12),[9,10],[42],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[301]? = some (⟨180,(12),[9,10],[42],666⟩) from rfl))
private theorem rec8607 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(13),[9,10],[42],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[308]? = some (⟨180,(13),[9,10],[42],667⟩) from rfl))
private theorem rec8614 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(14),[9,10],[42],671⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[315]? = some (⟨180,(14),[9,10],[42],671⟩) from rfl))
private theorem rec8621 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 180 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(15),[9,10],[42],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[322]? = some (⟨180,(15),[9,10],[42],669⟩) from rfl))
private theorem rec8628 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(0),[9],[42],1303⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[329]? = some (⟨183,(0),[9],[42],1303⟩) from rfl))
private theorem rec8636 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(1),[9],[42],1304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[337]? = some (⟨183,(1),[9],[42],1304⟩) from rfl))
private theorem rec8644 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(2),[9],[42],1303⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[345]? = some (⟨183,(2),[9],[42],1303⟩) from rfl))
private theorem rec8652 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(3),[9],[42],1305⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[353]? = some (⟨183,(3),[9],[42],1305⟩) from rfl))
private theorem rec8660 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(4),[9],[42],1306⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[361]? = some (⟨183,(4),[9],[42],1306⟩) from rfl))
private theorem rec8668 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(5),[9],[42],1306⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[369]? = some (⟨183,(5),[9],[42],1306⟩) from rfl))
private theorem rec8676 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(6),[9],[42],1306⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[377]? = some (⟨183,(6),[9],[42],1306⟩) from rfl))
private theorem rec8684 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(7),[9],[42],1306⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[385]? = some (⟨183,(7),[9],[42],1306⟩) from rfl))
private theorem rec8692 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(8),[9],[42],1307⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[393]? = some (⟨183,(8),[9],[42],1307⟩) from rfl))
private theorem rec8700 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(9),[9],[42],1307⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[401]? = some (⟨183,(9),[9],[42],1307⟩) from rfl))
private theorem rec8708 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(10),[9],[42],1307⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[409]? = some (⟨183,(10),[9],[42],1307⟩) from rfl))
private theorem rec8716 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(11),[9],[42],1307⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[417]? = some (⟨183,(11),[9],[42],1307⟩) from rfl))
private theorem rec8724 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(12),[9],[42],1308⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[425]? = some (⟨183,(12),[9],[42],1308⟩) from rfl))
private theorem rec8732 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(13),[9],[42],1308⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[433]? = some (⟨183,(13),[9],[42],1308⟩) from rfl))
private theorem rec8740 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(14),[9],[42],1308⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[441]? = some (⟨183,(14),[9],[42],1308⟩) from rfl))
private theorem rec8748 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(15),[9],[42],1308⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[449]? = some (⟨183,(15),[9],[42],1308⟩) from rfl))
private theorem rec8756 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(0),[9,10],[42],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[457]? = some (⟨185,(0),[9,10],[42],678⟩) from rfl))
private theorem rec8763 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(1),[9,10],[42],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[464]? = some (⟨185,(1),[9,10],[42],679⟩) from rfl))
private theorem rec8770 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(2),[9,10],[42],680⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[471]? = some (⟨185,(2),[9,10],[42],680⟩) from rfl))
private theorem rec8777 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(3),[9,10],[42],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[478]? = some (⟨185,(3),[9,10],[42],681⟩) from rfl))
private theorem rec8784 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(4),[9,10],[42],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[485]? = some (⟨185,(4),[9,10],[42],678⟩) from rfl))
private theorem rec8791 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(5),[9,10],[42],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[492]? = some (⟨185,(5),[9,10],[42],679⟩) from rfl))
private theorem rec8798 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(6),[9,10],[42],682⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[499]? = some (⟨185,(6),[9,10],[42],682⟩) from rfl))
private theorem rec8805 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(7),[9,10],[42],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[506]? = some (⟨185,(7),[9,10],[42],681⟩) from rfl))
private theorem rec8812 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(8),[9,10],[42],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[513]? = some (⟨185,(8),[9,10],[42],678⟩) from rfl))
private theorem rec8819 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(9),[9,10],[42],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[520]? = some (⟨185,(9),[9,10],[42],679⟩) from rfl))
private theorem rec8826 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(10),[9,10],[42],680⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[527]? = some (⟨185,(10),[9,10],[42],680⟩) from rfl))
private theorem rec8833 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(11),[9,10],[42],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[534]? = some (⟨185,(11),[9,10],[42],681⟩) from rfl))
private theorem rec8840 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(12),[9,10],[42],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[541]? = some (⟨185,(12),[9,10],[42],678⟩) from rfl))
private theorem rec8847 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(13),[9,10],[42],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[548]? = some (⟨185,(13),[9,10],[42],679⟩) from rfl))
private theorem rec8854 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(14),[9,10],[42],683⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[555]? = some (⟨185,(14),[9,10],[42],683⟩) from rfl))
private theorem rec8861 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 185 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(15),[9,10],[42],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[562]? = some (⟨185,(15),[9,10],[42],681⟩) from rfl))
private theorem rec8868 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(0),[9],[42],1309⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[569]? = some (⟨188,(0),[9],[42],1309⟩) from rfl))
private theorem rec8876 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(1),[9],[42],1310⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[577]? = some (⟨188,(1),[9],[42],1310⟩) from rfl))
private theorem rec8884 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(2),[9],[42],1309⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[585]? = some (⟨188,(2),[9],[42],1309⟩) from rfl))
private theorem rec8892 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(3),[9],[42],1311⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[593]? = some (⟨188,(3),[9],[42],1311⟩) from rfl))
private theorem rec8900 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(4),[9],[42],1312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[601]? = some (⟨188,(4),[9],[42],1312⟩) from rfl))
private theorem rec8908 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(5),[9],[42],1312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[609]? = some (⟨188,(5),[9],[42],1312⟩) from rfl))
private theorem rec8916 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(6),[9],[42],1312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[617]? = some (⟨188,(6),[9],[42],1312⟩) from rfl))
private theorem rec8924 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(7),[9],[42],1312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[625]? = some (⟨188,(7),[9],[42],1312⟩) from rfl))
private theorem rec8932 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(8),[9],[42],1313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[633]? = some (⟨188,(8),[9],[42],1313⟩) from rfl))
private theorem rec8940 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(9),[9],[42],1313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[641]? = some (⟨188,(9),[9],[42],1313⟩) from rfl))
private theorem rec8948 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(10),[9],[42],1313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[649]? = some (⟨188,(10),[9],[42],1313⟩) from rfl))
private theorem rec8956 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(11),[9],[42],1313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[657]? = some (⟨188,(11),[9],[42],1313⟩) from rfl))
private theorem rec8964 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(12),[9],[42],1314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[665]? = some (⟨188,(12),[9],[42],1314⟩) from rfl))
private theorem rec8972 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(13),[9],[42],1314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[673]? = some (⟨188,(13),[9],[42],1314⟩) from rfl))
private theorem rec8980 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(14),[9],[42],1314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[681]? = some (⟨188,(14),[9],[42],1314⟩) from rfl))
private theorem rec8988 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(15),[9],[42],1314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[689]? = some (⟨188,(15),[9],[42],1314⟩) from rfl))
private theorem rec8996 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(0),[9,10],[42],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[697]? = some (⟨190,(0),[9,10],[42],690⟩) from rfl))
private theorem rec9003 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(1),[9,10],[42],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[704]? = some (⟨190,(1),[9,10],[42],690⟩) from rfl))
private theorem rec9010 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(2),[9,10],[42],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[711]? = some (⟨190,(2),[9,10],[42],690⟩) from rfl))
private theorem rec9017 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(3),[9,10],[42],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[718]? = some (⟨190,(3),[9,10],[42],690⟩) from rfl))
private theorem rec9024 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(4),[9,10],[42],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[725]? = some (⟨190,(4),[9,10],[42],690⟩) from rfl))
private theorem rec9031 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(5),[9,10],[42],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[732]? = some (⟨190,(5),[9,10],[42],691⟩) from rfl))
private theorem rec9038 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(6),[9,10],[42],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[739]? = some (⟨190,(6),[9,10],[42],691⟩) from rfl))
private theorem rec9045 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(7),[9,10],[42],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[746]? = some (⟨190,(7),[9,10],[42],691⟩) from rfl))
private theorem rec9052 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(8),[9,10],[42],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[753]? = some (⟨190,(8),[9,10],[42],691⟩) from rfl))
private theorem rec9059 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(9),[9,10],[42],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[760]? = some (⟨190,(9),[9,10],[42],691⟩) from rfl))
private theorem rec9066 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(10),[9,10],[42],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[767]? = some (⟨190,(10),[9,10],[42],692⟩) from rfl))
private theorem rec9073 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(11),[9,10],[42],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[774]? = some (⟨190,(11),[9,10],[42],693⟩) from rfl))
private theorem rec9080 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(12),[9,10],[42],694⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[781]? = some (⟨190,(12),[9,10],[42],694⟩) from rfl))
private theorem rec9087 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(13),[9,10],[42],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[788]? = some (⟨190,(13),[9,10],[42],693⟩) from rfl))
private theorem rec9094 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(14),[9,10],[42],695⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[795]? = some (⟨190,(14),[9,10],[42],695⟩) from rfl))
private theorem rec9101 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(15),[9,10],[42],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[802]? = some (⟨190,(15),[9,10],[42],692⟩) from rfl))
private theorem rec9108 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(16),[9,10],[42],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[809]? = some (⟨190,(16),[9,10],[42],696⟩) from rfl))
private theorem rec9115 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(17),[9,10],[42],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[816]? = some (⟨190,(17),[9,10],[42],696⟩) from rfl))
private theorem rec9122 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(18),[9,10],[42],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[823]? = some (⟨190,(18),[9,10],[42],696⟩) from rfl))
private theorem rec9129 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(19),[9,10],[42],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[830]? = some (⟨190,(19),[9,10],[42],696⟩) from rfl))
private theorem rec9136 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(20),[9,10],[42],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[837]? = some (⟨190,(20),[9,10],[42],692⟩) from rfl))
private theorem rec9143 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(21),[9,10],[42],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[844]? = some (⟨190,(21),[9,10],[42],693⟩) from rfl))
private theorem rec9150 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(22),[9,10],[42],694⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[851]? = some (⟨190,(22),[9,10],[42],694⟩) from rfl))
private theorem rec9157 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(23),[9,10],[42],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[858]? = some (⟨190,(23),[9,10],[42],693⟩) from rfl))
private theorem rec9164 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 190 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(24),[9,10],[42],695⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[865]? = some (⟨190,(24),[9,10],[42],695⟩) from rfl))
private theorem rec9171 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(0),[9],[42],1315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[872]? = some (⟨192,(0),[9],[42],1315⟩) from rfl))
private theorem rec9179 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(1),[9],[42],1316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[880]? = some (⟨192,(1),[9],[42],1316⟩) from rfl))
private theorem rec9187 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(2),[9],[42],1315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[888]? = some (⟨192,(2),[9],[42],1315⟩) from rfl))
private theorem rec9195 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(3),[9],[42],1317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[896]? = some (⟨192,(3),[9],[42],1317⟩) from rfl))
private theorem rec9203 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(4),[9],[42],1318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[904]? = some (⟨192,(4),[9],[42],1318⟩) from rfl))
private theorem rec9211 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(5),[9],[42],1315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[912]? = some (⟨192,(5),[9],[42],1315⟩) from rfl))
private theorem rec9219 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(6),[9],[42],1316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[920]? = some (⟨192,(6),[9],[42],1316⟩) from rfl))
private theorem rec9227 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(7),[9],[42],1315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[928]? = some (⟨192,(7),[9],[42],1315⟩) from rfl))
private theorem rec9235 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(8),[9],[42],1317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[936]? = some (⟨192,(8),[9],[42],1317⟩) from rfl))
private theorem rec9243 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(9),[9],[42],1318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[944]? = some (⟨192,(9),[9],[42],1318⟩) from rfl))
private theorem rec9251 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(10),[9],[42],1319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[952]? = some (⟨192,(10),[9],[42],1319⟩) from rfl))
private theorem rec9259 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(11),[9],[42],1319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[960]? = some (⟨192,(11),[9],[42],1319⟩) from rfl))
private theorem rec9267 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(12),[9],[42],1319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[968]? = some (⟨192,(12),[9],[42],1319⟩) from rfl))
private theorem rec9275 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(13),[9],[42],1319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[976]? = some (⟨192,(13),[9],[42],1319⟩) from rfl))
private theorem rec9283 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(14),[9],[42],1318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[984]? = some (⟨192,(14),[9],[42],1318⟩) from rfl))
private theorem rec9291 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(15),[9],[42],1320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[992]? = some (⟨192,(15),[9],[42],1320⟩) from rfl))
private theorem rec9299 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(16),[9],[42],1320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1000]? = some (⟨192,(16),[9],[42],1320⟩) from rfl))
private theorem rec9307 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(17),[9],[42],1320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1008]? = some (⟨192,(17),[9],[42],1320⟩) from rfl))
private theorem rec9315 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(18),[9],[42],1320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1016]? = some (⟨192,(18),[9],[42],1320⟩) from rfl))
private theorem rec9323 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(19),[9],[42],1320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1024]? = some (⟨192,(19),[9],[42],1320⟩) from rfl))
private theorem rec9331 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(20),[9],[42],1321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1032]? = some (⟨192,(20),[9],[42],1321⟩) from rfl))
private theorem rec9339 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(21),[9],[42],1321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1040]? = some (⟨192,(21),[9],[42],1321⟩) from rfl))
private theorem rec9347 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(22),[9],[42],1321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1048]? = some (⟨192,(22),[9],[42],1321⟩) from rfl))
private theorem rec9355 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(23),[9],[42],1321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1056]? = some (⟨192,(23),[9],[42],1321⟩) from rfl))
private theorem rec9363 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(24),[9],[42],1321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1064]? = some (⟨192,(24),[9],[42],1321⟩) from rfl))
private theorem rec9371 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(0),[9,10],[42],697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1072]? = some (⟨195,(0),[9,10],[42],697⟩) from rfl))
private theorem rec9378 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(1),[9,10],[42],697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1079]? = some (⟨195,(1),[9,10],[42],697⟩) from rfl))
private theorem rec9385 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(2),[9,10],[42],698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1086]? = some (⟨195,(2),[9,10],[42],698⟩) from rfl))
private theorem rec9392 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(3),[9,10],[42],698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1093]? = some (⟨195,(3),[9,10],[42],698⟩) from rfl))
private theorem rec9399 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(4),[9,10],[42],699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1100]? = some (⟨195,(4),[9,10],[42],699⟩) from rfl))
private theorem rec9406 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(5),[9,10],[42],700⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1107]? = some (⟨195,(5),[9,10],[42],700⟩) from rfl))
private theorem rec9413 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(6),[9,10],[42],699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1114]? = some (⟨195,(6),[9,10],[42],699⟩) from rfl))
private theorem rec9420 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(7),[9,10],[42],701⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1121]? = some (⟨195,(7),[9,10],[42],701⟩) from rfl))
private theorem rec9427 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(8),[9,10],[42],702⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1128]? = some (⟨195,(8),[9,10],[42],702⟩) from rfl))
private theorem rec9434 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 195 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(9),[9,10],[42],703⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1135]? = some (⟨195,(9),[9,10],[42],703⟩) from rfl))
private theorem rec9441 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(0),[9],[42],1322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1142]? = some (⟨197,(0),[9],[42],1322⟩) from rfl))
private theorem rec9449 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(1),[9],[42],1323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1150]? = some (⟨197,(1),[9],[42],1323⟩) from rfl))
private theorem rec9457 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(2),[9],[42],1322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1158]? = some (⟨197,(2),[9],[42],1322⟩) from rfl))
private theorem rec9465 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(3),[9],[42],1324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1166]? = some (⟨197,(3),[9],[42],1324⟩) from rfl))
private theorem rec9473 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(4),[9],[42],1325⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1174]? = some (⟨197,(4),[9],[42],1325⟩) from rfl))
private theorem rec9481 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(5),[9],[42],1322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1182]? = some (⟨197,(5),[9],[42],1322⟩) from rfl))
private theorem rec9489 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(6),[9],[42],1323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1190]? = some (⟨197,(6),[9],[42],1323⟩) from rfl))
private theorem rec9497 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(7),[9],[42],1322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1198]? = some (⟨197,(7),[9],[42],1322⟩) from rfl))
private theorem rec9505 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(8),[9],[42],1324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1206]? = some (⟨197,(8),[9],[42],1324⟩) from rfl))
private theorem rec9513 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(9),[9],[42],1325⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1214]? = some (⟨197,(9),[9],[42],1325⟩) from rfl))
private theorem rec9521 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(10),[9],[42],1326⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[3]? = some (⟨197,(10),[9],[42],1326⟩) from rfl))
private theorem rec9529 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(11),[9],[42],1326⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[11]? = some (⟨197,(11),[9],[42],1326⟩) from rfl))
private theorem rec9537 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(12),[9],[42],1326⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[19]? = some (⟨197,(12),[9],[42],1326⟩) from rfl))
private theorem rec9545 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(13),[9],[42],1326⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[27]? = some (⟨197,(13),[9],[42],1326⟩) from rfl))
private theorem rec9553 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(14),[9],[42],1325⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[35]? = some (⟨197,(14),[9],[42],1325⟩) from rfl))
private theorem rec9561 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(15),[9],[42],1327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[43]? = some (⟨197,(15),[9],[42],1327⟩) from rfl))
private theorem rec9569 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(16),[9],[42],1327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[51]? = some (⟨197,(16),[9],[42],1327⟩) from rfl))
private theorem rec9577 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(17),[9],[42],1327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[59]? = some (⟨197,(17),[9],[42],1327⟩) from rfl))
private theorem rec9585 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(18),[9],[42],1327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[67]? = some (⟨197,(18),[9],[42],1327⟩) from rfl))
private theorem rec9593 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(19),[9],[42],1327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[75]? = some (⟨197,(19),[9],[42],1327⟩) from rfl))
private theorem rec9601 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(20),[9],[42],1328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[83]? = some (⟨197,(20),[9],[42],1328⟩) from rfl))
private theorem rec9609 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(21),[9],[42],1328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[91]? = some (⟨197,(21),[9],[42],1328⟩) from rfl))
private theorem rec9617 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(22),[9],[42],1328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[99]? = some (⟨197,(22),[9],[42],1328⟩) from rfl))
private theorem rec9625 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(23),[9],[42],1328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[107]? = some (⟨197,(23),[9],[42],1328⟩) from rfl))
private theorem rec9633 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(24),[9],[42],1328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[115]? = some (⟨197,(24),[9],[42],1328⟩) from rfl))
private theorem rec9641 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(0),[9,10],[42],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[123]? = some (⟨200,(0),[9,10],[42],704⟩) from rfl))
private theorem rec9648 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(1),[9,10],[42],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[130]? = some (⟨200,(1),[9,10],[42],704⟩) from rfl))
private theorem rec9655 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(2),[9,10],[42],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[137]? = some (⟨200,(2),[9,10],[42],704⟩) from rfl))
private theorem rec9662 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(3),[9,10],[42],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[144]? = some (⟨200,(3),[9,10],[42],704⟩) from rfl))
private theorem rec9669 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(4),[9,10],[42],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[151]? = some (⟨200,(4),[9,10],[42],704⟩) from rfl))
private theorem rec9676 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(5),[9,10],[42],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[158]? = some (⟨200,(5),[9,10],[42],705⟩) from rfl))
private theorem rec9683 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(6),[9,10],[42],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[165]? = some (⟨200,(6),[9,10],[42],705⟩) from rfl))
private theorem rec9690 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(7),[9,10],[42],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[172]? = some (⟨200,(7),[9,10],[42],705⟩) from rfl))
private theorem rec9697 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(8),[9,10],[42],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[179]? = some (⟨200,(8),[9,10],[42],705⟩) from rfl))
private theorem rec9704 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(9),[9,10],[42],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[186]? = some (⟨200,(9),[9,10],[42],705⟩) from rfl))
private theorem rec9711 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(10),[9,10],[42],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[193]? = some (⟨200,(10),[9,10],[42],706⟩) from rfl))
private theorem rec9718 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(11),[9,10],[42],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[200]? = some (⟨200,(11),[9,10],[42],707⟩) from rfl))
private theorem rec9725 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(12),[9,10],[42],708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[207]? = some (⟨200,(12),[9,10],[42],708⟩) from rfl))
private theorem rec9732 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(13),[9,10],[42],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[214]? = some (⟨200,(13),[9,10],[42],707⟩) from rfl))
private theorem rec9739 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(14),[9,10],[42],709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[221]? = some (⟨200,(14),[9,10],[42],709⟩) from rfl))
private theorem rec9746 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(15),[9,10],[42],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[228]? = some (⟨200,(15),[9,10],[42],706⟩) from rfl))
private theorem rec9753 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(16),[9,10],[42],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[235]? = some (⟨200,(16),[9,10],[42],710⟩) from rfl))
private theorem rec9760 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(17),[9,10],[42],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[242]? = some (⟨200,(17),[9,10],[42],710⟩) from rfl))
private theorem rec9767 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(18),[9,10],[42],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[249]? = some (⟨200,(18),[9,10],[42],710⟩) from rfl))
private theorem rec9774 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(19),[9,10],[42],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[256]? = some (⟨200,(19),[9,10],[42],710⟩) from rfl))
private theorem rec9781 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(20),[9,10],[42],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[263]? = some (⟨200,(20),[9,10],[42],706⟩) from rfl))
private theorem rec9788 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(21),[9,10],[42],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[270]? = some (⟨200,(21),[9,10],[42],707⟩) from rfl))
private theorem rec9795 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(22),[9,10],[42],708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[277]? = some (⟨200,(22),[9,10],[42],708⟩) from rfl))
private theorem rec9802 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(23),[9,10],[42],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[284]? = some (⟨200,(23),[9,10],[42],707⟩) from rfl))
private theorem rec9809 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 200 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(24),[9,10],[42],709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[291]? = some (⟨200,(24),[9,10],[42],709⟩) from rfl))
private theorem rec9816 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(0),[9],[42],1329⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[298]? = some (⟨202,(0),[9],[42],1329⟩) from rfl))
private theorem rec9824 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(1),[9],[42],1330⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[306]? = some (⟨202,(1),[9],[42],1330⟩) from rfl))
private theorem rec9832 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(2),[9],[42],1329⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[314]? = some (⟨202,(2),[9],[42],1329⟩) from rfl))
private theorem rec9840 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(3),[9],[42],1331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[322]? = some (⟨202,(3),[9],[42],1331⟩) from rfl))
private theorem rec9848 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(4),[9],[42],1332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[330]? = some (⟨202,(4),[9],[42],1332⟩) from rfl))
private theorem rec9856 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(5),[9],[42],1329⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[338]? = some (⟨202,(5),[9],[42],1329⟩) from rfl))
private theorem rec9864 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(6),[9],[42],1330⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[346]? = some (⟨202,(6),[9],[42],1330⟩) from rfl))
private theorem rec9872 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(7),[9],[42],1329⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[354]? = some (⟨202,(7),[9],[42],1329⟩) from rfl))
private theorem rec9880 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(8),[9],[42],1331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[362]? = some (⟨202,(8),[9],[42],1331⟩) from rfl))
private theorem rec9888 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(9),[9],[42],1332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[370]? = some (⟨202,(9),[9],[42],1332⟩) from rfl))
private theorem rec9896 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(10),[9],[42],1333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[378]? = some (⟨202,(10),[9],[42],1333⟩) from rfl))
private theorem rec9904 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(11),[9],[42],1333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[386]? = some (⟨202,(11),[9],[42],1333⟩) from rfl))
private theorem rec9912 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(12),[9],[42],1333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[394]? = some (⟨202,(12),[9],[42],1333⟩) from rfl))
private theorem rec9920 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(13),[9],[42],1333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[402]? = some (⟨202,(13),[9],[42],1333⟩) from rfl))
private theorem rec9928 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(14),[9],[42],1332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[410]? = some (⟨202,(14),[9],[42],1332⟩) from rfl))
private theorem rec9936 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(15),[9],[42],1334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[418]? = some (⟨202,(15),[9],[42],1334⟩) from rfl))
private theorem rec9944 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(16),[9],[42],1334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[426]? = some (⟨202,(16),[9],[42],1334⟩) from rfl))
private theorem rec9952 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(17),[9],[42],1334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[434]? = some (⟨202,(17),[9],[42],1334⟩) from rfl))
private theorem rec9960 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(18),[9],[42],1334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[442]? = some (⟨202,(18),[9],[42],1334⟩) from rfl))
private theorem rec9968 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(19),[9],[42],1334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[450]? = some (⟨202,(19),[9],[42],1334⟩) from rfl))
private theorem rec9976 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(20),[9],[42],1335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[458]? = some (⟨202,(20),[9],[42],1335⟩) from rfl))
private theorem rec9984 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(21),[9],[42],1335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[466]? = some (⟨202,(21),[9],[42],1335⟩) from rfl))
private theorem rec9992 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(22),[9],[42],1335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[474]? = some (⟨202,(22),[9],[42],1335⟩) from rfl))
private theorem rec10000 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(23),[9],[42],1335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[482]? = some (⟨202,(23),[9],[42],1335⟩) from rfl))
private theorem rec10008 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(24),[9],[42],1335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[490]? = some (⟨202,(24),[9],[42],1335⟩) from rfl))
private theorem rec10016 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(0),[9,10],[42],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[498]? = some (⟨205,(0),[9,10],[42],711⟩) from rfl))
private theorem rec10023 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(1),[9,10],[42],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[505]? = some (⟨205,(1),[9,10],[42],711⟩) from rfl))
private theorem rec10030 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(2),[9,10],[42],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[512]? = some (⟨205,(2),[9,10],[42],711⟩) from rfl))
private theorem rec10036 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(3),[9,10],[42],712⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[518]? = some (⟨205,(3),[9,10],[42],712⟩) from rfl))
private theorem rec10043 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(4),[9,10],[42],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[525]? = some (⟨205,(4),[9,10],[42],711⟩) from rfl))
private theorem rec10050 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(5),[9,10],[42],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[532]? = some (⟨205,(5),[9,10],[42],713⟩) from rfl))
private theorem rec10057 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(6),[9,10],[42],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[539]? = some (⟨205,(6),[9,10],[42],713⟩) from rfl))
private theorem rec10064 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(7),[9,10],[42],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[546]? = some (⟨205,(7),[9,10],[42],713⟩) from rfl))
private theorem rec10070 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(8),[9,10],[42],714⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[552]? = some (⟨205,(8),[9,10],[42],714⟩) from rfl))
private theorem rec10077 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(9),[9,10],[42],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[559]? = some (⟨205,(9),[9,10],[42],713⟩) from rfl))
private theorem rec10084 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(10),[9,10],[42],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[566]? = some (⟨205,(10),[9,10],[42],715⟩) from rfl))
private theorem rec10091 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(11),[9,10],[42],716⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[573]? = some (⟨205,(11),[9,10],[42],716⟩) from rfl))
private theorem rec10098 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(12),[9,10],[42],717⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[580]? = some (⟨205,(12),[9,10],[42],717⟩) from rfl))
private theorem rec10104 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(13),[9,10],[42],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[586]? = some (⟨205,(13),[9,10],[42],718⟩) from rfl))
private theorem rec10111 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(14),[9,10],[42],719⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[593]? = some (⟨205,(14),[9,10],[42],719⟩) from rfl))
private theorem rec10118 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(15),[9,10],[42],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[600]? = some (⟨205,(15),[9,10],[42],715⟩) from rfl))
private theorem rec10125 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(16),[9,10],[42],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[607]? = some (⟨205,(16),[9,10],[42],720⟩) from rfl))
private theorem rec10132 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(17),[9,10],[42],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[614]? = some (⟨205,(17),[9,10],[42],720⟩) from rfl))
private theorem rec10138 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(18),[9,10],[42],721⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[620]? = some (⟨205,(18),[9,10],[42],721⟩) from rfl))
private theorem rec10145 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(19),[9,10],[42],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[627]? = some (⟨205,(19),[9,10],[42],720⟩) from rfl))
private theorem rec10152 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(20),[9,10],[42],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[634]? = some (⟨205,(20),[9,10],[42],715⟩) from rfl))
private theorem rec10159 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(21),[9,10],[42],716⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[641]? = some (⟨205,(21),[9,10],[42],716⟩) from rfl))
private theorem rec10166 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(22),[9,10],[42],717⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[648]? = some (⟨205,(22),[9,10],[42],717⟩) from rfl))
private theorem rec10172 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(23),[9,10],[42],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[654]? = some (⟨205,(23),[9,10],[42],718⟩) from rfl))
private theorem rec10179 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 205 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(24),[9,10],[42],719⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[661]? = some (⟨205,(24),[9,10],[42],719⟩) from rfl))
private theorem rec10186 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(0),[9],[42],1336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[668]? = some (⟨207,(0),[9],[42],1336⟩) from rfl))
private theorem rec10194 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(1),[9],[42],1337⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[676]? = some (⟨207,(1),[9],[42],1337⟩) from rfl))
private theorem rec10202 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(2),[9],[42],1336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[684]? = some (⟨207,(2),[9],[42],1336⟩) from rfl))
private theorem rec10210 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(3),[9],[42],1338⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[692]? = some (⟨207,(3),[9],[42],1338⟩) from rfl))
private theorem rec10218 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(4),[9],[42],1339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[700]? = some (⟨207,(4),[9],[42],1339⟩) from rfl))
private theorem rec10226 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(5),[9],[42],1336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[708]? = some (⟨207,(5),[9],[42],1336⟩) from rfl))
private theorem rec10234 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(6),[9],[42],1337⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[716]? = some (⟨207,(6),[9],[42],1337⟩) from rfl))
private theorem rec10242 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(7),[9],[42],1336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[724]? = some (⟨207,(7),[9],[42],1336⟩) from rfl))
private theorem rec10250 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(8),[9],[42],1338⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[732]? = some (⟨207,(8),[9],[42],1338⟩) from rfl))
private theorem rec10258 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(9),[9],[42],1339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[740]? = some (⟨207,(9),[9],[42],1339⟩) from rfl))
private theorem rec10266 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(10),[9],[42],1340⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[748]? = some (⟨207,(10),[9],[42],1340⟩) from rfl))
private theorem rec10274 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(11),[9],[42],1340⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[756]? = some (⟨207,(11),[9],[42],1340⟩) from rfl))
private theorem rec10282 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(12),[9],[42],1340⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[764]? = some (⟨207,(12),[9],[42],1340⟩) from rfl))
private theorem rec10290 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(13),[9],[42],1340⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[772]? = some (⟨207,(13),[9],[42],1340⟩) from rfl))
private theorem rec10298 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(14),[9],[42],1339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[780]? = some (⟨207,(14),[9],[42],1339⟩) from rfl))
private theorem rec10306 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(15),[9],[42],1341⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[788]? = some (⟨207,(15),[9],[42],1341⟩) from rfl))
private theorem rec10314 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(16),[9],[42],1341⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[796]? = some (⟨207,(16),[9],[42],1341⟩) from rfl))
private theorem rec10322 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(17),[9],[42],1341⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[804]? = some (⟨207,(17),[9],[42],1341⟩) from rfl))
private theorem rec10330 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(18),[9],[42],1341⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[812]? = some (⟨207,(18),[9],[42],1341⟩) from rfl))
private theorem rec10338 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(19),[9],[42],1341⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[820]? = some (⟨207,(19),[9],[42],1341⟩) from rfl))
private theorem rec10346 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(20),[9],[42],1342⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[828]? = some (⟨207,(20),[9],[42],1342⟩) from rfl))
private theorem rec10354 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(21),[9],[42],1342⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[836]? = some (⟨207,(21),[9],[42],1342⟩) from rfl))
private theorem rec10362 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(22),[9],[42],1342⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[844]? = some (⟨207,(22),[9],[42],1342⟩) from rfl))
private theorem rec10370 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(23),[9],[42],1342⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[852]? = some (⟨207,(23),[9],[42],1342⟩) from rfl))
private theorem rec10378 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(24),[9],[42],1342⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[860]? = some (⟨207,(24),[9],[42],1342⟩) from rfl))
private theorem rec10384 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(0),[9,10],[42],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[866]? = some (⟨210,(0),[9,10],[42],722⟩) from rfl))
private theorem rec10388 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(1),[9,10],[42],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[870]? = some (⟨210,(1),[9,10],[42],723⟩) from rfl))
private theorem rec10392 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(2),[9,10],[42],724⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[874]? = some (⟨210,(2),[9,10],[42],724⟩) from rfl))
private theorem rec10396 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(3),[9,10],[42],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[878]? = some (⟨210,(3),[9,10],[42],725⟩) from rfl))
private theorem rec10400 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(4),[9,10],[42],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[882]? = some (⟨210,(4),[9,10],[42],722⟩) from rfl))
private theorem rec10404 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(5),[9,10],[42],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[886]? = some (⟨210,(5),[9,10],[42],723⟩) from rfl))
private theorem rec10408 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(6),[9,10],[42],726⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[890]? = some (⟨210,(6),[9,10],[42],726⟩) from rfl))
private theorem rec10412 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(7),[9,10],[42],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[894]? = some (⟨210,(7),[9,10],[42],725⟩) from rfl))
private theorem rec10416 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(8),[9,10],[42],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[898]? = some (⟨210,(8),[9,10],[42],722⟩) from rfl))
private theorem rec10420 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(9),[9,10],[42],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[902]? = some (⟨210,(9),[9,10],[42],723⟩) from rfl))
private theorem rec10424 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(10),[9,10],[42],724⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[906]? = some (⟨210,(10),[9,10],[42],724⟩) from rfl))
private theorem rec10428 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(11),[9,10],[42],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[910]? = some (⟨210,(11),[9,10],[42],725⟩) from rfl))
private theorem rec10432 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(12),[9,10],[42],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[914]? = some (⟨210,(12),[9,10],[42],722⟩) from rfl))
private theorem rec10436 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(13),[9,10],[42],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[918]? = some (⟨210,(13),[9,10],[42],723⟩) from rfl))
private theorem rec10440 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(14),[9,10],[42],727⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[922]? = some (⟨210,(14),[9,10],[42],727⟩) from rfl))
private theorem rec10444 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 210 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(15),[9,10],[42],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[926]? = some (⟨210,(15),[9,10],[42],725⟩) from rfl))
private theorem rec10450 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(0),[9],[42],1343⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[932]? = some (⟨213,(0),[9],[42],1343⟩) from rfl))
private theorem rec10458 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(1),[9],[42],1344⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[940]? = some (⟨213,(1),[9],[42],1344⟩) from rfl))
private theorem rec10466 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(2),[9],[42],1343⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[948]? = some (⟨213,(2),[9],[42],1343⟩) from rfl))
private theorem rec10474 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(3),[9],[42],1345⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[956]? = some (⟨213,(3),[9],[42],1345⟩) from rfl))
private theorem rec10482 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(4),[9],[42],1346⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[964]? = some (⟨213,(4),[9],[42],1346⟩) from rfl))
private theorem rec10490 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(5),[9],[42],1346⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[972]? = some (⟨213,(5),[9],[42],1346⟩) from rfl))
private theorem rec10501 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(6),[9],[42],1346⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[983]? = some (⟨213,(6),[9],[42],1346⟩) from rfl))
private theorem rec10509 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(7),[9],[42],1346⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[991]? = some (⟨213,(7),[9],[42],1346⟩) from rfl))
private theorem rec10517 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(8),[9],[42],1347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[999]? = some (⟨213,(8),[9],[42],1347⟩) from rfl))
private theorem rec10525 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(9),[9],[42],1347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1007]? = some (⟨213,(9),[9],[42],1347⟩) from rfl))
private theorem rec10533 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(10),[9],[42],1347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1015]? = some (⟨213,(10),[9],[42],1347⟩) from rfl))
private theorem rec10541 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(11),[9],[42],1347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1023]? = some (⟨213,(11),[9],[42],1347⟩) from rfl))
private theorem rec10549 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(12),[9],[42],1348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1031]? = some (⟨213,(12),[9],[42],1348⟩) from rfl))
private theorem rec10557 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(13),[9],[42],1348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1039]? = some (⟨213,(13),[9],[42],1348⟩) from rfl))
private theorem rec10565 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(14),[9],[42],1348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1047]? = some (⟨213,(14),[9],[42],1348⟩) from rfl))
private theorem rec10573 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(15),[9],[42],1348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1055]? = some (⟨213,(15),[9],[42],1348⟩) from rfl))
private theorem rec10579 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(0),[9,10],[42],728⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1061]? = some (⟨215,(0),[9,10],[42],728⟩) from rfl))
private theorem rec10583 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(1),[9,10],[42],729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1065]? = some (⟨215,(1),[9,10],[42],729⟩) from rfl))
private theorem rec10587 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(2),[9,10],[42],730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1069]? = some (⟨215,(2),[9,10],[42],730⟩) from rfl))
private theorem rec10591 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(3),[9,10],[42],731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1073]? = some (⟨215,(3),[9,10],[42],731⟩) from rfl))
private theorem rec10595 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(4),[9,10],[42],728⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1077]? = some (⟨215,(4),[9,10],[42],728⟩) from rfl))
private theorem rec10599 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(5),[9,10],[42],729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1081]? = some (⟨215,(5),[9,10],[42],729⟩) from rfl))
private theorem rec10603 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(6),[9,10],[42],732⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1085]? = some (⟨215,(6),[9,10],[42],732⟩) from rfl))
private theorem rec10607 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(7),[9,10],[42],731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1089]? = some (⟨215,(7),[9,10],[42],731⟩) from rfl))
private theorem rec10611 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(8),[9,10],[42],728⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1093]? = some (⟨215,(8),[9,10],[42],728⟩) from rfl))
private theorem rec10615 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(9),[9,10],[42],729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1097]? = some (⟨215,(9),[9,10],[42],729⟩) from rfl))
private theorem rec10619 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(10),[9,10],[42],730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1101]? = some (⟨215,(10),[9,10],[42],730⟩) from rfl))
private theorem rec10623 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(11),[9,10],[42],731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1105]? = some (⟨215,(11),[9,10],[42],731⟩) from rfl))
private theorem rec10627 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(12),[9,10],[42],728⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1109]? = some (⟨215,(12),[9,10],[42],728⟩) from rfl))
private theorem rec10631 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(13),[9,10],[42],729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1113]? = some (⟨215,(13),[9,10],[42],729⟩) from rfl))
private theorem rec10635 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(14),[9,10],[42],733⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1117]? = some (⟨215,(14),[9,10],[42],733⟩) from rfl))
private theorem rec10639 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 215 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(15),[9,10],[42],731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1121]? = some (⟨215,(15),[9,10],[42],731⟩) from rfl))
private theorem rec10645 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 218 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(0),[9],[42],1349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1127]? = some (⟨218,(0),[9],[42],1349⟩) from rfl))
private theorem rec10653 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 218 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(1),[9],[42],1350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1135]? = some (⟨218,(1),[9],[42],1350⟩) from rfl))
private theorem rec10661 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 218 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(2),[9],[42],1351⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1143]? = some (⟨218,(2),[9],[42],1351⟩) from rfl))
private theorem rec10669 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 218 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(3),[9],[42],1352⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1151]? = some (⟨218,(3),[9],[42],1352⟩) from rfl))
private theorem rec10676 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(0),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1158]? = some (⟨220,(0),[9,10],[42],3⟩) from rfl))
private theorem rec10680 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(1),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1162]? = some (⟨220,(1),[9,10],[42],3⟩) from rfl))
private theorem rec10684 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(2),[9,10],[42],734⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1166]? = some (⟨220,(2),[9,10],[42],734⟩) from rfl))
private theorem rec10688 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(3),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1170]? = some (⟨220,(3),[9,10],[42],29⟩) from rfl))
private theorem rec10692 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(4),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1174]? = some (⟨220,(4),[9,10],[42],3⟩) from rfl))
private theorem rec10696 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(5),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1178]? = some (⟨220,(5),[9,10],[42],3⟩) from rfl))
private theorem rec10700 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(6),[9,10],[42],511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1182]? = some (⟨220,(6),[9,10],[42],511⟩) from rfl))
private theorem rec10704 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(7),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1186]? = some (⟨220,(7),[9,10],[42],29⟩) from rfl))
private theorem rec10708 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(8),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1190]? = some (⟨220,(8),[9,10],[42],3⟩) from rfl))
private theorem rec10712 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(9),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1194]? = some (⟨220,(9),[9,10],[42],3⟩) from rfl))
private theorem rec10716 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(10),[9,10],[42],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1198]? = some (⟨220,(10),[9,10],[42],512⟩) from rfl))
private theorem rec10720 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(11),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1202]? = some (⟨220,(11),[9,10],[42],29⟩) from rfl))
private theorem rec10724 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(12),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1206]? = some (⟨220,(12),[9,10],[42],3⟩) from rfl))
private theorem rec10728 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(13),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1210]? = some (⟨220,(13),[9,10],[42],3⟩) from rfl))
private theorem rec10732 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(14),[9,10],[42],513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[3]? = some (⟨220,(14),[9,10],[42],513⟩) from rfl))
private theorem rec10736 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(15),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[7]? = some (⟨220,(15),[9,10],[42],29⟩) from rfl))
private theorem rec10740 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(16),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[11]? = some (⟨220,(16),[9,10],[42],3⟩) from rfl))
private theorem rec10744 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(17),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[15]? = some (⟨220,(17),[9,10],[42],3⟩) from rfl))
private theorem rec10748 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(18),[9,10],[42],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[19]? = some (⟨220,(18),[9,10],[42],514⟩) from rfl))
private theorem rec10752 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 220 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(19),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[23]? = some (⟨220,(19),[9,10],[42],29⟩) from rfl))
private theorem rec10758 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(0),[9],[42],1353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[29]? = some (⟨221,(0),[9],[42],1353⟩) from rfl))
private theorem rec10766 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(1),[9],[42],1353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[37]? = some (⟨221,(1),[9],[42],1353⟩) from rfl))
private theorem rec10774 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(2),[9],[42],1354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[45]? = some (⟨221,(2),[9],[42],1354⟩) from rfl))
private theorem rec10782 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(3),[9],[42],1355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[53]? = some (⟨221,(3),[9],[42],1355⟩) from rfl))
private theorem rec10790 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(4),[9],[42],1356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[61]? = some (⟨221,(4),[9],[42],1356⟩) from rfl))
private theorem rec10798 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(5),[9],[42],1353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[69]? = some (⟨221,(5),[9],[42],1353⟩) from rfl))
private theorem rec10806 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(6),[9],[42],1353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[77]? = some (⟨221,(6),[9],[42],1353⟩) from rfl))
private theorem rec10814 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(7),[9],[42],1354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[85]? = some (⟨221,(7),[9],[42],1354⟩) from rfl))
private theorem rec10822 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(8),[9],[42],1355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[93]? = some (⟨221,(8),[9],[42],1355⟩) from rfl))
private theorem rec10830 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(9),[9],[42],1356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[101]? = some (⟨221,(9),[9],[42],1356⟩) from rfl))
private theorem rec10838 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(10),[9],[42],1357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[109]? = some (⟨221,(10),[9],[42],1357⟩) from rfl))
private theorem rec10846 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(11),[9],[42],1357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[117]? = some (⟨221,(11),[9],[42],1357⟩) from rfl))
private theorem rec10854 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(12),[9],[42],1358⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[125]? = some (⟨221,(12),[9],[42],1358⟩) from rfl))
private theorem rec10862 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(13),[9],[42],1355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[133]? = some (⟨221,(13),[9],[42],1355⟩) from rfl))
private theorem rec10870 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(14),[9],[42],1356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[141]? = some (⟨221,(14),[9],[42],1356⟩) from rfl))
private theorem rec10878 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(15),[9],[42],1359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[149]? = some (⟨221,(15),[9],[42],1359⟩) from rfl))
private theorem rec10886 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(16),[9],[42],1359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[157]? = some (⟨221,(16),[9],[42],1359⟩) from rfl))
private theorem rec10894 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(17),[9],[42],1359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[165]? = some (⟨221,(17),[9],[42],1359⟩) from rfl))
private theorem rec10902 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(18),[9],[42],1359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[173]? = some (⟨221,(18),[9],[42],1359⟩) from rfl))
private theorem rec10911 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(19),[9],[42],1359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[182]? = some (⟨221,(19),[9],[42],1359⟩) from rfl))
private theorem rec10919 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(20),[9],[42],1360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[190]? = some (⟨221,(20),[9],[42],1360⟩) from rfl))
private theorem rec10927 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(21),[9],[42],1360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[198]? = some (⟨221,(21),[9],[42],1360⟩) from rfl))
private theorem rec10935 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(22),[9],[42],1360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[206]? = some (⟨221,(22),[9],[42],1360⟩) from rfl))
private theorem rec10943 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(23),[9],[42],1355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[214]? = some (⟨221,(23),[9],[42],1355⟩) from rfl))
private theorem rec10952 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(24),[9],[42],1360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[223]? = some (⟨221,(24),[9],[42],1360⟩) from rfl))
private theorem rec10962 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(0),[9,10],[42],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[233]? = some (⟨222,(0),[9,10],[42],736⟩) from rfl))
private theorem rec10969 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(1),[9,10],[42],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[240]? = some (⟨222,(1),[9,10],[42],736⟩) from rfl))
private theorem rec10976 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(2),[9],[42],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[247]? = some (⟨222,(2),[9],[42],736⟩) from rfl))
private theorem rec10984 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(3),[9,10],[42],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[255]? = some (⟨222,(3),[9,10],[42],736⟩) from rfl))
private theorem rec10990 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(4),[9,10],[42],525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[261]? = some (⟨222,(4),[9,10],[42],525⟩) from rfl))
private theorem rec10997 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(5),[9,10],[42],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[268]? = some (⟨222,(5),[9,10],[42],735⟩) from rfl))
private theorem rec11006 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(6),[9,10],[42],740⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[277]? = some (⟨222,(6),[9,10],[42],740⟩) from rfl))
private theorem rec11013 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(7),[9],[42],740⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[284]? = some (⟨222,(7),[9],[42],740⟩) from rfl))
private theorem rec11021 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(8),[9,10],[42],740⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[292]? = some (⟨222,(8),[9,10],[42],740⟩) from rfl))
private theorem rec11027 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(9),[9,10],[42],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[298]? = some (⟨222,(9),[9,10],[42],528⟩) from rfl))
private theorem rec11035 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(10),[9],[42],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[306]? = some (⟨222,(10),[9],[42],735⟩) from rfl))
private theorem rec11044 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(11),[9],[42],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[315]? = some (⟨222,(11),[9],[42],738⟩) from rfl))
private theorem rec11054 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(12),[9],[42],1644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[325]? = some (⟨222,(12),[9],[42],1644⟩) from rfl))
private theorem rec11063 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(13),[9],[42],1362⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[334]? = some (⟨222,(13),[9],[42],1362⟩) from rfl))
private theorem rec11070 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(14),[9,10],[42],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[341]? = some (⟨222,(14),[9,10],[42],531⟩) from rfl))
private theorem rec11077 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(15),[9,10],[42],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[348]? = some (⟨222,(15),[9,10],[42],735⟩) from rfl))
private theorem rec11084 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(16),[9,10],[42],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[355]? = some (⟨222,(16),[9,10],[42],738⟩) from rfl))
private theorem rec11091 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(17),[9],[42],1645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[362]? = some (⟨222,(17),[9],[42],1645⟩) from rfl))
private theorem rec11099 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(18),[9,10],[42],746⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[370]? = some (⟨222,(18),[9,10],[42],746⟩) from rfl))
private theorem rec11105 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(19),[9,10],[42],534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[376]? = some (⟨222,(19),[9,10],[42],534⟩) from rfl))
private theorem rec11111 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(20),[9,10],[42],535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[382]? = some (⟨222,(20),[9,10],[42],535⟩) from rfl))
private theorem rec11117 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(21),[9,10],[42],536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[388]? = some (⟨222,(21),[9,10],[42],536⟩) from rfl))
private theorem rec11123 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(22),[9,10],[42],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[394]? = some (⟨222,(22),[9,10],[42],537⟩) from rfl))
private theorem rec11129 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(23),[9,10],[42],538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[400]? = some (⟨222,(23),[9,10],[42],538⟩) from rfl))
private theorem rec11136 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(24),[9,10],[42],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[407]? = some (⟨222,(24),[9,10],[42],531⟩) from rfl))
private theorem rec11142 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(0),[9,10],[42],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[413]? = some (⟨224,(0),[9,10],[42],539⟩) from rfl))
private theorem rec11148 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(1),[9,10],[42],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[419]? = some (⟨224,(1),[9,10],[42],539⟩) from rfl))
private theorem rec11154 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(2),[9,10],[42],540⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[425]? = some (⟨224,(2),[9,10],[42],540⟩) from rfl))
private theorem rec11160 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(3),[9,10],[42],541⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[431]? = some (⟨224,(3),[9,10],[42],541⟩) from rfl))
private theorem rec11166 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(4),[9,10],[42],542⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[437]? = some (⟨224,(4),[9,10],[42],542⟩) from rfl))
private theorem rec11173 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(5),[9],[42],1363⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[444]? = some (⟨224,(5),[9],[42],1363⟩) from rfl))
private theorem rec11181 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(6),[9],[42],1363⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[452]? = some (⟨224,(6),[9],[42],1363⟩) from rfl))
private theorem rec11189 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(7),[9],[42],1364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[460]? = some (⟨224,(7),[9],[42],1364⟩) from rfl))
private theorem rec11197 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(8),[9],[42],1355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[468]? = some (⟨224,(8),[9],[42],1355⟩) from rfl))
private theorem rec11205 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(9),[9],[42],1356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[476]? = some (⟨224,(9),[9],[42],1356⟩) from rfl))
private theorem rec11213 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(10),[9],[42],1365⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[484]? = some (⟨224,(10),[9],[42],1365⟩) from rfl))
private theorem rec11221 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(11),[9],[42],1365⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[492]? = some (⟨224,(11),[9],[42],1365⟩) from rfl))
private theorem rec11229 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(12),[9],[42],1364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[500]? = some (⟨224,(12),[9],[42],1364⟩) from rfl))
private theorem rec11237 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(13),[9],[42],1355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[508]? = some (⟨224,(13),[9],[42],1355⟩) from rfl))
private theorem rec11245 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(14),[9],[42],1356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[516]? = some (⟨224,(14),[9],[42],1356⟩) from rfl))
private theorem rec11253 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(15),[9],[42],1366⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[524]? = some (⟨224,(15),[9],[42],1366⟩) from rfl))
private theorem rec11261 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(16),[9],[42],1366⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[532]? = some (⟨224,(16),[9],[42],1366⟩) from rfl))
private theorem rec11269 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(17),[9],[42],1364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[540]? = some (⟨224,(17),[9],[42],1364⟩) from rfl))
private theorem rec11277 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(18),[9],[42],1355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[548]? = some (⟨224,(18),[9],[42],1355⟩) from rfl))
private theorem rec11285 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(19),[9],[42],1356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[556]? = some (⟨224,(19),[9],[42],1356⟩) from rfl))
private theorem rec11293 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(20),[9],[42],1367⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[564]? = some (⟨224,(20),[9],[42],1367⟩) from rfl))
private theorem rec11301 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(21),[9],[42],1367⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[572]? = some (⟨224,(21),[9],[42],1367⟩) from rfl))
private theorem rec11309 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(22),[9],[42],1367⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[580]? = some (⟨224,(22),[9],[42],1367⟩) from rfl))
private theorem rec11317 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(23),[9],[42],1355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[588]? = some (⟨224,(23),[9],[42],1355⟩) from rfl))
private theorem rec11325 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(24),[9],[42],1356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[596]? = some (⟨224,(24),[9],[42],1356⟩) from rfl))
private theorem rec11332 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(0),[9,10],[42],747⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[603]? = some (⟨225,(0),[9,10],[42],747⟩) from rfl))
private theorem rec11338 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(1),[9,10],[42],748⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[609]? = some (⟨225,(1),[9,10],[42],748⟩) from rfl))
private theorem rec11345 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(2),[9,10],[42],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[616]? = some (⟨225,(2),[9,10],[42],749⟩) from rfl))
private theorem rec11352 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(3),[9,10],[42],750⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[623]? = some (⟨225,(3),[9,10],[42],750⟩) from rfl))
private theorem rec11359 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(4),[9,10],[42],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[630]? = some (⟨225,(4),[9,10],[42],749⟩) from rfl))
private theorem rec11365 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(5),[9,10],[42],751⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[636]? = some (⟨225,(5),[9,10],[42],751⟩) from rfl))
private theorem rec11371 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(6),[9,10],[42],752⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[642]? = some (⟨225,(6),[9,10],[42],752⟩) from rfl))
private theorem rec11378 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(7),[9],[42],1368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[649]? = some (⟨225,(7),[9],[42],1368⟩) from rfl))
private theorem rec11386 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(8),[9,10],[42],754⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[657]? = some (⟨225,(8),[9,10],[42],754⟩) from rfl))
private theorem rec11393 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(9),[9],[42],1368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[664]? = some (⟨225,(9),[9],[42],1368⟩) from rfl))
private theorem rec11400 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(10),[9,10],[42],755⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[671]? = some (⟨225,(10),[9,10],[42],755⟩) from rfl))
private theorem rec11406 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(11),[9,10],[42],756⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[677]? = some (⟨225,(11),[9,10],[42],756⟩) from rfl))
private theorem rec11413 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(12),[9],[42],1369⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[684]? = some (⟨225,(12),[9],[42],1369⟩) from rfl))
private theorem rec11421 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(13),[9,10],[42],758⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[692]? = some (⟨225,(13),[9,10],[42],758⟩) from rfl))
private theorem rec11428 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(14),[9],[42],1369⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[699]? = some (⟨225,(14),[9],[42],1369⟩) from rfl))
private theorem rec11435 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(15),[9,10],[42],759⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[706]? = some (⟨225,(15),[9,10],[42],759⟩) from rfl))
private theorem rec11441 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(16),[9,10],[42],760⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[712]? = some (⟨225,(16),[9,10],[42],760⟩) from rfl))
private theorem rec11448 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(17),[9],[42],1370⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[719]? = some (⟨225,(17),[9],[42],1370⟩) from rfl))
private theorem rec11456 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(18),[9,10],[42],762⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[727]? = some (⟨225,(18),[9,10],[42],762⟩) from rfl))
private theorem rec11463 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(19),[9],[42],1370⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[734]? = some (⟨225,(19),[9],[42],1370⟩) from rfl))
private theorem rec11470 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(20),[9,10],[42],763⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[741]? = some (⟨225,(20),[9,10],[42],763⟩) from rfl))
private theorem rec11476 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(21),[9,10],[42],764⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[747]? = some (⟨225,(21),[9,10],[42],764⟩) from rfl))
private theorem rec11483 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(22),[9],[42],1367⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[754]? = some (⟨225,(22),[9],[42],1367⟩) from rfl))
private theorem rec11491 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(23),[9,10],[42],765⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[762]? = some (⟨225,(23),[9,10],[42],765⟩) from rfl))
private theorem rec11498 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(24),[9],[42],1367⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[769]? = some (⟨225,(24),[9],[42],1367⟩) from rfl))
private theorem rec11506 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(0),[9,10],[42],766⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[777]? = some (⟨226,(0),[9,10],[42],766⟩) from rfl))
private theorem rec11512 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(1),[9,10],[42],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[783]? = some (⟨226,(1),[9,10],[42],767⟩) from rfl))
private theorem rec11518 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(2),[9,10],[42],768⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[789]? = some (⟨226,(2),[9,10],[42],768⟩) from rfl))
private theorem rec11524 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(3),[9,10],[42],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[795]? = some (⟨226,(3),[9,10],[42],767⟩) from rfl))
private theorem rec11530 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(4),[9,10],[42],769⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[801]? = some (⟨226,(4),[9,10],[42],769⟩) from rfl))
private theorem rec11536 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(5),[9,10],[42],770⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[807]? = some (⟨226,(5),[9,10],[42],770⟩) from rfl))
private theorem rec11542 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(6),[9,10],[42],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[813]? = some (⟨226,(6),[9,10],[42],771⟩) from rfl))
private theorem rec11548 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(7),[9,10],[42],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[819]? = some (⟨226,(7),[9,10],[42],771⟩) from rfl))
private theorem rec11554 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(8),[9,10],[42],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[825]? = some (⟨226,(8),[9,10],[42],772⟩) from rfl))
private theorem rec11560 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 226 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(9),[9,10],[42],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[831]? = some (⟨226,(9),[9,10],[42],772⟩) from rfl))
private theorem rec11566 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(0),[9,10],[42],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[837]? = some (⟨227,(0),[9,10],[42],773⟩) from rfl))
private theorem rec11572 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(1),[9,10],[42],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[843]? = some (⟨227,(1),[9,10],[42],774⟩) from rfl))
private theorem rec11579 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(2),[9],[42],1371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[850]? = some (⟨227,(2),[9],[42],1371⟩) from rfl))
private theorem rec11586 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(3),[9,10],[42],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[857]? = some (⟨227,(3),[9,10],[42],776⟩) from rfl))
private theorem rec11593 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(4),[9],[42],1371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[864]? = some (⟨227,(4),[9],[42],1371⟩) from rfl))
private theorem rec11600 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(5),[9,10],[42],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[871]? = some (⟨227,(5),[9,10],[42],773⟩) from rfl))
private theorem rec11606 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(6),[9,10],[42],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[877]? = some (⟨227,(6),[9,10],[42],774⟩) from rfl))
private theorem rec11613 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(7),[9],[42],1371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[884]? = some (⟨227,(7),[9],[42],1371⟩) from rfl))
private theorem rec11620 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(8),[9,10],[42],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[891]? = some (⟨227,(8),[9,10],[42],776⟩) from rfl))
private theorem rec11627 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(9),[9],[42],1371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[898]? = some (⟨227,(9),[9],[42],1371⟩) from rfl))
private theorem rec11634 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(10),[9,10],[42],777⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[905]? = some (⟨227,(10),[9,10],[42],777⟩) from rfl))
private theorem rec11640 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(11),[9,10],[42],778⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[911]? = some (⟨227,(11),[9,10],[42],778⟩) from rfl))
private theorem rec11647 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(12),[9],[42],1372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[918]? = some (⟨227,(12),[9],[42],1372⟩) from rfl))
private theorem rec11654 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(13),[9,10],[42],780⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[925]? = some (⟨227,(13),[9,10],[42],780⟩) from rfl))
private theorem rec11661 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(14),[9],[42],1372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[932]? = some (⟨227,(14),[9],[42],1372⟩) from rfl))
private theorem rec11668 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(15),[9,10],[42],781⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[939]? = some (⟨227,(15),[9,10],[42],781⟩) from rfl))
private theorem rec11674 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(16),[9,10],[42],782⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[945]? = some (⟨227,(16),[9,10],[42],782⟩) from rfl))
private theorem rec11681 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(17),[9],[42],1373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[952]? = some (⟨227,(17),[9],[42],1373⟩) from rfl))
private theorem rec11688 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(18),[9,10],[42],784⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[959]? = some (⟨227,(18),[9,10],[42],784⟩) from rfl))
private theorem rec11695 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(19),[9],[42],1373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[966]? = some (⟨227,(19),[9],[42],1373⟩) from rfl))
private theorem rec11702 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(20),[9,10],[42],785⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[973]? = some (⟨227,(20),[9,10],[42],785⟩) from rfl))
private theorem rec11708 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(21),[9,10],[42],786⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[979]? = some (⟨227,(21),[9,10],[42],786⟩) from rfl))
private theorem rec11715 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(22),[9],[42],1374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[986]? = some (⟨227,(22),[9],[42],1374⟩) from rfl))
private theorem rec11722 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(23),[9,10],[42],788⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[993]? = some (⟨227,(23),[9,10],[42],788⟩) from rfl))
private theorem rec11729 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(24),[9],[42],1374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1000]? = some (⟨227,(24),[9],[42],1374⟩) from rfl))
private theorem rec11737 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(0),[9,10],[42],789⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1008]? = some (⟨228,(0),[9,10],[42],789⟩) from rfl))
private theorem rec11744 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(1),[9,10],[42],790⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1015]? = some (⟨228,(1),[9,10],[42],790⟩) from rfl))
private theorem rec11754 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(2),[9,10],[42],791⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1025]? = some (⟨228,(2),[9,10],[42],791⟩) from rfl))
private theorem rec11761 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(3),[9,10],[42],792⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1032]? = some (⟨228,(3),[9,10],[42],792⟩) from rfl))
private theorem rec11767 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(4),[9,10],[42],793⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1038]? = some (⟨228,(4),[9,10],[42],793⟩) from rfl))
private theorem rec11773 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(5),[9,10],[42],794⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1044]? = some (⟨228,(5),[9,10],[42],794⟩) from rfl))
private theorem rec11779 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(6),[9,10],[42],795⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1050]? = some (⟨228,(6),[9,10],[42],795⟩) from rfl))
private theorem rec11785 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(7),[9,10],[42],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1056]? = some (⟨228,(7),[9,10],[42],796⟩) from rfl))
private theorem rec11791 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(8),[9,10],[42],797⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1062]? = some (⟨228,(8),[9,10],[42],797⟩) from rfl))
private theorem rec11798 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(9),[9,10],[42],793⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1069]? = some (⟨228,(9),[9,10],[42],793⟩) from rfl))
private theorem rec11804 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(10),[9,10],[42],798⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1075]? = some (⟨228,(10),[9,10],[42],798⟩) from rfl))
private theorem rec11810 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(11),[9,10],[42],799⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1081]? = some (⟨228,(11),[9,10],[42],799⟩) from rfl))
private theorem rec11816 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(12),[9,10],[42],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1087]? = some (⟨228,(12),[9,10],[42],800⟩) from rfl))
private theorem rec11822 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(13),[9,10],[42],801⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1093]? = some (⟨228,(13),[9,10],[42],801⟩) from rfl))
private theorem rec11828 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(14),[9,10],[42],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1099]? = some (⟨228,(14),[9,10],[42],800⟩) from rfl))
private theorem rec11834 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(15),[9,10],[42],802⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1105]? = some (⟨228,(15),[9,10],[42],802⟩) from rfl))
private theorem rec11840 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(16),[9,10],[42],803⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1111]? = some (⟨228,(16),[9,10],[42],803⟩) from rfl))
private theorem rec11846 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(17),[9,10],[42],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1117]? = some (⟨228,(17),[9,10],[42],804⟩) from rfl))
private theorem rec11852 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(18),[9,10],[42],805⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1123]? = some (⟨228,(18),[9,10],[42],805⟩) from rfl))
private theorem rec11858 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(19),[9,10],[42],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1129]? = some (⟨228,(19),[9,10],[42],804⟩) from rfl))
private theorem rec11864 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(20),[9,10],[42],806⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1135]? = some (⟨228,(20),[9,10],[42],806⟩) from rfl))
private theorem rec11870 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(21),[9,10],[42],807⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1141]? = some (⟨228,(21),[9,10],[42],807⟩) from rfl))
private theorem rec11876 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(22),[9,10],[42],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1147]? = some (⟨228,(22),[9,10],[42],808⟩) from rfl))
private theorem rec11882 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(23),[9,10],[42],809⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1153]? = some (⟨228,(23),[9,10],[42],809⟩) from rfl))
private theorem rec11888 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 228 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(24),[9,10],[42],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1159]? = some (⟨228,(24),[9,10],[42],808⟩) from rfl))
private theorem rec11894 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(0),[9,10],[42],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1165]? = some (⟨230,(0),[9,10],[42],810⟩) from rfl))
private theorem rec11900 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(1),[9,10],[42],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1171]? = some (⟨230,(1),[9,10],[42],811⟩) from rfl))
private theorem rec11907 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(2),[9,10],[42],812⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1178]? = some (⟨230,(2),[9,10],[42],812⟩) from rfl))
private theorem rec11913 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(3),[9,10],[42],813⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1184]? = some (⟨230,(3),[9,10],[42],813⟩) from rfl))
private theorem rec11919 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(4),[9,10],[42],814⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1190]? = some (⟨230,(4),[9,10],[42],814⟩) from rfl))
private theorem rec11925 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(5),[9,10],[42],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1196]? = some (⟨230,(5),[9,10],[42],810⟩) from rfl))
private theorem rec11931 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(6),[9,10],[42],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[2]? = some (⟨230,(6),[9,10],[42],811⟩) from rfl))
private theorem rec11940 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(7),[9,10],[42],815⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[11]? = some (⟨230,(7),[9,10],[42],815⟩) from rfl))
private theorem rec11947 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(8),[9,10],[42],816⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[18]? = some (⟨230,(8),[9,10],[42],816⟩) from rfl))
private theorem rec11955 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(9),[9],[42],1375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[26]? = some (⟨230,(9),[9],[42],1375⟩) from rfl))
private theorem rec11962 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(10),[9,10],[42],818⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[33]? = some (⟨230,(10),[9,10],[42],818⟩) from rfl))
private theorem rec11968 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(11),[9,10],[42],819⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[39]? = some (⟨230,(11),[9,10],[42],819⟩) from rfl))
private theorem rec11976 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(12),[9,10],[42],820⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[47]? = some (⟨230,(12),[9,10],[42],820⟩) from rfl))
private theorem rec11982 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(13),[9,10],[42],821⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[53]? = some (⟨230,(13),[9,10],[42],821⟩) from rfl))
private theorem rec11990 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(14),[9],[42],1375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[61]? = some (⟨230,(14),[9],[42],1375⟩) from rfl))
private theorem rec11997 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(15),[9,10],[42],822⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[68]? = some (⟨230,(15),[9,10],[42],822⟩) from rfl))
private theorem rec12003 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(16),[9,10],[42],823⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[74]? = some (⟨230,(16),[9,10],[42],823⟩) from rfl))
private theorem rec12010 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(17),[9],[42],1376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[81]? = some (⟨230,(17),[9],[42],1376⟩) from rfl))
private theorem rec12017 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(18),[9,10],[42],825⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[88]? = some (⟨230,(18),[9,10],[42],825⟩) from rfl))
private theorem rec12024 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(19),[9],[42],1376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[95]? = some (⟨230,(19),[9],[42],1376⟩) from rfl))
private theorem rec12031 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(20),[9,10],[42],826⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[102]? = some (⟨230,(20),[9,10],[42],826⟩) from rfl))
private theorem rec12037 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(21),[9,10],[42],827⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[108]? = some (⟨230,(21),[9,10],[42],827⟩) from rfl))
private theorem rec12044 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(22),[9],[42],1377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[115]? = some (⟨230,(22),[9],[42],1377⟩) from rfl))
private theorem rec12051 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(23),[9,10],[42],829⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[122]? = some (⟨230,(23),[9,10],[42],829⟩) from rfl))
private theorem rec12058 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(24),[9],[42],1377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[129]? = some (⟨230,(24),[9],[42],1377⟩) from rfl))
private theorem rec12066 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(0),[9,10],[42],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[137]? = some (⟨231,(0),[9,10],[42],830⟩) from rfl))
private theorem rec12073 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(1),[9],[42],1646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[144]? = some (⟨231,(1),[9],[42],1646⟩) from rfl))
private theorem rec12080 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(2),[9,10],[42],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[151]? = some (⟨231,(2),[9,10],[42],832⟩) from rfl))
private theorem rec12086 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(3),[9,10],[42],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[157]? = some (⟨231,(3),[9,10],[42],833⟩) from rfl))
private theorem rec12093 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(4),[9,10],[42],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[164]? = some (⟨231,(4),[9,10],[42],830⟩) from rfl))
private theorem rec12100 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(5),[9],[42],1646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[171]? = some (⟨231,(5),[9],[42],1646⟩) from rfl))
private theorem rec12107 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(6),[9,10],[42],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[178]? = some (⟨231,(6),[9,10],[42],832⟩) from rfl))
private theorem rec12113 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(7),[9,10],[42],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[184]? = some (⟨231,(7),[9,10],[42],833⟩) from rfl))
private theorem rec12119 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(8),[9,10],[42],834⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[190]? = some (⟨231,(8),[9,10],[42],834⟩) from rfl))
private theorem rec12125 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(9),[9,10],[42],835⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[196]? = some (⟨231,(9),[9,10],[42],835⟩) from rfl))
private theorem rec12131 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(10),[9,10],[42],836⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[202]? = some (⟨231,(10),[9,10],[42],836⟩) from rfl))
private theorem rec12137 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(11),[9,10],[42],837⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[208]? = some (⟨231,(11),[9,10],[42],837⟩) from rfl))
private theorem rec12143 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(12),[9,10],[42],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[214]? = some (⟨231,(12),[9,10],[42],838⟩) from rfl))
private theorem rec12149 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(13),[9,10],[42],839⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[220]? = some (⟨231,(13),[9,10],[42],839⟩) from rfl))
private theorem rec12155 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(14),[9,10],[42],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[226]? = some (⟨231,(14),[9,10],[42],838⟩) from rfl))
private theorem rec12161 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(15),[9,10],[42],840⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[232]? = some (⟨231,(15),[9,10],[42],840⟩) from rfl))
private theorem rec12167 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(16),[9,10],[42],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[238]? = some (⟨231,(16),[9,10],[42],841⟩) from rfl))
private theorem rec12173 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(17),[9,10],[42],842⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[244]? = some (⟨231,(17),[9,10],[42],842⟩) from rfl))
private theorem rec12179 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(18),[9,10],[42],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[250]? = some (⟨231,(18),[9,10],[42],841⟩) from rfl))
private theorem rec12185 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(19),[9,10],[42],843⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[256]? = some (⟨231,(19),[9,10],[42],843⟩) from rfl))
private theorem rec12191 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(0),[9,10],[42],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[262]? = some (⟨232,(0),[9,10],[42],844⟩) from rfl))
private theorem rec12197 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(1),[9,10],[42],845⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[268]? = some (⟨232,(1),[9,10],[42],845⟩) from rfl))
private theorem rec12204 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(2),[9,10],[42],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[275]? = some (⟨232,(2),[9,10],[42],846⟩) from rfl))
private theorem rec12210 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(3),[9,10],[42],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[281]? = some (⟨232,(3),[9,10],[42],847⟩) from rfl))
private theorem rec12218 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(4),[9,10],[42],848⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[289]? = some (⟨232,(4),[9,10],[42],848⟩) from rfl))
private theorem rec12224 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(5),[9,10],[42],849⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[295]? = some (⟨232,(5),[9,10],[42],849⟩) from rfl))
private theorem rec12230 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(6),[9,10],[42],850⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[301]? = some (⟨232,(6),[9,10],[42],850⟩) from rfl))
private theorem rec12237 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(7),[9,10],[42],851⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[308]? = some (⟨232,(7),[9,10],[42],851⟩) from rfl))
private theorem rec12243 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(8),[9,10],[42],852⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[314]? = some (⟨232,(8),[9,10],[42],852⟩) from rfl))
private theorem rec12250 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(9),[9],[42],1378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[321]? = some (⟨232,(9),[9],[42],1378⟩) from rfl))
private theorem rec12257 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(10),[9,10],[42],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[328]? = some (⟨232,(10),[9,10],[42],844⟩) from rfl))
private theorem rec12263 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(11),[9,10],[42],854⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[334]? = some (⟨232,(11),[9,10],[42],854⟩) from rfl))
private theorem rec12270 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(12),[9,10],[42],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[341]? = some (⟨232,(12),[9,10],[42],846⟩) from rfl))
private theorem rec12276 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(13),[9,10],[42],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[347]? = some (⟨232,(13),[9,10],[42],847⟩) from rfl))
private theorem rec12283 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(14),[9],[42],1379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[354]? = some (⟨232,(14),[9],[42],1379⟩) from rfl))
private theorem rec12290 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(15),[9,10],[42],856⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[361]? = some (⟨232,(15),[9,10],[42],856⟩) from rfl))
private theorem rec12296 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(16),[9,10],[42],857⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[367]? = some (⟨232,(16),[9,10],[42],857⟩) from rfl))
private theorem rec12303 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(17),[9,10],[42],858⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[374]? = some (⟨232,(17),[9,10],[42],858⟩) from rfl))
private theorem rec12309 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(18),[9,10],[42],859⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[380]? = some (⟨232,(18),[9,10],[42],859⟩) from rfl))
private theorem rec12316 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(19),[9],[42],1380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[387]? = some (⟨232,(19),[9],[42],1380⟩) from rfl))
private theorem rec12323 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(0),[9,10],[42],568⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[394]? = some (⟨234,(0),[9,10],[42],568⟩) from rfl))
private theorem rec12330 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(1),[9],[42],1381⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[401]? = some (⟨234,(1),[9],[42],1381⟩) from rfl))
private theorem rec12338 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(2),[9],[42],1382⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[409]? = some (⟨234,(2),[9],[42],1382⟩) from rfl))
private theorem rec12346 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(3),[9],[42],1383⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[417]? = some (⟨234,(3),[9],[42],1383⟩) from rfl))
private theorem rec12353 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(4),[9,10],[42],572⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[424]? = some (⟨234,(4),[9,10],[42],572⟩) from rfl))
private theorem rec12360 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(5),[9],[42],1384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[431]? = some (⟨234,(5),[9],[42],1384⟩) from rfl))
private theorem rec12368 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(6),[9],[42],1384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[439]? = some (⟨234,(6),[9],[42],1384⟩) from rfl))
private theorem rec12376 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(7),[9],[42],1384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[447]? = some (⟨234,(7),[9],[42],1384⟩) from rfl))
private theorem rec12383 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(8),[9,10],[42],574⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[454]? = some (⟨234,(8),[9,10],[42],574⟩) from rfl))
private theorem rec12390 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(9),[9],[42],1385⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[461]? = some (⟨234,(9),[9],[42],1385⟩) from rfl))
private theorem rec12398 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(10),[9],[42],1385⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[469]? = some (⟨234,(10),[9],[42],1385⟩) from rfl))
private theorem rec12406 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(11),[9],[42],1385⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[477]? = some (⟨234,(11),[9],[42],1385⟩) from rfl))
private theorem rec12413 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(12),[9,10],[42],576⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[484]? = some (⟨234,(12),[9,10],[42],576⟩) from rfl))
private theorem rec12420 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(13),[9],[42],1386⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[491]? = some (⟨234,(13),[9],[42],1386⟩) from rfl))
private theorem rec12428 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(14),[9],[42],1386⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[499]? = some (⟨234,(14),[9],[42],1386⟩) from rfl))
private theorem rec12436 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(15),[9],[42],1386⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[507]? = some (⟨234,(15),[9],[42],1386⟩) from rfl))
private theorem rec12443 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(0),[9,10],[42],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[514]? = some (⟨235,(0),[9,10],[42],578⟩) from rfl))
private theorem rec12449 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(1),[9,10],[42],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1]? = some (⟨235,(1),[9,10],[42],579⟩) from rfl))
private theorem rec12456 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(2),[9],[42],1387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[8]? = some (⟨235,(2),[9],[42],1387⟩) from rfl))
private theorem rec12463 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(3),[9,10],[42],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[15]? = some (⟨235,(3),[9,10],[42],581⟩) from rfl))
private theorem rec12469 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(4),[9,10],[42],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[21]? = some (⟨235,(4),[9,10],[42],582⟩) from rfl))
private theorem rec12475 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(5),[9,10],[42],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[27]? = some (⟨235,(5),[9,10],[42],583⟩) from rfl))
private theorem rec12482 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(6),[9],[42],1388⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[34]? = some (⟨235,(6),[9],[42],1388⟩) from rfl))
private theorem rec12489 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(7),[9,10],[42],585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[41]? = some (⟨235,(7),[9,10],[42],585⟩) from rfl))
private theorem rec12495 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(8),[9,10],[42],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[47]? = some (⟨235,(8),[9,10],[42],578⟩) from rfl))
private theorem rec12501 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(9),[9,10],[42],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[53]? = some (⟨235,(9),[9,10],[42],579⟩) from rfl))
private theorem rec12508 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(10),[9],[42],1387⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[60]? = some (⟨235,(10),[9],[42],1387⟩) from rfl))
private theorem rec12515 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(11),[9,10],[42],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[67]? = some (⟨235,(11),[9,10],[42],581⟩) from rfl))
private theorem rec12521 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(12),[9,10],[42],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[73]? = some (⟨235,(12),[9,10],[42],586⟩) from rfl))
private theorem rec12527 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(13),[9,10],[42],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[79]? = some (⟨235,(13),[9,10],[42],587⟩) from rfl))
private theorem rec12534 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(14),[9],[42],1389⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[86]? = some (⟨235,(14),[9],[42],1389⟩) from rfl))
private theorem rec12541 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(15),[9,10],[42],589⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[93]? = some (⟨235,(15),[9,10],[42],589⟩) from rfl))
private theorem rec12548 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 236 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(0),[9,10],[42],861⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[100]? = some (⟨236,(0),[9,10],[42],861⟩) from rfl))
private theorem rec12555 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 236 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(1),[9,10],[42],862⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[107]? = some (⟨236,(1),[9,10],[42],862⟩) from rfl))
private theorem rec12563 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 236 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(2),[9],[42],861⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[115]? = some (⟨236,(2),[9],[42],861⟩) from rfl))
private theorem rec12571 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 236 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(3),[9,10],[42],864⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[123]? = some (⟨236,(3),[9,10],[42],864⟩) from rfl))
private theorem rec12578 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(0),[9,10],[42],865⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[130]? = some (⟨237,(0),[9,10],[42],865⟩) from rfl))
private theorem rec12584 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(1),[9,10],[42],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[136]? = some (⟨237,(1),[9,10],[42],594⟩) from rfl))
private theorem rec12591 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(2),[9,10],[42],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[143]? = some (⟨237,(2),[9,10],[42],595⟩) from rfl))
private theorem rec12598 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(3),[9],[42],1271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[150]? = some (⟨237,(3),[9],[42],1271⟩) from rfl))
private theorem rec12606 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(4),[9,10],[42],866⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[158]? = some (⟨237,(4),[9,10],[42],866⟩) from rfl))
private theorem rec12612 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(5),[9,10],[42],598⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[164]? = some (⟨237,(5),[9,10],[42],598⟩) from rfl))
private theorem rec12618 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(6),[9,10],[42],599⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[170]? = some (⟨237,(6),[9,10],[42],599⟩) from rfl))
private theorem rec12624 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(7),[9,10],[42],600⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[176]? = some (⟨237,(7),[9,10],[42],600⟩) from rfl))
private theorem rec12632 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(8),[9],[42],865⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[184]? = some (⟨237,(8),[9],[42],865⟩) from rfl))
private theorem rec12639 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(9),[9,10],[42],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[191]? = some (⟨237,(9),[9,10],[42],594⟩) from rfl))
private theorem rec12645 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(10),[9,10],[42],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[197]? = some (⟨237,(10),[9,10],[42],595⟩) from rfl))
private theorem rec12651 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(11),[9,10],[42],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[203]? = some (⟨237,(11),[9,10],[42],596⟩) from rfl))
private theorem rec12658 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(12),[9,10],[42],868⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[210]? = some (⟨237,(12),[9,10],[42],868⟩) from rfl))
private theorem rec12664 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(13),[9,10],[42],602⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[216]? = some (⟨237,(13),[9,10],[42],602⟩) from rfl))
private theorem rec12670 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(14),[9,10],[42],603⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[222]? = some (⟨237,(14),[9,10],[42],603⟩) from rfl))
private theorem rec12676 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(15),[9,10],[42],604⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[228]? = some (⟨237,(15),[9,10],[42],604⟩) from rfl))
private theorem rec12682 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(0),[9,10],[42],869⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[234]? = some (⟨238,(0),[9,10],[42],869⟩) from rfl))
private theorem rec12688 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(1),[9,10],[42],870⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[240]? = some (⟨238,(1),[9,10],[42],870⟩) from rfl))
private theorem rec12695 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(2),[9],[42],1390⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[247]? = some (⟨238,(2),[9],[42],1390⟩) from rfl))
private theorem rec12703 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(3),[9,10],[42],871⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[255]? = some (⟨238,(3),[9,10],[42],871⟩) from rfl))
private theorem rec12709 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(4),[9,10],[42],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[261]? = some (⟨238,(4),[9,10],[42],609⟩) from rfl))
private theorem rec12715 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(5),[9,10],[42],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[267]? = some (⟨238,(5),[9,10],[42],610⟩) from rfl))
private theorem rec12722 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(6),[9],[42],1391⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[274]? = some (⟨238,(6),[9],[42],1391⟩) from rfl))
private theorem rec12729 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(7),[9,10],[42],612⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[281]? = some (⟨238,(7),[9,10],[42],612⟩) from rfl))
private theorem rec12735 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(8),[9,10],[42],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[287]? = some (⟨238,(8),[9,10],[42],613⟩) from rfl))
private theorem rec12741 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(9),[9,10],[42],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[293]? = some (⟨238,(9),[9,10],[42],614⟩) from rfl))
private theorem rec12748 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(10),[9],[42],1392⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[300]? = some (⟨238,(10),[9],[42],1392⟩) from rfl))
private theorem rec12755 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(11),[9,10],[42],616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[307]? = some (⟨238,(11),[9,10],[42],616⟩) from rfl))
private theorem rec12761 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(12),[9,10],[42],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[313]? = some (⟨238,(12),[9,10],[42],617⟩) from rfl))
private theorem rec12767 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(13),[9,10],[42],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[319]? = some (⟨238,(13),[9,10],[42],618⟩) from rfl))
private theorem rec12774 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(14),[9],[42],1393⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[326]? = some (⟨238,(14),[9],[42],1393⟩) from rfl))
private theorem rec12781 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(15),[9,10],[42],620⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[333]? = some (⟨238,(15),[9,10],[42],620⟩) from rfl))
private theorem rec12786 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(0),[9,10],[42],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[338]? = some (⟨242,(0),[9,10],[42],632⟩) from rfl))
private theorem rec12790 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(1),[9,10],[42],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[342]? = some (⟨242,(1),[9,10],[42],872⟩) from rfl))
private theorem rec12794 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(2),[9,10],[42],873⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[346]? = some (⟨242,(2),[9,10],[42],873⟩) from rfl))
private theorem rec12798 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(3),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[350]? = some (⟨242,(3),[9,10],[42],101⟩) from rfl))
private theorem rec12802 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(4),[9,10],[42],873⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[354]? = some (⟨242,(4),[9,10],[42],873⟩) from rfl))
private theorem rec12806 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(5),[9,10],[42],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[358]? = some (⟨242,(5),[9,10],[42],632⟩) from rfl))
private theorem rec12810 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(6),[9,10],[42],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[362]? = some (⟨242,(6),[9,10],[42],872⟩) from rfl))
private theorem rec12814 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(7),[9,10],[42],874⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[366]? = some (⟨242,(7),[9,10],[42],874⟩) from rfl))
private theorem rec12818 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(8),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[370]? = some (⟨242,(8),[9,10],[42],101⟩) from rfl))
private theorem rec12822 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(9),[9,10],[42],874⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[374]? = some (⟨242,(9),[9,10],[42],874⟩) from rfl))
private theorem rec12826 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(10),[9,10],[42],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[378]? = some (⟨242,(10),[9,10],[42],632⟩) from rfl))
private theorem rec12830 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(11),[9,10],[42],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[382]? = some (⟨242,(11),[9,10],[42],872⟩) from rfl))
private theorem rec12834 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(12),[9,10],[42],875⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[386]? = some (⟨242,(12),[9,10],[42],875⟩) from rfl))
private theorem rec12838 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(13),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[390]? = some (⟨242,(13),[9,10],[42],101⟩) from rfl))
private theorem rec12842 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(14),[9,10],[42],875⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[394]? = some (⟨242,(14),[9,10],[42],875⟩) from rfl))
private theorem rec12846 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(15),[9,10],[42],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[398]? = some (⟨242,(15),[9,10],[42],625⟩) from rfl))
private theorem rec12850 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(16),[9,10],[42],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[402]? = some (⟨242,(16),[9,10],[42],626⟩) from rfl))
private theorem rec12854 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(17),[9,10],[42],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[406]? = some (⟨242,(17),[9,10],[42],286⟩) from rfl))
private theorem rec12858 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(18),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[410]? = some (⟨242,(18),[9,10],[42],101⟩) from rfl))
private theorem rec12862 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(19),[9,10],[42],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[414]? = some (⟨242,(19),[9,10],[42],286⟩) from rfl))
private theorem rec12866 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(20),[9,10],[42],876⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[418]? = some (⟨242,(20),[9,10],[42],876⟩) from rfl))
private theorem rec12870 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(21),[9,10],[42],877⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[422]? = some (⟨242,(21),[9,10],[42],877⟩) from rfl))
private theorem rec12874 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(22),[9,10],[42],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[426]? = some (⟨242,(22),[9,10],[42],287⟩) from rfl))
private theorem rec12878 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(23),[9,10],[42],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[430]? = some (⟨242,(23),[9,10],[42],101⟩) from rfl))
private theorem rec12882 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 242 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(24),[9,10],[42],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[434]? = some (⟨242,(24),[9,10],[42],287⟩) from rfl))
private theorem rec16434 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(0),[9,10],[42],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[226]? = some (⟨567,(0),[9,10],[42],1649⟩) from rfl))
private theorem rec16437 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(1),[9],[42],1669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[229]? = some (⟨567,(1),[9],[42],1669⟩) from rfl))
private theorem rec16441 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(2),[9],[42],1670⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[233]? = some (⟨567,(2),[9],[42],1670⟩) from rfl))
private theorem rec16445 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(3),[9],[42],1671⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[237]? = some (⟨567,(3),[9],[42],1671⟩) from rfl))
private theorem rec16449 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(4),[9],[42],1275⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[241]? = some (⟨567,(4),[9],[42],1275⟩) from rfl))
private theorem rec16453 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(5),[9,10],[42],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[245]? = some (⟨567,(5),[9,10],[42],1649⟩) from rfl))
private theorem rec16456 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(6),[9],[42],1669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[248]? = some (⟨567,(6),[9],[42],1669⟩) from rfl))
private theorem rec16460 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(7),[9],[42],1670⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[252]? = some (⟨567,(7),[9],[42],1670⟩) from rfl))
private theorem rec16464 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(8),[9],[42],1671⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[256]? = some (⟨567,(8),[9],[42],1671⟩) from rfl))
private theorem rec16468 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(9),[9],[42],1275⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[260]? = some (⟨567,(9),[9],[42],1275⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 9).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 32).take 16, section14Recorded section14Catalog 9 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 9 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 9).plans.drop 5).take 1 = [⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(566,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(567,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(568,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(569,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(570,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec7425 9 32 (by decide) (by decide)
  · left
    exact rec7425 9 33 (by decide) (by decide)
  · left
    exact rec7429 9 34 (by decide) (by decide)
  · left
    exact rec7430 9 35 (by decide) (by decide)
  · left
    exact rec7425 9 36 (by decide) (by decide)
  · left
    exact rec7425 9 37 (by decide) (by decide)
  · left
    exact rec7431 9 38 (by decide) (by decide)
  · left
    exact rec7430 9 39 (by decide) (by decide)
  · left
    exact rec7425 9 40 (by decide) (by decide)
  · left
    exact rec7425 9 41 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(566,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(567,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(568,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(569,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(570,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 566)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 155)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7442 9 42 (by decide) (by decide)
      · right
        exact rec7445 9 42 (by decide) (by decide)
      · right
        exact rec7448 9 42 (by decide) (by decide)
      · right
        exact rec7451 9 42 (by decide) (by decide)
      · right
        exact rec7454 9 42 (by decide) (by decide)
      · right
        exact rec7457 9 42 (by decide) (by decide)
      · right
        exact rec7460 9 42 (by decide) (by decide)
      · right
        exact rec7463 9 42 (by decide) (by decide)
      · right
        exact rec7466 9 42 (by decide) (by decide)
      · right
        exact rec7469 9 42 (by decide) (by decide)
      · right
        exact rec7472 9 42 (by decide) (by decide)
      · right
        exact rec7475 9 42 (by decide) (by decide)
      · right
        exact rec7478 9 42 (by decide) (by decide)
      · right
        exact rec7481 9 42 (by decide) (by decide)
      · right
        exact rec7484 9 42 (by decide) (by decide)
      · right
        exact rec7487 9 42 (by decide) (by decide)
      · right
        exact rec7490 9 42 (by decide) (by decide)
      · right
        exact rec7493 9 42 (by decide) (by decide)
      · right
        exact rec7496 9 42 (by decide) (by decide)
      · right
        exact rec7499 9 42 (by decide) (by decide)
      · right
        exact rec7502 9 42 (by decide) (by decide)
      · right
        exact rec7505 9 42 (by decide) (by decide)
      · right
        exact rec7508 9 42 (by decide) (by decide)
      · right
        exact rec7511 9 42 (by decide) (by decide)
      · right
        exact rec7514 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 156)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 567)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16434 9 42 (by decide) (by decide)
      · right
        exact rec16437 9 42 (by decide) (by decide)
      · right
        exact rec16441 9 42 (by decide) (by decide)
      · right
        exact rec16445 9 42 (by decide) (by decide)
      · right
        exact rec16449 9 42 (by decide) (by decide)
      · right
        exact rec16453 9 42 (by decide) (by decide)
      · right
        exact rec16456 9 42 (by decide) (by decide)
      · right
        exact rec16460 9 42 (by decide) (by decide)
      · right
        exact rec16464 9 42 (by decide) (by decide)
      · right
        exact rec16468 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 568)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 159)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 160)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7640 9 42 (by decide) (by decide)
      · right
        exact rec7647 9 42 (by decide) (by decide)
      · right
        exact rec7654 9 42 (by decide) (by decide)
      · right
        exact rec7661 9 42 (by decide) (by decide)
      · right
        exact rec7668 9 42 (by decide) (by decide)
      · right
        exact rec7675 9 42 (by decide) (by decide)
      · right
        exact rec7682 9 42 (by decide) (by decide)
      · right
        exact rec7689 9 42 (by decide) (by decide)
      · right
        exact rec7696 9 42 (by decide) (by decide)
      · right
        exact rec7703 9 42 (by decide) (by decide)
      · right
        exact rec7710 9 42 (by decide) (by decide)
      · right
        exact rec7717 9 42 (by decide) (by decide)
      · right
        exact rec7724 9 42 (by decide) (by decide)
      · right
        exact rec7731 9 42 (by decide) (by decide)
      · right
        exact rec7738 9 42 (by decide) (by decide)
      · right
        exact rec7745 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 161)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 162)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 163)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7752 9 42 (by decide) (by decide)
      · right
        exact rec7760 9 42 (by decide) (by decide)
      · right
        exact rec7768 9 42 (by decide) (by decide)
      · right
        exact rec7776 9 42 (by decide) (by decide)
      · right
        exact rec7784 9 42 (by decide) (by decide)
      · right
        exact rec7792 9 42 (by decide) (by decide)
      · right
        exact rec7800 9 42 (by decide) (by decide)
      · right
        exact rec7808 9 42 (by decide) (by decide)
      · right
        exact rec7816 9 42 (by decide) (by decide)
      · right
        exact rec7824 9 42 (by decide) (by decide)
      · right
        exact rec7832 9 42 (by decide) (by decide)
      · right
        exact rec7840 9 42 (by decide) (by decide)
      · right
        exact rec7848 9 42 (by decide) (by decide)
      · right
        exact rec7856 9 42 (by decide) (by decide)
      · right
        exact rec7864 9 42 (by decide) (by decide)
      · right
        exact rec7872 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 164)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 165)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 166)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7880 9 42 (by decide) (by decide)
      · right
        exact rec7887 9 42 (by decide) (by decide)
      · right
        exact rec7894 9 42 (by decide) (by decide)
      · right
        exact rec7901 9 42 (by decide) (by decide)
      · right
        exact rec7908 9 42 (by decide) (by decide)
      · right
        exact rec7915 9 42 (by decide) (by decide)
      · right
        exact rec7922 9 42 (by decide) (by decide)
      · right
        exact rec7929 9 42 (by decide) (by decide)
      · right
        exact rec7936 9 42 (by decide) (by decide)
      · right
        exact rec7943 9 42 (by decide) (by decide)
      · right
        exact rec7950 9 42 (by decide) (by decide)
      · right
        exact rec7957 9 42 (by decide) (by decide)
      · right
        exact rec7964 9 42 (by decide) (by decide)
      · right
        exact rec7971 9 42 (by decide) (by decide)
      · right
        exact rec7978 9 42 (by decide) (by decide)
      · right
        exact rec7985 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 167)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7992 9 42 (by decide) (by decide)
      · right
        exact rec8000 9 42 (by decide) (by decide)
      · right
        exact rec8008 9 42 (by decide) (by decide)
      · right
        exact rec8016 9 42 (by decide) (by decide)
      · right
        exact rec8024 9 42 (by decide) (by decide)
      · right
        exact rec8032 9 42 (by decide) (by decide)
      · right
        exact rec8040 9 42 (by decide) (by decide)
      · right
        exact rec8048 9 42 (by decide) (by decide)
      · right
        exact rec8056 9 42 (by decide) (by decide)
      · right
        exact rec8064 9 42 (by decide) (by decide)
      · right
        exact rec8072 9 42 (by decide) (by decide)
      · right
        exact rec8080 9 42 (by decide) (by decide)
      · right
        exact rec8088 9 42 (by decide) (by decide)
      · right
        exact rec8096 9 42 (by decide) (by decide)
      · right
        exact rec8104 9 42 (by decide) (by decide)
      · right
        exact rec8112 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 168)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 169)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 170)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 171)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8120 9 42 (by decide) (by decide)
      · right
        exact rec8127 9 42 (by decide) (by decide)
      · right
        exact rec8134 9 42 (by decide) (by decide)
      · right
        exact rec8141 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 172)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8148 9 42 (by decide) (by decide)
      · right
        exact rec8156 9 42 (by decide) (by decide)
      · right
        exact rec8164 9 42 (by decide) (by decide)
      · right
        exact rec8172 9 42 (by decide) (by decide)
      · right
        exact rec8180 9 42 (by decide) (by decide)
      · right
        exact rec8188 9 42 (by decide) (by decide)
      · right
        exact rec8196 9 42 (by decide) (by decide)
      · right
        exact rec8204 9 42 (by decide) (by decide)
      · right
        exact rec8212 9 42 (by decide) (by decide)
      · right
        exact rec8220 9 42 (by decide) (by decide)
      · right
        exact rec8228 9 42 (by decide) (by decide)
      · right
        exact rec8236 9 42 (by decide) (by decide)
      · right
        exact rec8244 9 42 (by decide) (by decide)
      · right
        exact rec8252 9 42 (by decide) (by decide)
      · right
        exact rec8260 9 42 (by decide) (by decide)
      · right
        exact rec8268 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 173)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 174)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 175)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8276 9 42 (by decide) (by decide)
      · right
        exact rec8283 9 42 (by decide) (by decide)
      · right
        exact rec8290 9 42 (by decide) (by decide)
      · right
        exact rec8297 9 42 (by decide) (by decide)
      · right
        exact rec8304 9 42 (by decide) (by decide)
      · right
        exact rec8311 9 42 (by decide) (by decide)
      · right
        exact rec8318 9 42 (by decide) (by decide)
      · right
        exact rec8325 9 42 (by decide) (by decide)
      · right
        exact rec8332 9 42 (by decide) (by decide)
      · right
        exact rec8339 9 42 (by decide) (by decide)
      · right
        exact rec8346 9 42 (by decide) (by decide)
      · right
        exact rec8353 9 42 (by decide) (by decide)
      · right
        exact rec8360 9 42 (by decide) (by decide)
      · right
        exact rec8367 9 42 (by decide) (by decide)
      · right
        exact rec8374 9 42 (by decide) (by decide)
      · right
        exact rec8381 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 176)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 177)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 178)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8388 9 42 (by decide) (by decide)
      · right
        exact rec8396 9 42 (by decide) (by decide)
      · right
        exact rec8404 9 42 (by decide) (by decide)
      · right
        exact rec8412 9 42 (by decide) (by decide)
      · right
        exact rec8420 9 42 (by decide) (by decide)
      · right
        exact rec8428 9 42 (by decide) (by decide)
      · right
        exact rec8436 9 42 (by decide) (by decide)
      · right
        exact rec8444 9 42 (by decide) (by decide)
      · right
        exact rec8452 9 42 (by decide) (by decide)
      · right
        exact rec8460 9 42 (by decide) (by decide)
      · right
        exact rec8468 9 42 (by decide) (by decide)
      · right
        exact rec8476 9 42 (by decide) (by decide)
      · right
        exact rec8484 9 42 (by decide) (by decide)
      · right
        exact rec8492 9 42 (by decide) (by decide)
      · right
        exact rec8500 9 42 (by decide) (by decide)
      · right
        exact rec8508 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 179)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 180)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8516 9 42 (by decide) (by decide)
      · right
        exact rec8523 9 42 (by decide) (by decide)
      · right
        exact rec8530 9 42 (by decide) (by decide)
      · right
        exact rec8537 9 42 (by decide) (by decide)
      · right
        exact rec8544 9 42 (by decide) (by decide)
      · right
        exact rec8551 9 42 (by decide) (by decide)
      · right
        exact rec8558 9 42 (by decide) (by decide)
      · right
        exact rec8565 9 42 (by decide) (by decide)
      · right
        exact rec8572 9 42 (by decide) (by decide)
      · right
        exact rec8579 9 42 (by decide) (by decide)
      · right
        exact rec8586 9 42 (by decide) (by decide)
      · right
        exact rec8593 9 42 (by decide) (by decide)
      · right
        exact rec8600 9 42 (by decide) (by decide)
      · right
        exact rec8607 9 42 (by decide) (by decide)
      · right
        exact rec8614 9 42 (by decide) (by decide)
      · right
        exact rec8621 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 181)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 182)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 183)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8628 9 42 (by decide) (by decide)
      · right
        exact rec8636 9 42 (by decide) (by decide)
      · right
        exact rec8644 9 42 (by decide) (by decide)
      · right
        exact rec8652 9 42 (by decide) (by decide)
      · right
        exact rec8660 9 42 (by decide) (by decide)
      · right
        exact rec8668 9 42 (by decide) (by decide)
      · right
        exact rec8676 9 42 (by decide) (by decide)
      · right
        exact rec8684 9 42 (by decide) (by decide)
      · right
        exact rec8692 9 42 (by decide) (by decide)
      · right
        exact rec8700 9 42 (by decide) (by decide)
      · right
        exact rec8708 9 42 (by decide) (by decide)
      · right
        exact rec8716 9 42 (by decide) (by decide)
      · right
        exact rec8724 9 42 (by decide) (by decide)
      · right
        exact rec8732 9 42 (by decide) (by decide)
      · right
        exact rec8740 9 42 (by decide) (by decide)
      · right
        exact rec8748 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 184)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 185)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8756 9 42 (by decide) (by decide)
      · right
        exact rec8763 9 42 (by decide) (by decide)
      · right
        exact rec8770 9 42 (by decide) (by decide)
      · right
        exact rec8777 9 42 (by decide) (by decide)
      · right
        exact rec8784 9 42 (by decide) (by decide)
      · right
        exact rec8791 9 42 (by decide) (by decide)
      · right
        exact rec8798 9 42 (by decide) (by decide)
      · right
        exact rec8805 9 42 (by decide) (by decide)
      · right
        exact rec8812 9 42 (by decide) (by decide)
      · right
        exact rec8819 9 42 (by decide) (by decide)
      · right
        exact rec8826 9 42 (by decide) (by decide)
      · right
        exact rec8833 9 42 (by decide) (by decide)
      · right
        exact rec8840 9 42 (by decide) (by decide)
      · right
        exact rec8847 9 42 (by decide) (by decide)
      · right
        exact rec8854 9 42 (by decide) (by decide)
      · right
        exact rec8861 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 186)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 187)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 188)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8868 9 42 (by decide) (by decide)
      · right
        exact rec8876 9 42 (by decide) (by decide)
      · right
        exact rec8884 9 42 (by decide) (by decide)
      · right
        exact rec8892 9 42 (by decide) (by decide)
      · right
        exact rec8900 9 42 (by decide) (by decide)
      · right
        exact rec8908 9 42 (by decide) (by decide)
      · right
        exact rec8916 9 42 (by decide) (by decide)
      · right
        exact rec8924 9 42 (by decide) (by decide)
      · right
        exact rec8932 9 42 (by decide) (by decide)
      · right
        exact rec8940 9 42 (by decide) (by decide)
      · right
        exact rec8948 9 42 (by decide) (by decide)
      · right
        exact rec8956 9 42 (by decide) (by decide)
      · right
        exact rec8964 9 42 (by decide) (by decide)
      · right
        exact rec8972 9 42 (by decide) (by decide)
      · right
        exact rec8980 9 42 (by decide) (by decide)
      · right
        exact rec8988 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 189)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 190)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8996 9 42 (by decide) (by decide)
      · right
        exact rec9003 9 42 (by decide) (by decide)
      · right
        exact rec9010 9 42 (by decide) (by decide)
      · right
        exact rec9017 9 42 (by decide) (by decide)
      · right
        exact rec9024 9 42 (by decide) (by decide)
      · right
        exact rec9031 9 42 (by decide) (by decide)
      · right
        exact rec9038 9 42 (by decide) (by decide)
      · right
        exact rec9045 9 42 (by decide) (by decide)
      · right
        exact rec9052 9 42 (by decide) (by decide)
      · right
        exact rec9059 9 42 (by decide) (by decide)
      · right
        exact rec9066 9 42 (by decide) (by decide)
      · right
        exact rec9073 9 42 (by decide) (by decide)
      · right
        exact rec9080 9 42 (by decide) (by decide)
      · right
        exact rec9087 9 42 (by decide) (by decide)
      · right
        exact rec9094 9 42 (by decide) (by decide)
      · right
        exact rec9101 9 42 (by decide) (by decide)
      · right
        exact rec9108 9 42 (by decide) (by decide)
      · right
        exact rec9115 9 42 (by decide) (by decide)
      · right
        exact rec9122 9 42 (by decide) (by decide)
      · right
        exact rec9129 9 42 (by decide) (by decide)
      · right
        exact rec9136 9 42 (by decide) (by decide)
      · right
        exact rec9143 9 42 (by decide) (by decide)
      · right
        exact rec9150 9 42 (by decide) (by decide)
      · right
        exact rec9157 9 42 (by decide) (by decide)
      · right
        exact rec9164 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 191)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 192)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9171 9 42 (by decide) (by decide)
      · right
        exact rec9179 9 42 (by decide) (by decide)
      · right
        exact rec9187 9 42 (by decide) (by decide)
      · right
        exact rec9195 9 42 (by decide) (by decide)
      · right
        exact rec9203 9 42 (by decide) (by decide)
      · right
        exact rec9211 9 42 (by decide) (by decide)
      · right
        exact rec9219 9 42 (by decide) (by decide)
      · right
        exact rec9227 9 42 (by decide) (by decide)
      · right
        exact rec9235 9 42 (by decide) (by decide)
      · right
        exact rec9243 9 42 (by decide) (by decide)
      · right
        exact rec9251 9 42 (by decide) (by decide)
      · right
        exact rec9259 9 42 (by decide) (by decide)
      · right
        exact rec9267 9 42 (by decide) (by decide)
      · right
        exact rec9275 9 42 (by decide) (by decide)
      · right
        exact rec9283 9 42 (by decide) (by decide)
      · right
        exact rec9291 9 42 (by decide) (by decide)
      · right
        exact rec9299 9 42 (by decide) (by decide)
      · right
        exact rec9307 9 42 (by decide) (by decide)
      · right
        exact rec9315 9 42 (by decide) (by decide)
      · right
        exact rec9323 9 42 (by decide) (by decide)
      · right
        exact rec9331 9 42 (by decide) (by decide)
      · right
        exact rec9339 9 42 (by decide) (by decide)
      · right
        exact rec9347 9 42 (by decide) (by decide)
      · right
        exact rec9355 9 42 (by decide) (by decide)
      · right
        exact rec9363 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 193)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 194)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 195)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9371 9 42 (by decide) (by decide)
      · right
        exact rec9378 9 42 (by decide) (by decide)
      · right
        exact rec9385 9 42 (by decide) (by decide)
      · right
        exact rec9392 9 42 (by decide) (by decide)
      · right
        exact rec9399 9 42 (by decide) (by decide)
      · right
        exact rec9406 9 42 (by decide) (by decide)
      · right
        exact rec9413 9 42 (by decide) (by decide)
      · right
        exact rec9420 9 42 (by decide) (by decide)
      · right
        exact rec9427 9 42 (by decide) (by decide)
      · right
        exact rec9434 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 196)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 197)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9441 9 42 (by decide) (by decide)
      · right
        exact rec9449 9 42 (by decide) (by decide)
      · right
        exact rec9457 9 42 (by decide) (by decide)
      · right
        exact rec9465 9 42 (by decide) (by decide)
      · right
        exact rec9473 9 42 (by decide) (by decide)
      · right
        exact rec9481 9 42 (by decide) (by decide)
      · right
        exact rec9489 9 42 (by decide) (by decide)
      · right
        exact rec9497 9 42 (by decide) (by decide)
      · right
        exact rec9505 9 42 (by decide) (by decide)
      · right
        exact rec9513 9 42 (by decide) (by decide)
      · right
        exact rec9521 9 42 (by decide) (by decide)
      · right
        exact rec9529 9 42 (by decide) (by decide)
      · right
        exact rec9537 9 42 (by decide) (by decide)
      · right
        exact rec9545 9 42 (by decide) (by decide)
      · right
        exact rec9553 9 42 (by decide) (by decide)
      · right
        exact rec9561 9 42 (by decide) (by decide)
      · right
        exact rec9569 9 42 (by decide) (by decide)
      · right
        exact rec9577 9 42 (by decide) (by decide)
      · right
        exact rec9585 9 42 (by decide) (by decide)
      · right
        exact rec9593 9 42 (by decide) (by decide)
      · right
        exact rec9601 9 42 (by decide) (by decide)
      · right
        exact rec9609 9 42 (by decide) (by decide)
      · right
        exact rec9617 9 42 (by decide) (by decide)
      · right
        exact rec9625 9 42 (by decide) (by decide)
      · right
        exact rec9633 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 198)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 199)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 200)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9641 9 42 (by decide) (by decide)
      · right
        exact rec9648 9 42 (by decide) (by decide)
      · right
        exact rec9655 9 42 (by decide) (by decide)
      · right
        exact rec9662 9 42 (by decide) (by decide)
      · right
        exact rec9669 9 42 (by decide) (by decide)
      · right
        exact rec9676 9 42 (by decide) (by decide)
      · right
        exact rec9683 9 42 (by decide) (by decide)
      · right
        exact rec9690 9 42 (by decide) (by decide)
      · right
        exact rec9697 9 42 (by decide) (by decide)
      · right
        exact rec9704 9 42 (by decide) (by decide)
      · right
        exact rec9711 9 42 (by decide) (by decide)
      · right
        exact rec9718 9 42 (by decide) (by decide)
      · right
        exact rec9725 9 42 (by decide) (by decide)
      · right
        exact rec9732 9 42 (by decide) (by decide)
      · right
        exact rec9739 9 42 (by decide) (by decide)
      · right
        exact rec9746 9 42 (by decide) (by decide)
      · right
        exact rec9753 9 42 (by decide) (by decide)
      · right
        exact rec9760 9 42 (by decide) (by decide)
      · right
        exact rec9767 9 42 (by decide) (by decide)
      · right
        exact rec9774 9 42 (by decide) (by decide)
      · right
        exact rec9781 9 42 (by decide) (by decide)
      · right
        exact rec9788 9 42 (by decide) (by decide)
      · right
        exact rec9795 9 42 (by decide) (by decide)
      · right
        exact rec9802 9 42 (by decide) (by decide)
      · right
        exact rec9809 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 201)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 202)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9816 9 42 (by decide) (by decide)
      · right
        exact rec9824 9 42 (by decide) (by decide)
      · right
        exact rec9832 9 42 (by decide) (by decide)
      · right
        exact rec9840 9 42 (by decide) (by decide)
      · right
        exact rec9848 9 42 (by decide) (by decide)
      · right
        exact rec9856 9 42 (by decide) (by decide)
      · right
        exact rec9864 9 42 (by decide) (by decide)
      · right
        exact rec9872 9 42 (by decide) (by decide)
      · right
        exact rec9880 9 42 (by decide) (by decide)
      · right
        exact rec9888 9 42 (by decide) (by decide)
      · right
        exact rec9896 9 42 (by decide) (by decide)
      · right
        exact rec9904 9 42 (by decide) (by decide)
      · right
        exact rec9912 9 42 (by decide) (by decide)
      · right
        exact rec9920 9 42 (by decide) (by decide)
      · right
        exact rec9928 9 42 (by decide) (by decide)
      · right
        exact rec9936 9 42 (by decide) (by decide)
      · right
        exact rec9944 9 42 (by decide) (by decide)
      · right
        exact rec9952 9 42 (by decide) (by decide)
      · right
        exact rec9960 9 42 (by decide) (by decide)
      · right
        exact rec9968 9 42 (by decide) (by decide)
      · right
        exact rec9976 9 42 (by decide) (by decide)
      · right
        exact rec9984 9 42 (by decide) (by decide)
      · right
        exact rec9992 9 42 (by decide) (by decide)
      · right
        exact rec10000 9 42 (by decide) (by decide)
      · right
        exact rec10008 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 203)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 204)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 205)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10016 9 42 (by decide) (by decide)
      · right
        exact rec10023 9 42 (by decide) (by decide)
      · right
        exact rec10030 9 42 (by decide) (by decide)
      · right
        exact rec10036 9 42 (by decide) (by decide)
      · right
        exact rec10043 9 42 (by decide) (by decide)
      · right
        exact rec10050 9 42 (by decide) (by decide)
      · right
        exact rec10057 9 42 (by decide) (by decide)
      · right
        exact rec10064 9 42 (by decide) (by decide)
      · right
        exact rec10070 9 42 (by decide) (by decide)
      · right
        exact rec10077 9 42 (by decide) (by decide)
      · right
        exact rec10084 9 42 (by decide) (by decide)
      · right
        exact rec10091 9 42 (by decide) (by decide)
      · right
        exact rec10098 9 42 (by decide) (by decide)
      · right
        exact rec10104 9 42 (by decide) (by decide)
      · right
        exact rec10111 9 42 (by decide) (by decide)
      · right
        exact rec10118 9 42 (by decide) (by decide)
      · right
        exact rec10125 9 42 (by decide) (by decide)
      · right
        exact rec10132 9 42 (by decide) (by decide)
      · right
        exact rec10138 9 42 (by decide) (by decide)
      · right
        exact rec10145 9 42 (by decide) (by decide)
      · right
        exact rec10152 9 42 (by decide) (by decide)
      · right
        exact rec10159 9 42 (by decide) (by decide)
      · right
        exact rec10166 9 42 (by decide) (by decide)
      · right
        exact rec10172 9 42 (by decide) (by decide)
      · right
        exact rec10179 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 206)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 207)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10186 9 42 (by decide) (by decide)
      · right
        exact rec10194 9 42 (by decide) (by decide)
      · right
        exact rec10202 9 42 (by decide) (by decide)
      · right
        exact rec10210 9 42 (by decide) (by decide)
      · right
        exact rec10218 9 42 (by decide) (by decide)
      · right
        exact rec10226 9 42 (by decide) (by decide)
      · right
        exact rec10234 9 42 (by decide) (by decide)
      · right
        exact rec10242 9 42 (by decide) (by decide)
      · right
        exact rec10250 9 42 (by decide) (by decide)
      · right
        exact rec10258 9 42 (by decide) (by decide)
      · right
        exact rec10266 9 42 (by decide) (by decide)
      · right
        exact rec10274 9 42 (by decide) (by decide)
      · right
        exact rec10282 9 42 (by decide) (by decide)
      · right
        exact rec10290 9 42 (by decide) (by decide)
      · right
        exact rec10298 9 42 (by decide) (by decide)
      · right
        exact rec10306 9 42 (by decide) (by decide)
      · right
        exact rec10314 9 42 (by decide) (by decide)
      · right
        exact rec10322 9 42 (by decide) (by decide)
      · right
        exact rec10330 9 42 (by decide) (by decide)
      · right
        exact rec10338 9 42 (by decide) (by decide)
      · right
        exact rec10346 9 42 (by decide) (by decide)
      · right
        exact rec10354 9 42 (by decide) (by decide)
      · right
        exact rec10362 9 42 (by decide) (by decide)
      · right
        exact rec10370 9 42 (by decide) (by decide)
      · right
        exact rec10378 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 208)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 209)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 210)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10384 9 42 (by decide) (by decide)
      · right
        exact rec10388 9 42 (by decide) (by decide)
      · right
        exact rec10392 9 42 (by decide) (by decide)
      · right
        exact rec10396 9 42 (by decide) (by decide)
      · right
        exact rec10400 9 42 (by decide) (by decide)
      · right
        exact rec10404 9 42 (by decide) (by decide)
      · right
        exact rec10408 9 42 (by decide) (by decide)
      · right
        exact rec10412 9 42 (by decide) (by decide)
      · right
        exact rec10416 9 42 (by decide) (by decide)
      · right
        exact rec10420 9 42 (by decide) (by decide)
      · right
        exact rec10424 9 42 (by decide) (by decide)
      · right
        exact rec10428 9 42 (by decide) (by decide)
      · right
        exact rec10432 9 42 (by decide) (by decide)
      · right
        exact rec10436 9 42 (by decide) (by decide)
      · right
        exact rec10440 9 42 (by decide) (by decide)
      · right
        exact rec10444 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 211)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 212)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 213)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10450 9 42 (by decide) (by decide)
      · right
        exact rec10458 9 42 (by decide) (by decide)
      · right
        exact rec10466 9 42 (by decide) (by decide)
      · right
        exact rec10474 9 42 (by decide) (by decide)
      · right
        exact rec10482 9 42 (by decide) (by decide)
      · right
        exact rec10490 9 42 (by decide) (by decide)
      · right
        exact rec10501 9 42 (by decide) (by decide)
      · right
        exact rec10509 9 42 (by decide) (by decide)
      · right
        exact rec10517 9 42 (by decide) (by decide)
      · right
        exact rec10525 9 42 (by decide) (by decide)
      · right
        exact rec10533 9 42 (by decide) (by decide)
      · right
        exact rec10541 9 42 (by decide) (by decide)
      · right
        exact rec10549 9 42 (by decide) (by decide)
      · right
        exact rec10557 9 42 (by decide) (by decide)
      · right
        exact rec10565 9 42 (by decide) (by decide)
      · right
        exact rec10573 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 214)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 215)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10579 9 42 (by decide) (by decide)
      · right
        exact rec10583 9 42 (by decide) (by decide)
      · right
        exact rec10587 9 42 (by decide) (by decide)
      · right
        exact rec10591 9 42 (by decide) (by decide)
      · right
        exact rec10595 9 42 (by decide) (by decide)
      · right
        exact rec10599 9 42 (by decide) (by decide)
      · right
        exact rec10603 9 42 (by decide) (by decide)
      · right
        exact rec10607 9 42 (by decide) (by decide)
      · right
        exact rec10611 9 42 (by decide) (by decide)
      · right
        exact rec10615 9 42 (by decide) (by decide)
      · right
        exact rec10619 9 42 (by decide) (by decide)
      · right
        exact rec10623 9 42 (by decide) (by decide)
      · right
        exact rec10627 9 42 (by decide) (by decide)
      · right
        exact rec10631 9 42 (by decide) (by decide)
      · right
        exact rec10635 9 42 (by decide) (by decide)
      · right
        exact rec10639 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 216)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 217)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 218)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10645 9 42 (by decide) (by decide)
      · right
        exact rec10653 9 42 (by decide) (by decide)
      · right
        exact rec10661 9 42 (by decide) (by decide)
      · right
        exact rec10669 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 569)).length = 5 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 220)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10676 9 42 (by decide) (by decide)
      · right
        exact rec10680 9 42 (by decide) (by decide)
      · right
        exact rec10684 9 42 (by decide) (by decide)
      · right
        exact rec10688 9 42 (by decide) (by decide)
      · right
        exact rec10692 9 42 (by decide) (by decide)
      · right
        exact rec10696 9 42 (by decide) (by decide)
      · right
        exact rec10700 9 42 (by decide) (by decide)
      · right
        exact rec10704 9 42 (by decide) (by decide)
      · right
        exact rec10708 9 42 (by decide) (by decide)
      · right
        exact rec10712 9 42 (by decide) (by decide)
      · right
        exact rec10716 9 42 (by decide) (by decide)
      · right
        exact rec10720 9 42 (by decide) (by decide)
      · right
        exact rec10724 9 42 (by decide) (by decide)
      · right
        exact rec10728 9 42 (by decide) (by decide)
      · right
        exact rec10732 9 42 (by decide) (by decide)
      · right
        exact rec10736 9 42 (by decide) (by decide)
      · right
        exact rec10740 9 42 (by decide) (by decide)
      · right
        exact rec10744 9 42 (by decide) (by decide)
      · right
        exact rec10748 9 42 (by decide) (by decide)
      · right
        exact rec10752 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 221)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10758 9 42 (by decide) (by decide)
      · right
        exact rec10766 9 42 (by decide) (by decide)
      · right
        exact rec10774 9 42 (by decide) (by decide)
      · right
        exact rec10782 9 42 (by decide) (by decide)
      · right
        exact rec10790 9 42 (by decide) (by decide)
      · right
        exact rec10798 9 42 (by decide) (by decide)
      · right
        exact rec10806 9 42 (by decide) (by decide)
      · right
        exact rec10814 9 42 (by decide) (by decide)
      · right
        exact rec10822 9 42 (by decide) (by decide)
      · right
        exact rec10830 9 42 (by decide) (by decide)
      · right
        exact rec10838 9 42 (by decide) (by decide)
      · right
        exact rec10846 9 42 (by decide) (by decide)
      · right
        exact rec10854 9 42 (by decide) (by decide)
      · right
        exact rec10862 9 42 (by decide) (by decide)
      · right
        exact rec10870 9 42 (by decide) (by decide)
      · right
        exact rec10878 9 42 (by decide) (by decide)
      · right
        exact rec10886 9 42 (by decide) (by decide)
      · right
        exact rec10894 9 42 (by decide) (by decide)
      · right
        exact rec10902 9 42 (by decide) (by decide)
      · right
        exact rec10911 9 42 (by decide) (by decide)
      · right
        exact rec10919 9 42 (by decide) (by decide)
      · right
        exact rec10927 9 42 (by decide) (by decide)
      · right
        exact rec10935 9 42 (by decide) (by decide)
      · right
        exact rec10943 9 42 (by decide) (by decide)
      · right
        exact rec10952 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 222)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10962 9 42 (by decide) (by decide)
      · right
        exact rec10969 9 42 (by decide) (by decide)
      · right
        exact rec10976 9 42 (by decide) (by decide)
      · right
        exact rec10984 9 42 (by decide) (by decide)
      · right
        exact rec10990 9 42 (by decide) (by decide)
      · right
        exact rec10997 9 42 (by decide) (by decide)
      · right
        exact rec11006 9 42 (by decide) (by decide)
      · right
        exact rec11013 9 42 (by decide) (by decide)
      · right
        exact rec11021 9 42 (by decide) (by decide)
      · right
        exact rec11027 9 42 (by decide) (by decide)
      · right
        exact rec11035 9 42 (by decide) (by decide)
      · right
        exact rec11044 9 42 (by decide) (by decide)
      · right
        exact rec11054 9 42 (by decide) (by decide)
      · right
        exact rec11063 9 42 (by decide) (by decide)
      · right
        exact rec11070 9 42 (by decide) (by decide)
      · right
        exact rec11077 9 42 (by decide) (by decide)
      · right
        exact rec11084 9 42 (by decide) (by decide)
      · right
        exact rec11091 9 42 (by decide) (by decide)
      · right
        exact rec11099 9 42 (by decide) (by decide)
      · right
        exact rec11105 9 42 (by decide) (by decide)
      · right
        exact rec11111 9 42 (by decide) (by decide)
      · right
        exact rec11117 9 42 (by decide) (by decide)
      · right
        exact rec11123 9 42 (by decide) (by decide)
      · right
        exact rec11129 9 42 (by decide) (by decide)
      · right
        exact rec11136 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 223)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 224)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11142 9 42 (by decide) (by decide)
      · right
        exact rec11148 9 42 (by decide) (by decide)
      · right
        exact rec11154 9 42 (by decide) (by decide)
      · right
        exact rec11160 9 42 (by decide) (by decide)
      · right
        exact rec11166 9 42 (by decide) (by decide)
      · right
        exact rec11173 9 42 (by decide) (by decide)
      · right
        exact rec11181 9 42 (by decide) (by decide)
      · right
        exact rec11189 9 42 (by decide) (by decide)
      · right
        exact rec11197 9 42 (by decide) (by decide)
      · right
        exact rec11205 9 42 (by decide) (by decide)
      · right
        exact rec11213 9 42 (by decide) (by decide)
      · right
        exact rec11221 9 42 (by decide) (by decide)
      · right
        exact rec11229 9 42 (by decide) (by decide)
      · right
        exact rec11237 9 42 (by decide) (by decide)
      · right
        exact rec11245 9 42 (by decide) (by decide)
      · right
        exact rec11253 9 42 (by decide) (by decide)
      · right
        exact rec11261 9 42 (by decide) (by decide)
      · right
        exact rec11269 9 42 (by decide) (by decide)
      · right
        exact rec11277 9 42 (by decide) (by decide)
      · right
        exact rec11285 9 42 (by decide) (by decide)
      · right
        exact rec11293 9 42 (by decide) (by decide)
      · right
        exact rec11301 9 42 (by decide) (by decide)
      · right
        exact rec11309 9 42 (by decide) (by decide)
      · right
        exact rec11317 9 42 (by decide) (by decide)
      · right
        exact rec11325 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 225)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11332 9 42 (by decide) (by decide)
      · right
        exact rec11338 9 42 (by decide) (by decide)
      · right
        exact rec11345 9 42 (by decide) (by decide)
      · right
        exact rec11352 9 42 (by decide) (by decide)
      · right
        exact rec11359 9 42 (by decide) (by decide)
      · right
        exact rec11365 9 42 (by decide) (by decide)
      · right
        exact rec11371 9 42 (by decide) (by decide)
      · right
        exact rec11378 9 42 (by decide) (by decide)
      · right
        exact rec11386 9 42 (by decide) (by decide)
      · right
        exact rec11393 9 42 (by decide) (by decide)
      · right
        exact rec11400 9 42 (by decide) (by decide)
      · right
        exact rec11406 9 42 (by decide) (by decide)
      · right
        exact rec11413 9 42 (by decide) (by decide)
      · right
        exact rec11421 9 42 (by decide) (by decide)
      · right
        exact rec11428 9 42 (by decide) (by decide)
      · right
        exact rec11435 9 42 (by decide) (by decide)
      · right
        exact rec11441 9 42 (by decide) (by decide)
      · right
        exact rec11448 9 42 (by decide) (by decide)
      · right
        exact rec11456 9 42 (by decide) (by decide)
      · right
        exact rec11463 9 42 (by decide) (by decide)
      · right
        exact rec11470 9 42 (by decide) (by decide)
      · right
        exact rec11476 9 42 (by decide) (by decide)
      · right
        exact rec11483 9 42 (by decide) (by decide)
      · right
        exact rec11491 9 42 (by decide) (by decide)
      · right
        exact rec11498 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 226)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11506 9 42 (by decide) (by decide)
      · right
        exact rec11512 9 42 (by decide) (by decide)
      · right
        exact rec11518 9 42 (by decide) (by decide)
      · right
        exact rec11524 9 42 (by decide) (by decide)
      · right
        exact rec11530 9 42 (by decide) (by decide)
      · right
        exact rec11536 9 42 (by decide) (by decide)
      · right
        exact rec11542 9 42 (by decide) (by decide)
      · right
        exact rec11548 9 42 (by decide) (by decide)
      · right
        exact rec11554 9 42 (by decide) (by decide)
      · right
        exact rec11560 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 227)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11566 9 42 (by decide) (by decide)
      · right
        exact rec11572 9 42 (by decide) (by decide)
      · right
        exact rec11579 9 42 (by decide) (by decide)
      · right
        exact rec11586 9 42 (by decide) (by decide)
      · right
        exact rec11593 9 42 (by decide) (by decide)
      · right
        exact rec11600 9 42 (by decide) (by decide)
      · right
        exact rec11606 9 42 (by decide) (by decide)
      · right
        exact rec11613 9 42 (by decide) (by decide)
      · right
        exact rec11620 9 42 (by decide) (by decide)
      · right
        exact rec11627 9 42 (by decide) (by decide)
      · right
        exact rec11634 9 42 (by decide) (by decide)
      · right
        exact rec11640 9 42 (by decide) (by decide)
      · right
        exact rec11647 9 42 (by decide) (by decide)
      · right
        exact rec11654 9 42 (by decide) (by decide)
      · right
        exact rec11661 9 42 (by decide) (by decide)
      · right
        exact rec11668 9 42 (by decide) (by decide)
      · right
        exact rec11674 9 42 (by decide) (by decide)
      · right
        exact rec11681 9 42 (by decide) (by decide)
      · right
        exact rec11688 9 42 (by decide) (by decide)
      · right
        exact rec11695 9 42 (by decide) (by decide)
      · right
        exact rec11702 9 42 (by decide) (by decide)
      · right
        exact rec11708 9 42 (by decide) (by decide)
      · right
        exact rec11715 9 42 (by decide) (by decide)
      · right
        exact rec11722 9 42 (by decide) (by decide)
      · right
        exact rec11729 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 228)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11737 9 42 (by decide) (by decide)
      · right
        exact rec11744 9 42 (by decide) (by decide)
      · right
        exact rec11754 9 42 (by decide) (by decide)
      · right
        exact rec11761 9 42 (by decide) (by decide)
      · right
        exact rec11767 9 42 (by decide) (by decide)
      · right
        exact rec11773 9 42 (by decide) (by decide)
      · right
        exact rec11779 9 42 (by decide) (by decide)
      · right
        exact rec11785 9 42 (by decide) (by decide)
      · right
        exact rec11791 9 42 (by decide) (by decide)
      · right
        exact rec11798 9 42 (by decide) (by decide)
      · right
        exact rec11804 9 42 (by decide) (by decide)
      · right
        exact rec11810 9 42 (by decide) (by decide)
      · right
        exact rec11816 9 42 (by decide) (by decide)
      · right
        exact rec11822 9 42 (by decide) (by decide)
      · right
        exact rec11828 9 42 (by decide) (by decide)
      · right
        exact rec11834 9 42 (by decide) (by decide)
      · right
        exact rec11840 9 42 (by decide) (by decide)
      · right
        exact rec11846 9 42 (by decide) (by decide)
      · right
        exact rec11852 9 42 (by decide) (by decide)
      · right
        exact rec11858 9 42 (by decide) (by decide)
      · right
        exact rec11864 9 42 (by decide) (by decide)
      · right
        exact rec11870 9 42 (by decide) (by decide)
      · right
        exact rec11876 9 42 (by decide) (by decide)
      · right
        exact rec11882 9 42 (by decide) (by decide)
      · right
        exact rec11888 9 42 (by decide) (by decide)
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
        exact rec11894 9 42 (by decide) (by decide)
      · right
        exact rec11900 9 42 (by decide) (by decide)
      · right
        exact rec11907 9 42 (by decide) (by decide)
      · right
        exact rec11913 9 42 (by decide) (by decide)
      · right
        exact rec11919 9 42 (by decide) (by decide)
      · right
        exact rec11925 9 42 (by decide) (by decide)
      · right
        exact rec11931 9 42 (by decide) (by decide)
      · right
        exact rec11940 9 42 (by decide) (by decide)
      · right
        exact rec11947 9 42 (by decide) (by decide)
      · right
        exact rec11955 9 42 (by decide) (by decide)
      · right
        exact rec11962 9 42 (by decide) (by decide)
      · right
        exact rec11968 9 42 (by decide) (by decide)
      · right
        exact rec11976 9 42 (by decide) (by decide)
      · right
        exact rec11982 9 42 (by decide) (by decide)
      · right
        exact rec11990 9 42 (by decide) (by decide)
      · right
        exact rec11997 9 42 (by decide) (by decide)
      · right
        exact rec12003 9 42 (by decide) (by decide)
      · right
        exact rec12010 9 42 (by decide) (by decide)
      · right
        exact rec12017 9 42 (by decide) (by decide)
      · right
        exact rec12024 9 42 (by decide) (by decide)
      · right
        exact rec12031 9 42 (by decide) (by decide)
      · right
        exact rec12037 9 42 (by decide) (by decide)
      · right
        exact rec12044 9 42 (by decide) (by decide)
      · right
        exact rec12051 9 42 (by decide) (by decide)
      · right
        exact rec12058 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 231)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12066 9 42 (by decide) (by decide)
      · right
        exact rec12073 9 42 (by decide) (by decide)
      · right
        exact rec12080 9 42 (by decide) (by decide)
      · right
        exact rec12086 9 42 (by decide) (by decide)
      · right
        exact rec12093 9 42 (by decide) (by decide)
      · right
        exact rec12100 9 42 (by decide) (by decide)
      · right
        exact rec12107 9 42 (by decide) (by decide)
      · right
        exact rec12113 9 42 (by decide) (by decide)
      · right
        exact rec12119 9 42 (by decide) (by decide)
      · right
        exact rec12125 9 42 (by decide) (by decide)
      · right
        exact rec12131 9 42 (by decide) (by decide)
      · right
        exact rec12137 9 42 (by decide) (by decide)
      · right
        exact rec12143 9 42 (by decide) (by decide)
      · right
        exact rec12149 9 42 (by decide) (by decide)
      · right
        exact rec12155 9 42 (by decide) (by decide)
      · right
        exact rec12161 9 42 (by decide) (by decide)
      · right
        exact rec12167 9 42 (by decide) (by decide)
      · right
        exact rec12173 9 42 (by decide) (by decide)
      · right
        exact rec12179 9 42 (by decide) (by decide)
      · right
        exact rec12185 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 232)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12191 9 42 (by decide) (by decide)
      · right
        exact rec12197 9 42 (by decide) (by decide)
      · right
        exact rec12204 9 42 (by decide) (by decide)
      · right
        exact rec12210 9 42 (by decide) (by decide)
      · right
        exact rec12218 9 42 (by decide) (by decide)
      · right
        exact rec12224 9 42 (by decide) (by decide)
      · right
        exact rec12230 9 42 (by decide) (by decide)
      · right
        exact rec12237 9 42 (by decide) (by decide)
      · right
        exact rec12243 9 42 (by decide) (by decide)
      · right
        exact rec12250 9 42 (by decide) (by decide)
      · right
        exact rec12257 9 42 (by decide) (by decide)
      · right
        exact rec12263 9 42 (by decide) (by decide)
      · right
        exact rec12270 9 42 (by decide) (by decide)
      · right
        exact rec12276 9 42 (by decide) (by decide)
      · right
        exact rec12283 9 42 (by decide) (by decide)
      · right
        exact rec12290 9 42 (by decide) (by decide)
      · right
        exact rec12296 9 42 (by decide) (by decide)
      · right
        exact rec12303 9 42 (by decide) (by decide)
      · right
        exact rec12309 9 42 (by decide) (by decide)
      · right
        exact rec12316 9 42 (by decide) (by decide)
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 234)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12323 9 42 (by decide) (by decide)
      · right
        exact rec12330 9 42 (by decide) (by decide)
      · right
        exact rec12338 9 42 (by decide) (by decide)
      · right
        exact rec12346 9 42 (by decide) (by decide)
      · right
        exact rec12353 9 42 (by decide) (by decide)
      · right
        exact rec12360 9 42 (by decide) (by decide)
      · right
        exact rec12368 9 42 (by decide) (by decide)
      · right
        exact rec12376 9 42 (by decide) (by decide)
      · right
        exact rec12383 9 42 (by decide) (by decide)
      · right
        exact rec12390 9 42 (by decide) (by decide)
      · right
        exact rec12398 9 42 (by decide) (by decide)
      · right
        exact rec12406 9 42 (by decide) (by decide)
      · right
        exact rec12413 9 42 (by decide) (by decide)
      · right
        exact rec12420 9 42 (by decide) (by decide)
      · right
        exact rec12428 9 42 (by decide) (by decide)
      · right
        exact rec12436 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 235)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12443 9 42 (by decide) (by decide)
      · right
        exact rec12449 9 42 (by decide) (by decide)
      · right
        exact rec12456 9 42 (by decide) (by decide)
      · right
        exact rec12463 9 42 (by decide) (by decide)
      · right
        exact rec12469 9 42 (by decide) (by decide)
      · right
        exact rec12475 9 42 (by decide) (by decide)
      · right
        exact rec12482 9 42 (by decide) (by decide)
      · right
        exact rec12489 9 42 (by decide) (by decide)
      · right
        exact rec12495 9 42 (by decide) (by decide)
      · right
        exact rec12501 9 42 (by decide) (by decide)
      · right
        exact rec12508 9 42 (by decide) (by decide)
      · right
        exact rec12515 9 42 (by decide) (by decide)
      · right
        exact rec12521 9 42 (by decide) (by decide)
      · right
        exact rec12527 9 42 (by decide) (by decide)
      · right
        exact rec12534 9 42 (by decide) (by decide)
      · right
        exact rec12541 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 236)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12548 9 42 (by decide) (by decide)
      · right
        exact rec12555 9 42 (by decide) (by decide)
      · right
        exact rec12563 9 42 (by decide) (by decide)
      · right
        exact rec12571 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 237)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12578 9 42 (by decide) (by decide)
      · right
        exact rec12584 9 42 (by decide) (by decide)
      · right
        exact rec12591 9 42 (by decide) (by decide)
      · right
        exact rec12598 9 42 (by decide) (by decide)
      · right
        exact rec12606 9 42 (by decide) (by decide)
      · right
        exact rec12612 9 42 (by decide) (by decide)
      · right
        exact rec12618 9 42 (by decide) (by decide)
      · right
        exact rec12624 9 42 (by decide) (by decide)
      · right
        exact rec12632 9 42 (by decide) (by decide)
      · right
        exact rec12639 9 42 (by decide) (by decide)
      · right
        exact rec12645 9 42 (by decide) (by decide)
      · right
        exact rec12651 9 42 (by decide) (by decide)
      · right
        exact rec12658 9 42 (by decide) (by decide)
      · right
        exact rec12664 9 42 (by decide) (by decide)
      · right
        exact rec12670 9 42 (by decide) (by decide)
      · right
        exact rec12676 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 238)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12682 9 42 (by decide) (by decide)
      · right
        exact rec12688 9 42 (by decide) (by decide)
      · right
        exact rec12695 9 42 (by decide) (by decide)
      · right
        exact rec12703 9 42 (by decide) (by decide)
      · right
        exact rec12709 9 42 (by decide) (by decide)
      · right
        exact rec12715 9 42 (by decide) (by decide)
      · right
        exact rec12722 9 42 (by decide) (by decide)
      · right
        exact rec12729 9 42 (by decide) (by decide)
      · right
        exact rec12735 9 42 (by decide) (by decide)
      · right
        exact rec12741 9 42 (by decide) (by decide)
      · right
        exact rec12748 9 42 (by decide) (by decide)
      · right
        exact rec12755 9 42 (by decide) (by decide)
      · right
        exact rec12761 9 42 (by decide) (by decide)
      · right
        exact rec12767 9 42 (by decide) (by decide)
      · right
        exact rec12774 9 42 (by decide) (by decide)
      · right
        exact rec12781 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 239)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 240)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 241)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 242)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12786 9 42 (by decide) (by decide)
      · right
        exact rec12790 9 42 (by decide) (by decide)
      · right
        exact rec12794 9 42 (by decide) (by decide)
      · right
        exact rec12798 9 42 (by decide) (by decide)
      · right
        exact rec12802 9 42 (by decide) (by decide)
      · right
        exact rec12806 9 42 (by decide) (by decide)
      · right
        exact rec12810 9 42 (by decide) (by decide)
      · right
        exact rec12814 9 42 (by decide) (by decide)
      · right
        exact rec12818 9 42 (by decide) (by decide)
      · right
        exact rec12822 9 42 (by decide) (by decide)
      · right
        exact rec12826 9 42 (by decide) (by decide)
      · right
        exact rec12830 9 42 (by decide) (by decide)
      · right
        exact rec12834 9 42 (by decide) (by decide)
      · right
        exact rec12838 9 42 (by decide) (by decide)
      · right
        exact rec12842 9 42 (by decide) (by decide)
      · right
        exact rec12846 9 42 (by decide) (by decide)
      · right
        exact rec12850 9 42 (by decide) (by decide)
      · right
        exact rec12854 9 42 (by decide) (by decide)
      · right
        exact rec12858 9 42 (by decide) (by decide)
      · right
        exact rec12862 9 42 (by decide) (by decide)
      · right
        exact rec12866 9 42 (by decide) (by decide)
      · right
        exact rec12870 9 42 (by decide) (by decide)
      · right
        exact rec12874 9 42 (by decide) (by decide)
      · right
        exact rec12878 9 42 (by decide) (by decide)
      · right
        exact rec12882 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 570)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 244)).length = 10 := by decide +kernel
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
    exact rec7430 9 43 (by decide) (by decide)
  · left
    exact rec7425 9 44 (by decide) (by decide)
  · left
    exact rec7425 9 45 (by decide) (by decide)
  · left
    exact rec7432 9 46 (by decide) (by decide)
  · left
    exact rec7430 9 47 (by decide) (by decide)
end Section14Coverage_9_5_p32_48

#print axioms solution
