-- Prove2me | solution 1 for Freiman.section14_s0010_coverage0005_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:17:11.378524+00:00
-- url     : https://prove2.me/submissions/a63e4576-c1a8-4d5e-8772-fbdab6b27e7b

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
namespace Section14Coverage_10_5_p32_48
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
private theorem rec7753 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(0),[10],[42],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[69]? = some (⟨163,(0),[10],[42],406⟩) from rfl))
private theorem rec7761 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(1),[10],[42],407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[77]? = some (⟨163,(1),[10],[42],407⟩) from rfl))
private theorem rec7769 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(2),[10],[42],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[85]? = some (⟨163,(2),[10],[42],406⟩) from rfl))
private theorem rec7777 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(3),[10],[42],408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[93]? = some (⟨163,(3),[10],[42],408⟩) from rfl))
private theorem rec7785 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(4),[10],[42],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[101]? = some (⟨163,(4),[10],[42],409⟩) from rfl))
private theorem rec7793 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(5),[10],[42],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[109]? = some (⟨163,(5),[10],[42],409⟩) from rfl))
private theorem rec7801 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(6),[10],[42],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[117]? = some (⟨163,(6),[10],[42],409⟩) from rfl))
private theorem rec7809 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(7),[10],[42],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[125]? = some (⟨163,(7),[10],[42],409⟩) from rfl))
private theorem rec7817 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(8),[10],[42],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[133]? = some (⟨163,(8),[10],[42],410⟩) from rfl))
private theorem rec7825 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(9),[10],[42],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[141]? = some (⟨163,(9),[10],[42],410⟩) from rfl))
private theorem rec7833 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(10),[10],[42],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[149]? = some (⟨163,(10),[10],[42],410⟩) from rfl))
private theorem rec7841 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(11),[10],[42],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[157]? = some (⟨163,(11),[10],[42],410⟩) from rfl))
private theorem rec7849 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(12),[10],[42],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[165]? = some (⟨163,(12),[10],[42],411⟩) from rfl))
private theorem rec7857 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(13),[10],[42],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[173]? = some (⟨163,(13),[10],[42],411⟩) from rfl))
private theorem rec7865 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(14),[10],[42],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[181]? = some (⟨163,(14),[10],[42],411⟩) from rfl))
private theorem rec7873 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 163 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(15),[10],[42],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[189]? = some (⟨163,(15),[10],[42],411⟩) from rfl))
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
private theorem rec7993 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(0),[10],[42],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[309]? = some (⟨167,(0),[10],[42],418⟩) from rfl))
private theorem rec8001 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(1),[10],[42],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[317]? = some (⟨167,(1),[10],[42],419⟩) from rfl))
private theorem rec8009 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(2),[10],[42],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[325]? = some (⟨167,(2),[10],[42],420⟩) from rfl))
private theorem rec8017 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(3),[10],[42],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[333]? = some (⟨167,(3),[10],[42],421⟩) from rfl))
private theorem rec8025 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(4),[10],[42],422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[341]? = some (⟨167,(4),[10],[42],422⟩) from rfl))
private theorem rec8033 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(5),[10],[42],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[349]? = some (⟨167,(5),[10],[42],419⟩) from rfl))
private theorem rec8041 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(6),[10],[42],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[357]? = some (⟨167,(6),[10],[42],420⟩) from rfl))
private theorem rec8049 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(7),[10],[42],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[365]? = some (⟨167,(7),[10],[42],421⟩) from rfl))
private theorem rec8057 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(8),[10],[42],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[373]? = some (⟨167,(8),[10],[42],418⟩) from rfl))
private theorem rec8065 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(9),[10],[42],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[381]? = some (⟨167,(9),[10],[42],419⟩) from rfl))
private theorem rec8073 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(10),[10],[42],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[389]? = some (⟨167,(10),[10],[42],420⟩) from rfl))
private theorem rec8081 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(11),[10],[42],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[397]? = some (⟨167,(11),[10],[42],421⟩) from rfl))
private theorem rec8089 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(12),[10],[42],423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[405]? = some (⟨167,(12),[10],[42],423⟩) from rfl))
private theorem rec8097 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(13),[10],[42],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[413]? = some (⟨167,(13),[10],[42],419⟩) from rfl))
private theorem rec8105 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(14),[10],[42],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[421]? = some (⟨167,(14),[10],[42],420⟩) from rfl))
private theorem rec8113 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 167 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(15),[10],[42],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[429]? = some (⟨167,(15),[10],[42],421⟩) from rfl))
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
private theorem rec8149 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(0),[10],[42],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[465]? = some (⟨172,(0),[10],[42],428⟩) from rfl))
private theorem rec8157 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(1),[10],[42],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[473]? = some (⟨172,(1),[10],[42],429⟩) from rfl))
private theorem rec8165 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(2),[10],[42],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[481]? = some (⟨172,(2),[10],[42],430⟩) from rfl))
private theorem rec8173 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(3),[10],[42],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[489]? = some (⟨172,(3),[10],[42],431⟩) from rfl))
private theorem rec8181 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(4),[10],[42],432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[497]? = some (⟨172,(4),[10],[42],432⟩) from rfl))
private theorem rec8189 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(5),[10],[42],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[505]? = some (⟨172,(5),[10],[42],429⟩) from rfl))
private theorem rec8197 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(6),[10],[42],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[513]? = some (⟨172,(6),[10],[42],430⟩) from rfl))
private theorem rec8205 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(7),[10],[42],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[521]? = some (⟨172,(7),[10],[42],431⟩) from rfl))
private theorem rec8213 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(8),[10],[42],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[529]? = some (⟨172,(8),[10],[42],428⟩) from rfl))
private theorem rec8221 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(9),[10],[42],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[537]? = some (⟨172,(9),[10],[42],429⟩) from rfl))
private theorem rec8229 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(10),[10],[42],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[545]? = some (⟨172,(10),[10],[42],430⟩) from rfl))
private theorem rec8237 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(11),[10],[42],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[553]? = some (⟨172,(11),[10],[42],431⟩) from rfl))
private theorem rec8245 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(12),[10],[42],433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[561]? = some (⟨172,(12),[10],[42],433⟩) from rfl))
private theorem rec8253 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(13),[10],[42],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[569]? = some (⟨172,(13),[10],[42],429⟩) from rfl))
private theorem rec8261 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(14),[10],[42],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[577]? = some (⟨172,(14),[10],[42],430⟩) from rfl))
private theorem rec8269 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 172 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(15),[10],[42],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[585]? = some (⟨172,(15),[10],[42],431⟩) from rfl))
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
private theorem rec8389 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(0),[10],[42],660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[90]? = some (⟨178,(0),[10],[42],660⟩) from rfl))
private theorem rec8397 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(1),[10],[42],661⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[98]? = some (⟨178,(1),[10],[42],661⟩) from rfl))
private theorem rec8405 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(2),[10],[42],660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[106]? = some (⟨178,(2),[10],[42],660⟩) from rfl))
private theorem rec8413 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(3),[10],[42],662⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[114]? = some (⟨178,(3),[10],[42],662⟩) from rfl))
private theorem rec8421 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(4),[10],[42],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[122]? = some (⟨178,(4),[10],[42],663⟩) from rfl))
private theorem rec8429 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(5),[10],[42],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[130]? = some (⟨178,(5),[10],[42],663⟩) from rfl))
private theorem rec8437 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(6),[10],[42],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[138]? = some (⟨178,(6),[10],[42],663⟩) from rfl))
private theorem rec8445 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(7),[10],[42],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[146]? = some (⟨178,(7),[10],[42],663⟩) from rfl))
private theorem rec8453 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(8),[10],[42],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[154]? = some (⟨178,(8),[10],[42],664⟩) from rfl))
private theorem rec8461 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(9),[10],[42],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[162]? = some (⟨178,(9),[10],[42],664⟩) from rfl))
private theorem rec8469 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(10),[10],[42],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[170]? = some (⟨178,(10),[10],[42],664⟩) from rfl))
private theorem rec8477 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(11),[10],[42],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[178]? = some (⟨178,(11),[10],[42],664⟩) from rfl))
private theorem rec8485 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(12),[10],[42],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[186]? = some (⟨178,(12),[10],[42],665⟩) from rfl))
private theorem rec8493 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(13),[10],[42],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[194]? = some (⟨178,(13),[10],[42],665⟩) from rfl))
private theorem rec8501 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(14),[10],[42],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[202]? = some (⟨178,(14),[10],[42],665⟩) from rfl))
private theorem rec8509 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 178 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(15),[10],[42],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[210]? = some (⟨178,(15),[10],[42],665⟩) from rfl))
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
private theorem rec8629 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(0),[10],[42],672⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[330]? = some (⟨183,(0),[10],[42],672⟩) from rfl))
private theorem rec8637 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(1),[10],[42],673⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[338]? = some (⟨183,(1),[10],[42],673⟩) from rfl))
private theorem rec8645 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(2),[10],[42],672⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[346]? = some (⟨183,(2),[10],[42],672⟩) from rfl))
private theorem rec8653 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(3),[10],[42],674⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[354]? = some (⟨183,(3),[10],[42],674⟩) from rfl))
private theorem rec8661 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(4),[10],[42],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[362]? = some (⟨183,(4),[10],[42],675⟩) from rfl))
private theorem rec8669 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(5),[10],[42],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[370]? = some (⟨183,(5),[10],[42],675⟩) from rfl))
private theorem rec8677 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(6),[10],[42],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[378]? = some (⟨183,(6),[10],[42],675⟩) from rfl))
private theorem rec8685 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(7),[10],[42],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[386]? = some (⟨183,(7),[10],[42],675⟩) from rfl))
private theorem rec8693 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(8),[10],[42],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[394]? = some (⟨183,(8),[10],[42],676⟩) from rfl))
private theorem rec8701 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(9),[10],[42],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[402]? = some (⟨183,(9),[10],[42],676⟩) from rfl))
private theorem rec8709 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(10),[10],[42],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[410]? = some (⟨183,(10),[10],[42],676⟩) from rfl))
private theorem rec8717 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(11),[10],[42],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[418]? = some (⟨183,(11),[10],[42],676⟩) from rfl))
private theorem rec8725 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(12),[10],[42],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[426]? = some (⟨183,(12),[10],[42],677⟩) from rfl))
private theorem rec8733 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(13),[10],[42],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[434]? = some (⟨183,(13),[10],[42],677⟩) from rfl))
private theorem rec8741 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(14),[10],[42],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[442]? = some (⟨183,(14),[10],[42],677⟩) from rfl))
private theorem rec8749 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 183 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(15),[10],[42],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[450]? = some (⟨183,(15),[10],[42],677⟩) from rfl))
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
private theorem rec8869 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(0),[10],[42],684⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[570]? = some (⟨188,(0),[10],[42],684⟩) from rfl))
private theorem rec8877 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(1),[10],[42],685⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[578]? = some (⟨188,(1),[10],[42],685⟩) from rfl))
private theorem rec8885 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(2),[10],[42],684⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[586]? = some (⟨188,(2),[10],[42],684⟩) from rfl))
private theorem rec8893 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(3),[10],[42],686⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[594]? = some (⟨188,(3),[10],[42],686⟩) from rfl))
private theorem rec8901 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(4),[10],[42],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[602]? = some (⟨188,(4),[10],[42],687⟩) from rfl))
private theorem rec8909 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(5),[10],[42],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[610]? = some (⟨188,(5),[10],[42],687⟩) from rfl))
private theorem rec8917 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(6),[10],[42],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[618]? = some (⟨188,(6),[10],[42],687⟩) from rfl))
private theorem rec8925 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(7),[10],[42],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[626]? = some (⟨188,(7),[10],[42],687⟩) from rfl))
private theorem rec8933 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(8),[10],[42],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[634]? = some (⟨188,(8),[10],[42],688⟩) from rfl))
private theorem rec8941 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(9),[10],[42],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[642]? = some (⟨188,(9),[10],[42],688⟩) from rfl))
private theorem rec8949 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(10),[10],[42],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[650]? = some (⟨188,(10),[10],[42],688⟩) from rfl))
private theorem rec8957 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(11),[10],[42],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[658]? = some (⟨188,(11),[10],[42],688⟩) from rfl))
private theorem rec8965 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(12),[10],[42],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[666]? = some (⟨188,(12),[10],[42],689⟩) from rfl))
private theorem rec8973 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(13),[10],[42],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[674]? = some (⟨188,(13),[10],[42],689⟩) from rfl))
private theorem rec8981 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(14),[10],[42],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[682]? = some (⟨188,(14),[10],[42],689⟩) from rfl))
private theorem rec8989 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 188 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(15),[10],[42],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[690]? = some (⟨188,(15),[10],[42],689⟩) from rfl))
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
private theorem rec9172 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(0),[10],[42],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[873]? = some (⟨192,(0),[10],[42],441⟩) from rfl))
private theorem rec9180 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(1),[10],[42],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[881]? = some (⟨192,(1),[10],[42],442⟩) from rfl))
private theorem rec9188 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(2),[10],[42],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[889]? = some (⟨192,(2),[10],[42],441⟩) from rfl))
private theorem rec9196 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(3),[10],[42],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[897]? = some (⟨192,(3),[10],[42],443⟩) from rfl))
private theorem rec9204 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(4),[10],[42],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[905]? = some (⟨192,(4),[10],[42],444⟩) from rfl))
private theorem rec9212 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(5),[10],[42],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[913]? = some (⟨192,(5),[10],[42],441⟩) from rfl))
private theorem rec9220 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(6),[10],[42],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[921]? = some (⟨192,(6),[10],[42],442⟩) from rfl))
private theorem rec9228 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(7),[10],[42],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[929]? = some (⟨192,(7),[10],[42],441⟩) from rfl))
private theorem rec9236 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(8),[10],[42],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[937]? = some (⟨192,(8),[10],[42],443⟩) from rfl))
private theorem rec9244 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(9),[10],[42],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[945]? = some (⟨192,(9),[10],[42],444⟩) from rfl))
private theorem rec9252 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(10),[10],[42],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[953]? = some (⟨192,(10),[10],[42],445⟩) from rfl))
private theorem rec9260 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(11),[10],[42],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[961]? = some (⟨192,(11),[10],[42],445⟩) from rfl))
private theorem rec9268 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(12),[10],[42],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[969]? = some (⟨192,(12),[10],[42],445⟩) from rfl))
private theorem rec9276 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(13),[10],[42],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[977]? = some (⟨192,(13),[10],[42],445⟩) from rfl))
private theorem rec9284 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(14),[10],[42],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[985]? = some (⟨192,(14),[10],[42],444⟩) from rfl))
private theorem rec9292 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(15),[10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[993]? = some (⟨192,(15),[10],[42],446⟩) from rfl))
private theorem rec9300 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(16),[10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1001]? = some (⟨192,(16),[10],[42],446⟩) from rfl))
private theorem rec9308 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(17),[10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1009]? = some (⟨192,(17),[10],[42],446⟩) from rfl))
private theorem rec9316 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(18),[10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1017]? = some (⟨192,(18),[10],[42],446⟩) from rfl))
private theorem rec9324 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(19),[10],[42],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1025]? = some (⟨192,(19),[10],[42],446⟩) from rfl))
private theorem rec9332 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(20),[10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1033]? = some (⟨192,(20),[10],[42],447⟩) from rfl))
private theorem rec9340 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(21),[10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1041]? = some (⟨192,(21),[10],[42],447⟩) from rfl))
private theorem rec9348 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(22),[10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1049]? = some (⟨192,(22),[10],[42],447⟩) from rfl))
private theorem rec9356 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(23),[10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1057]? = some (⟨192,(23),[10],[42],447⟩) from rfl))
private theorem rec9364 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 192 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(24),[10],[42],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1065]? = some (⟨192,(24),[10],[42],447⟩) from rfl))
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
private theorem rec9442 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(0),[10],[42],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1143]? = some (⟨197,(0),[10],[42],453⟩) from rfl))
private theorem rec9450 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(1),[10],[42],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1151]? = some (⟨197,(1),[10],[42],454⟩) from rfl))
private theorem rec9458 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(2),[10],[42],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1159]? = some (⟨197,(2),[10],[42],453⟩) from rfl))
private theorem rec9466 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(3),[10],[42],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1167]? = some (⟨197,(3),[10],[42],455⟩) from rfl))
private theorem rec9474 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(4),[10],[42],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1175]? = some (⟨197,(4),[10],[42],456⟩) from rfl))
private theorem rec9482 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(5),[10],[42],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1183]? = some (⟨197,(5),[10],[42],453⟩) from rfl))
private theorem rec9490 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(6),[10],[42],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1191]? = some (⟨197,(6),[10],[42],454⟩) from rfl))
private theorem rec9498 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(7),[10],[42],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1199]? = some (⟨197,(7),[10],[42],453⟩) from rfl))
private theorem rec9506 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(8),[10],[42],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1207]? = some (⟨197,(8),[10],[42],455⟩) from rfl))
private theorem rec9514 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(9),[10],[42],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1215]? = some (⟨197,(9),[10],[42],456⟩) from rfl))
private theorem rec9522 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(10),[10],[42],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[4]? = some (⟨197,(10),[10],[42],457⟩) from rfl))
private theorem rec9530 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(11),[10],[42],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[12]? = some (⟨197,(11),[10],[42],457⟩) from rfl))
private theorem rec9538 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(12),[10],[42],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[20]? = some (⟨197,(12),[10],[42],457⟩) from rfl))
private theorem rec9546 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(13),[10],[42],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[28]? = some (⟨197,(13),[10],[42],457⟩) from rfl))
private theorem rec9554 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(14),[10],[42],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[36]? = some (⟨197,(14),[10],[42],456⟩) from rfl))
private theorem rec9562 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(15),[10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[44]? = some (⟨197,(15),[10],[42],458⟩) from rfl))
private theorem rec9570 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(16),[10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[52]? = some (⟨197,(16),[10],[42],458⟩) from rfl))
private theorem rec9578 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(17),[10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[60]? = some (⟨197,(17),[10],[42],458⟩) from rfl))
private theorem rec9586 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(18),[10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[68]? = some (⟨197,(18),[10],[42],458⟩) from rfl))
private theorem rec9594 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(19),[10],[42],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[76]? = some (⟨197,(19),[10],[42],458⟩) from rfl))
private theorem rec9602 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(20),[10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[84]? = some (⟨197,(20),[10],[42],459⟩) from rfl))
private theorem rec9610 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(21),[10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[92]? = some (⟨197,(21),[10],[42],459⟩) from rfl))
private theorem rec9618 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(22),[10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[100]? = some (⟨197,(22),[10],[42],459⟩) from rfl))
private theorem rec9626 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(23),[10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[108]? = some (⟨197,(23),[10],[42],459⟩) from rfl))
private theorem rec9634 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 197 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(24),[10],[42],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[116]? = some (⟨197,(24),[10],[42],459⟩) from rfl))
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
private theorem rec9817 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(0),[10],[42],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[299]? = some (⟨202,(0),[10],[42],467⟩) from rfl))
private theorem rec9825 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(1),[10],[42],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[307]? = some (⟨202,(1),[10],[42],468⟩) from rfl))
private theorem rec9833 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(2),[10],[42],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[315]? = some (⟨202,(2),[10],[42],467⟩) from rfl))
private theorem rec9841 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(3),[10],[42],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[323]? = some (⟨202,(3),[10],[42],469⟩) from rfl))
private theorem rec9849 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(4),[10],[42],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[331]? = some (⟨202,(4),[10],[42],470⟩) from rfl))
private theorem rec9857 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(5),[10],[42],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[339]? = some (⟨202,(5),[10],[42],467⟩) from rfl))
private theorem rec9865 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(6),[10],[42],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[347]? = some (⟨202,(6),[10],[42],468⟩) from rfl))
private theorem rec9873 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(7),[10],[42],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[355]? = some (⟨202,(7),[10],[42],467⟩) from rfl))
private theorem rec9881 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(8),[10],[42],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[363]? = some (⟨202,(8),[10],[42],469⟩) from rfl))
private theorem rec9889 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(9),[10],[42],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[371]? = some (⟨202,(9),[10],[42],470⟩) from rfl))
private theorem rec9897 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(10),[10],[42],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[379]? = some (⟨202,(10),[10],[42],471⟩) from rfl))
private theorem rec9905 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(11),[10],[42],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[387]? = some (⟨202,(11),[10],[42],471⟩) from rfl))
private theorem rec9913 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(12),[10],[42],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[395]? = some (⟨202,(12),[10],[42],471⟩) from rfl))
private theorem rec9921 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(13),[10],[42],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[403]? = some (⟨202,(13),[10],[42],471⟩) from rfl))
private theorem rec9929 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(14),[10],[42],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[411]? = some (⟨202,(14),[10],[42],470⟩) from rfl))
private theorem rec9937 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(15),[10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[419]? = some (⟨202,(15),[10],[42],472⟩) from rfl))
private theorem rec9945 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(16),[10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[427]? = some (⟨202,(16),[10],[42],472⟩) from rfl))
private theorem rec9953 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(17),[10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[435]? = some (⟨202,(17),[10],[42],472⟩) from rfl))
private theorem rec9961 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(18),[10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[443]? = some (⟨202,(18),[10],[42],472⟩) from rfl))
private theorem rec9969 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(19),[10],[42],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[451]? = some (⟨202,(19),[10],[42],472⟩) from rfl))
private theorem rec9977 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(20),[10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[459]? = some (⟨202,(20),[10],[42],473⟩) from rfl))
private theorem rec9985 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(21),[10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[467]? = some (⟨202,(21),[10],[42],473⟩) from rfl))
private theorem rec9993 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(22),[10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[475]? = some (⟨202,(22),[10],[42],473⟩) from rfl))
private theorem rec10001 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(23),[10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[483]? = some (⟨202,(23),[10],[42],473⟩) from rfl))
private theorem rec10009 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 202 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(24),[10],[42],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[491]? = some (⟨202,(24),[10],[42],473⟩) from rfl))
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
private theorem rec10187 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(0),[10],[42],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[669]? = some (⟨207,(0),[10],[42],481⟩) from rfl))
private theorem rec10195 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(1),[10],[42],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[677]? = some (⟨207,(1),[10],[42],482⟩) from rfl))
private theorem rec10203 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(2),[10],[42],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[685]? = some (⟨207,(2),[10],[42],481⟩) from rfl))
private theorem rec10211 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(3),[10],[42],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[693]? = some (⟨207,(3),[10],[42],483⟩) from rfl))
private theorem rec10219 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(4),[10],[42],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[701]? = some (⟨207,(4),[10],[42],484⟩) from rfl))
private theorem rec10227 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(5),[10],[42],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[709]? = some (⟨207,(5),[10],[42],481⟩) from rfl))
private theorem rec10235 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(6),[10],[42],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[717]? = some (⟨207,(6),[10],[42],482⟩) from rfl))
private theorem rec10243 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(7),[10],[42],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[725]? = some (⟨207,(7),[10],[42],481⟩) from rfl))
private theorem rec10251 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(8),[10],[42],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[733]? = some (⟨207,(8),[10],[42],483⟩) from rfl))
private theorem rec10259 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(9),[10],[42],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[741]? = some (⟨207,(9),[10],[42],484⟩) from rfl))
private theorem rec10267 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(10),[10],[42],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[749]? = some (⟨207,(10),[10],[42],485⟩) from rfl))
private theorem rec10275 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(11),[10],[42],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[757]? = some (⟨207,(11),[10],[42],485⟩) from rfl))
private theorem rec10283 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(12),[10],[42],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[765]? = some (⟨207,(12),[10],[42],485⟩) from rfl))
private theorem rec10291 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(13),[10],[42],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[773]? = some (⟨207,(13),[10],[42],485⟩) from rfl))
private theorem rec10299 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(14),[10],[42],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[781]? = some (⟨207,(14),[10],[42],484⟩) from rfl))
private theorem rec10307 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(15),[10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[789]? = some (⟨207,(15),[10],[42],486⟩) from rfl))
private theorem rec10315 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(16),[10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[797]? = some (⟨207,(16),[10],[42],486⟩) from rfl))
private theorem rec10323 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(17),[10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[805]? = some (⟨207,(17),[10],[42],486⟩) from rfl))
private theorem rec10331 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(18),[10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[813]? = some (⟨207,(18),[10],[42],486⟩) from rfl))
private theorem rec10339 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(19),[10],[42],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[821]? = some (⟨207,(19),[10],[42],486⟩) from rfl))
private theorem rec10347 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(20),[10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[829]? = some (⟨207,(20),[10],[42],487⟩) from rfl))
private theorem rec10355 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(21),[10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[837]? = some (⟨207,(21),[10],[42],487⟩) from rfl))
private theorem rec10363 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(22),[10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[845]? = some (⟨207,(22),[10],[42],487⟩) from rfl))
private theorem rec10371 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(23),[10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[853]? = some (⟨207,(23),[10],[42],487⟩) from rfl))
private theorem rec10379 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 207 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(24),[10],[42],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[861]? = some (⟨207,(24),[10],[42],487⟩) from rfl))
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
private theorem rec10451 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(0),[10],[42],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[933]? = some (⟨213,(0),[10],[42],494⟩) from rfl))
private theorem rec10459 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(1),[10],[42],495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[941]? = some (⟨213,(1),[10],[42],495⟩) from rfl))
private theorem rec10467 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(2),[10],[42],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[949]? = some (⟨213,(2),[10],[42],494⟩) from rfl))
private theorem rec10475 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(3),[10],[42],496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[957]? = some (⟨213,(3),[10],[42],496⟩) from rfl))
private theorem rec10483 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(4),[10],[42],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[965]? = some (⟨213,(4),[10],[42],497⟩) from rfl))
private theorem rec10491 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(5),[10],[42],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[973]? = some (⟨213,(5),[10],[42],497⟩) from rfl))
private theorem rec10502 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(6),[10],[42],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[984]? = some (⟨213,(6),[10],[42],497⟩) from rfl))
private theorem rec10510 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(7),[10],[42],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[992]? = some (⟨213,(7),[10],[42],497⟩) from rfl))
private theorem rec10518 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(8),[10],[42],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1000]? = some (⟨213,(8),[10],[42],498⟩) from rfl))
private theorem rec10526 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(9),[10],[42],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1008]? = some (⟨213,(9),[10],[42],498⟩) from rfl))
private theorem rec10534 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(10),[10],[42],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1016]? = some (⟨213,(10),[10],[42],498⟩) from rfl))
private theorem rec10542 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(11),[10],[42],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1024]? = some (⟨213,(11),[10],[42],498⟩) from rfl))
private theorem rec10550 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(12),[10],[42],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1032]? = some (⟨213,(12),[10],[42],499⟩) from rfl))
private theorem rec10558 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(13),[10],[42],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1040]? = some (⟨213,(13),[10],[42],499⟩) from rfl))
private theorem rec10566 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(14),[10],[42],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1048]? = some (⟨213,(14),[10],[42],499⟩) from rfl))
private theorem rec10574 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 213 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(15),[10],[42],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1056]? = some (⟨213,(15),[10],[42],499⟩) from rfl))
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
private theorem rec10646 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 218 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(0),[10],[42],506⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1128]? = some (⟨218,(0),[10],[42],506⟩) from rfl))
private theorem rec10654 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 218 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(1),[10],[42],507⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1136]? = some (⟨218,(1),[10],[42],507⟩) from rfl))
private theorem rec10662 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 218 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(2),[10],[42],508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1144]? = some (⟨218,(2),[10],[42],508⟩) from rfl))
private theorem rec10670 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 218 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(3),[10],[42],509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1152]? = some (⟨218,(3),[10],[42],509⟩) from rfl))
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
private theorem rec10759 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(0),[10],[42],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[30]? = some (⟨221,(0),[10],[42],515⟩) from rfl))
private theorem rec10767 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(1),[10],[42],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[38]? = some (⟨221,(1),[10],[42],515⟩) from rfl))
private theorem rec10775 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(2),[10],[42],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[46]? = some (⟨221,(2),[10],[42],516⟩) from rfl))
private theorem rec10783 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(3),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[54]? = some (⟨221,(3),[10],[42],517⟩) from rfl))
private theorem rec10791 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(4),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[62]? = some (⟨221,(4),[10],[42],518⟩) from rfl))
private theorem rec10799 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(5),[10],[42],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[70]? = some (⟨221,(5),[10],[42],515⟩) from rfl))
private theorem rec10807 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(6),[10],[42],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[78]? = some (⟨221,(6),[10],[42],515⟩) from rfl))
private theorem rec10815 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(7),[10],[42],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[86]? = some (⟨221,(7),[10],[42],516⟩) from rfl))
private theorem rec10823 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(8),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[94]? = some (⟨221,(8),[10],[42],517⟩) from rfl))
private theorem rec10831 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(9),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[102]? = some (⟨221,(9),[10],[42],518⟩) from rfl))
private theorem rec10839 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(10),[10],[42],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[110]? = some (⟨221,(10),[10],[42],519⟩) from rfl))
private theorem rec10847 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(11),[10],[42],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[118]? = some (⟨221,(11),[10],[42],519⟩) from rfl))
private theorem rec10855 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(12),[10],[42],520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[126]? = some (⟨221,(12),[10],[42],520⟩) from rfl))
private theorem rec10863 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(13),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[134]? = some (⟨221,(13),[10],[42],517⟩) from rfl))
private theorem rec10871 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(14),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[142]? = some (⟨221,(14),[10],[42],518⟩) from rfl))
private theorem rec10879 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(15),[10],[42],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[150]? = some (⟨221,(15),[10],[42],521⟩) from rfl))
private theorem rec10887 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(16),[10],[42],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[158]? = some (⟨221,(16),[10],[42],521⟩) from rfl))
private theorem rec10895 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(17),[10],[42],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[166]? = some (⟨221,(17),[10],[42],521⟩) from rfl))
private theorem rec10903 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(18),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[174]? = some (⟨221,(18),[10],[42],517⟩) from rfl))
private theorem rec10912 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(19),[10],[42],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[183]? = some (⟨221,(19),[10],[42],521⟩) from rfl))
private theorem rec10920 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(20),[10],[42],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[191]? = some (⟨221,(20),[10],[42],522⟩) from rfl))
private theorem rec10928 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(21),[10],[42],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[199]? = some (⟨221,(21),[10],[42],522⟩) from rfl))
private theorem rec10936 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(22),[10],[42],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[207]? = some (⟨221,(22),[10],[42],522⟩) from rfl))
private theorem rec10944 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(23),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[215]? = some (⟨221,(23),[10],[42],517⟩) from rfl))
private theorem rec10953 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 221 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(24),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[224]? = some (⟨221,(24),[10],[42],518⟩) from rfl))
private theorem rec10962 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(0),[9,10],[42],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[233]? = some (⟨222,(0),[9,10],[42],736⟩) from rfl))
private theorem rec10969 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(1),[9,10],[42],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[240]? = some (⟨222,(1),[9,10],[42],736⟩) from rfl))
private theorem rec10977 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(2),[10],[42],737⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[248]? = some (⟨222,(2),[10],[42],737⟩) from rfl))
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
private theorem rec11014 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(7),[10],[42],739⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[285]? = some (⟨222,(7),[10],[42],739⟩) from rfl))
private theorem rec11021 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(8),[9,10],[42],740⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[292]? = some (⟨222,(8),[9,10],[42],740⟩) from rfl))
private theorem rec11027 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(9),[9,10],[42],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[298]? = some (⟨222,(9),[9,10],[42],528⟩) from rfl))
private theorem rec11036 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(10),[10],[42],741⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[307]? = some (⟨222,(10),[10],[42],741⟩) from rfl))
private theorem rec11045 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(11),[10],[42],742⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[316]? = some (⟨222,(11),[10],[42],742⟩) from rfl))
private theorem rec11055 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(12),[10],[42],1361⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[326]? = some (⟨222,(12),[10],[42],1361⟩) from rfl))
private theorem rec11064 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(13),[10],[42],744⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[335]? = some (⟨222,(13),[10],[42],744⟩) from rfl))
private theorem rec11070 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(14),[9,10],[42],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[341]? = some (⟨222,(14),[9,10],[42],531⟩) from rfl))
private theorem rec11077 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(15),[9,10],[42],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[348]? = some (⟨222,(15),[9,10],[42],735⟩) from rfl))
private theorem rec11084 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(16),[9,10],[42],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[355]? = some (⟨222,(16),[9,10],[42],738⟩) from rfl))
private theorem rec11092 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 222 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(17),[10],[42],745⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[363]? = some (⟨222,(17),[10],[42],745⟩) from rfl))
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
private theorem rec11174 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(5),[10],[42],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[445]? = some (⟨224,(5),[10],[42],543⟩) from rfl))
private theorem rec11182 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(6),[10],[42],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[453]? = some (⟨224,(6),[10],[42],543⟩) from rfl))
private theorem rec11190 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(7),[10],[42],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[461]? = some (⟨224,(7),[10],[42],544⟩) from rfl))
private theorem rec11198 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(8),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[469]? = some (⟨224,(8),[10],[42],517⟩) from rfl))
private theorem rec11206 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(9),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[477]? = some (⟨224,(9),[10],[42],518⟩) from rfl))
private theorem rec11214 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(10),[10],[42],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[485]? = some (⟨224,(10),[10],[42],545⟩) from rfl))
private theorem rec11222 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(11),[10],[42],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[493]? = some (⟨224,(11),[10],[42],545⟩) from rfl))
private theorem rec11230 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(12),[10],[42],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[501]? = some (⟨224,(12),[10],[42],544⟩) from rfl))
private theorem rec11238 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(13),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[509]? = some (⟨224,(13),[10],[42],517⟩) from rfl))
private theorem rec11246 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(14),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[517]? = some (⟨224,(14),[10],[42],518⟩) from rfl))
private theorem rec11254 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(15),[10],[42],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[525]? = some (⟨224,(15),[10],[42],546⟩) from rfl))
private theorem rec11262 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(16),[10],[42],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[533]? = some (⟨224,(16),[10],[42],546⟩) from rfl))
private theorem rec11270 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(17),[10],[42],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[541]? = some (⟨224,(17),[10],[42],544⟩) from rfl))
private theorem rec11278 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(18),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[549]? = some (⟨224,(18),[10],[42],517⟩) from rfl))
private theorem rec11286 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(19),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[557]? = some (⟨224,(19),[10],[42],518⟩) from rfl))
private theorem rec11294 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(20),[10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[565]? = some (⟨224,(20),[10],[42],547⟩) from rfl))
private theorem rec11302 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(21),[10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[573]? = some (⟨224,(21),[10],[42],547⟩) from rfl))
private theorem rec11310 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(22),[10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[581]? = some (⟨224,(22),[10],[42],547⟩) from rfl))
private theorem rec11318 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(23),[10],[42],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[589]? = some (⟨224,(23),[10],[42],517⟩) from rfl))
private theorem rec11326 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 224 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(24),[10],[42],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[597]? = some (⟨224,(24),[10],[42],518⟩) from rfl))
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
private theorem rec11379 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(7),[10],[42],753⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[650]? = some (⟨225,(7),[10],[42],753⟩) from rfl))
private theorem rec11386 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(8),[9,10],[42],754⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[657]? = some (⟨225,(8),[9,10],[42],754⟩) from rfl))
private theorem rec11394 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(9),[10],[42],753⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[665]? = some (⟨225,(9),[10],[42],753⟩) from rfl))
private theorem rec11400 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(10),[9,10],[42],755⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[671]? = some (⟨225,(10),[9,10],[42],755⟩) from rfl))
private theorem rec11406 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(11),[9,10],[42],756⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[677]? = some (⟨225,(11),[9,10],[42],756⟩) from rfl))
private theorem rec11414 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(12),[10],[42],757⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[685]? = some (⟨225,(12),[10],[42],757⟩) from rfl))
private theorem rec11421 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(13),[9,10],[42],758⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[692]? = some (⟨225,(13),[9,10],[42],758⟩) from rfl))
private theorem rec11429 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(14),[10],[42],757⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[700]? = some (⟨225,(14),[10],[42],757⟩) from rfl))
private theorem rec11435 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(15),[9,10],[42],759⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[706]? = some (⟨225,(15),[9,10],[42],759⟩) from rfl))
private theorem rec11441 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(16),[9,10],[42],760⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[712]? = some (⟨225,(16),[9,10],[42],760⟩) from rfl))
private theorem rec11449 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(17),[10],[42],761⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[720]? = some (⟨225,(17),[10],[42],761⟩) from rfl))
private theorem rec11456 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(18),[9,10],[42],762⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[727]? = some (⟨225,(18),[9,10],[42],762⟩) from rfl))
private theorem rec11464 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(19),[10],[42],761⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[735]? = some (⟨225,(19),[10],[42],761⟩) from rfl))
private theorem rec11470 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(20),[9,10],[42],763⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[741]? = some (⟨225,(20),[9,10],[42],763⟩) from rfl))
private theorem rec11476 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(21),[9,10],[42],764⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[747]? = some (⟨225,(21),[9,10],[42],764⟩) from rfl))
private theorem rec11484 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(22),[10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[755]? = some (⟨225,(22),[10],[42],547⟩) from rfl))
private theorem rec11491 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(23),[9,10],[42],765⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[762]? = some (⟨225,(23),[9,10],[42],765⟩) from rfl))
private theorem rec11499 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 225 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(24),[10],[42],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[770]? = some (⟨225,(24),[10],[42],547⟩) from rfl))
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
private theorem rec11580 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(2),[10],[42],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[851]? = some (⟨227,(2),[10],[42],775⟩) from rfl))
private theorem rec11586 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(3),[9,10],[42],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[857]? = some (⟨227,(3),[9,10],[42],776⟩) from rfl))
private theorem rec11594 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(4),[10],[42],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[865]? = some (⟨227,(4),[10],[42],775⟩) from rfl))
private theorem rec11600 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(5),[9,10],[42],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[871]? = some (⟨227,(5),[9,10],[42],773⟩) from rfl))
private theorem rec11606 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(6),[9,10],[42],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[877]? = some (⟨227,(6),[9,10],[42],774⟩) from rfl))
private theorem rec11614 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(7),[10],[42],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[885]? = some (⟨227,(7),[10],[42],775⟩) from rfl))
private theorem rec11620 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(8),[9,10],[42],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[891]? = some (⟨227,(8),[9,10],[42],776⟩) from rfl))
private theorem rec11628 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(9),[10],[42],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[899]? = some (⟨227,(9),[10],[42],775⟩) from rfl))
private theorem rec11634 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(10),[9,10],[42],777⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[905]? = some (⟨227,(10),[9,10],[42],777⟩) from rfl))
private theorem rec11640 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(11),[9,10],[42],778⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[911]? = some (⟨227,(11),[9,10],[42],778⟩) from rfl))
private theorem rec11648 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(12),[10],[42],779⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[919]? = some (⟨227,(12),[10],[42],779⟩) from rfl))
private theorem rec11654 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(13),[9,10],[42],780⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[925]? = some (⟨227,(13),[9,10],[42],780⟩) from rfl))
private theorem rec11662 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(14),[10],[42],779⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[933]? = some (⟨227,(14),[10],[42],779⟩) from rfl))
private theorem rec11668 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(15),[9,10],[42],781⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[939]? = some (⟨227,(15),[9,10],[42],781⟩) from rfl))
private theorem rec11674 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(16),[9,10],[42],782⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[945]? = some (⟨227,(16),[9,10],[42],782⟩) from rfl))
private theorem rec11682 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(17),[10],[42],783⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[953]? = some (⟨227,(17),[10],[42],783⟩) from rfl))
private theorem rec11688 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(18),[9,10],[42],784⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[959]? = some (⟨227,(18),[9,10],[42],784⟩) from rfl))
private theorem rec11696 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(19),[10],[42],783⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[967]? = some (⟨227,(19),[10],[42],783⟩) from rfl))
private theorem rec11702 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(20),[9,10],[42],785⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[973]? = some (⟨227,(20),[9,10],[42],785⟩) from rfl))
private theorem rec11708 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(21),[9,10],[42],786⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[979]? = some (⟨227,(21),[9,10],[42],786⟩) from rfl))
private theorem rec11716 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(22),[10],[42],787⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[987]? = some (⟨227,(22),[10],[42],787⟩) from rfl))
private theorem rec11722 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(23),[9,10],[42],788⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[993]? = some (⟨227,(23),[9,10],[42],788⟩) from rfl))
private theorem rec11730 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 227 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(24),[10],[42],787⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1001]? = some (⟨227,(24),[10],[42],787⟩) from rfl))
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
private theorem rec11956 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(9),[10],[42],817⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[27]? = some (⟨230,(9),[10],[42],817⟩) from rfl))
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
private theorem rec11991 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(14),[10],[42],817⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[62]? = some (⟨230,(14),[10],[42],817⟩) from rfl))
private theorem rec11997 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(15),[9,10],[42],822⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[68]? = some (⟨230,(15),[9,10],[42],822⟩) from rfl))
private theorem rec12003 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(16),[9,10],[42],823⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[74]? = some (⟨230,(16),[9,10],[42],823⟩) from rfl))
private theorem rec12011 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(17),[10],[42],824⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[82]? = some (⟨230,(17),[10],[42],824⟩) from rfl))
private theorem rec12017 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(18),[9,10],[42],825⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[88]? = some (⟨230,(18),[9,10],[42],825⟩) from rfl))
private theorem rec12025 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(19),[10],[42],824⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[96]? = some (⟨230,(19),[10],[42],824⟩) from rfl))
private theorem rec12031 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(20),[9,10],[42],826⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[102]? = some (⟨230,(20),[9,10],[42],826⟩) from rfl))
private theorem rec12037 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(21),[9,10],[42],827⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[108]? = some (⟨230,(21),[9,10],[42],827⟩) from rfl))
private theorem rec12045 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(22),[10],[42],828⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[116]? = some (⟨230,(22),[10],[42],828⟩) from rfl))
private theorem rec12051 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(23),[9,10],[42],829⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[122]? = some (⟨230,(23),[9,10],[42],829⟩) from rfl))
private theorem rec12059 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 230 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(24),[10],[42],828⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[130]? = some (⟨230,(24),[10],[42],828⟩) from rfl))
private theorem rec12066 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(0),[9,10],[42],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[137]? = some (⟨231,(0),[9,10],[42],830⟩) from rfl))
private theorem rec12074 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(1),[10],[42],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[145]? = some (⟨231,(1),[10],[42],831⟩) from rfl))
private theorem rec12080 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(2),[9,10],[42],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[151]? = some (⟨231,(2),[9,10],[42],832⟩) from rfl))
private theorem rec12086 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(3),[9,10],[42],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[157]? = some (⟨231,(3),[9,10],[42],833⟩) from rfl))
private theorem rec12093 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(4),[9,10],[42],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[164]? = some (⟨231,(4),[9,10],[42],830⟩) from rfl))
private theorem rec12101 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 231 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(5),[10],[42],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[172]? = some (⟨231,(5),[10],[42],831⟩) from rfl))
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
private theorem rec12251 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(9),[10],[42],853⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[322]? = some (⟨232,(9),[10],[42],853⟩) from rfl))
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
private theorem rec12284 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(14),[10],[42],855⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[355]? = some (⟨232,(14),[10],[42],855⟩) from rfl))
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
private theorem rec12317 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 232 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(19),[10],[42],860⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[388]? = some (⟨232,(19),[10],[42],860⟩) from rfl))
private theorem rec12323 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(0),[9,10],[42],568⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[394]? = some (⟨234,(0),[9,10],[42],568⟩) from rfl))
private theorem rec12331 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(1),[10],[42],569⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[402]? = some (⟨234,(1),[10],[42],569⟩) from rfl))
private theorem rec12339 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(2),[10],[42],570⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[410]? = some (⟨234,(2),[10],[42],570⟩) from rfl))
private theorem rec12347 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(3),[10],[42],571⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[418]? = some (⟨234,(3),[10],[42],571⟩) from rfl))
private theorem rec12353 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(4),[9,10],[42],572⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[424]? = some (⟨234,(4),[9,10],[42],572⟩) from rfl))
private theorem rec12361 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(5),[10],[42],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[432]? = some (⟨234,(5),[10],[42],573⟩) from rfl))
private theorem rec12369 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(6),[10],[42],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[440]? = some (⟨234,(6),[10],[42],573⟩) from rfl))
private theorem rec12377 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(7),[10],[42],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[448]? = some (⟨234,(7),[10],[42],573⟩) from rfl))
private theorem rec12383 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(8),[9,10],[42],574⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[454]? = some (⟨234,(8),[9,10],[42],574⟩) from rfl))
private theorem rec12391 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(9),[10],[42],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[462]? = some (⟨234,(9),[10],[42],575⟩) from rfl))
private theorem rec12399 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(10),[10],[42],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[470]? = some (⟨234,(10),[10],[42],575⟩) from rfl))
private theorem rec12407 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(11),[10],[42],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[478]? = some (⟨234,(11),[10],[42],575⟩) from rfl))
private theorem rec12413 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(12),[9,10],[42],576⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[484]? = some (⟨234,(12),[9,10],[42],576⟩) from rfl))
private theorem rec12421 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(13),[10],[42],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[492]? = some (⟨234,(13),[10],[42],577⟩) from rfl))
private theorem rec12429 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(14),[10],[42],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[500]? = some (⟨234,(14),[10],[42],577⟩) from rfl))
private theorem rec12437 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 234 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(15),[10],[42],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[508]? = some (⟨234,(15),[10],[42],577⟩) from rfl))
private theorem rec12443 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(0),[9,10],[42],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[514]? = some (⟨235,(0),[9,10],[42],578⟩) from rfl))
private theorem rec12449 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(1),[9,10],[42],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[1]? = some (⟨235,(1),[9,10],[42],579⟩) from rfl))
private theorem rec12457 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(2),[10],[42],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[9]? = some (⟨235,(2),[10],[42],580⟩) from rfl))
private theorem rec12463 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(3),[9,10],[42],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[15]? = some (⟨235,(3),[9,10],[42],581⟩) from rfl))
private theorem rec12469 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(4),[9,10],[42],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[21]? = some (⟨235,(4),[9,10],[42],582⟩) from rfl))
private theorem rec12475 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(5),[9,10],[42],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[27]? = some (⟨235,(5),[9,10],[42],583⟩) from rfl))
private theorem rec12483 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(6),[10],[42],584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[35]? = some (⟨235,(6),[10],[42],584⟩) from rfl))
private theorem rec12489 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(7),[9,10],[42],585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[41]? = some (⟨235,(7),[9,10],[42],585⟩) from rfl))
private theorem rec12495 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(8),[9,10],[42],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[47]? = some (⟨235,(8),[9,10],[42],578⟩) from rfl))
private theorem rec12501 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(9),[9,10],[42],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[53]? = some (⟨235,(9),[9,10],[42],579⟩) from rfl))
private theorem rec12509 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(10),[10],[42],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[61]? = some (⟨235,(10),[10],[42],580⟩) from rfl))
private theorem rec12515 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(11),[9,10],[42],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[67]? = some (⟨235,(11),[9,10],[42],581⟩) from rfl))
private theorem rec12521 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(12),[9,10],[42],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[73]? = some (⟨235,(12),[9,10],[42],586⟩) from rfl))
private theorem rec12527 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(13),[9,10],[42],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[79]? = some (⟨235,(13),[9,10],[42],587⟩) from rfl))
private theorem rec12535 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(14),[10],[42],588⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[87]? = some (⟨235,(14),[10],[42],588⟩) from rfl))
private theorem rec12541 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 235 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(15),[9,10],[42],589⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[93]? = some (⟨235,(15),[9,10],[42],589⟩) from rfl))
private theorem rec12548 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 236 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(0),[9,10],[42],861⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[100]? = some (⟨236,(0),[9,10],[42],861⟩) from rfl))
private theorem rec12555 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 236 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(1),[9,10],[42],862⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[107]? = some (⟨236,(1),[9,10],[42],862⟩) from rfl))
private theorem rec12564 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 236 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(2),[10],[42],863⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[116]? = some (⟨236,(2),[10],[42],863⟩) from rfl))
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
private theorem rec12599 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(3),[10],[42],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[151]? = some (⟨237,(3),[10],[42],596⟩) from rfl))
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
private theorem rec12633 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 237 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(8),[10],[42],867⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[185]? = some (⟨237,(8),[10],[42],867⟩) from rfl))
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
private theorem rec12696 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(2),[10],[42],607⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[248]? = some (⟨238,(2),[10],[42],607⟩) from rfl))
private theorem rec12703 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(3),[9,10],[42],871⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[255]? = some (⟨238,(3),[9,10],[42],871⟩) from rfl))
private theorem rec12709 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(4),[9,10],[42],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[261]? = some (⟨238,(4),[9,10],[42],609⟩) from rfl))
private theorem rec12715 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(5),[9,10],[42],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[267]? = some (⟨238,(5),[9,10],[42],610⟩) from rfl))
private theorem rec12723 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(6),[10],[42],611⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[275]? = some (⟨238,(6),[10],[42],611⟩) from rfl))
private theorem rec12729 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(7),[9,10],[42],612⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[281]? = some (⟨238,(7),[9,10],[42],612⟩) from rfl))
private theorem rec12735 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(8),[9,10],[42],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[287]? = some (⟨238,(8),[9,10],[42],613⟩) from rfl))
private theorem rec12741 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(9),[9,10],[42],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[293]? = some (⟨238,(9),[9,10],[42],614⟩) from rfl))
private theorem rec12749 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(10),[10],[42],615⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[301]? = some (⟨238,(10),[10],[42],615⟩) from rfl))
private theorem rec12755 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(11),[9,10],[42],616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[307]? = some (⟨238,(11),[9,10],[42],616⟩) from rfl))
private theorem rec12761 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(12),[9,10],[42],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[313]? = some (⟨238,(12),[9,10],[42],617⟩) from rfl))
private theorem rec12767 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(13),[9,10],[42],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[319]? = some (⟨238,(13),[9,10],[42],618⟩) from rfl))
private theorem rec12775 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 238 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(14),[10],[42],619⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[327]? = some (⟨238,(14),[10],[42],619⟩) from rfl))
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
private theorem rec16438 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(1),[10],[42],1666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[230]? = some (⟨567,(1),[10],[42],1666⟩) from rfl))
private theorem rec16442 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(2),[10],[42],1667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[234]? = some (⟨567,(2),[10],[42],1667⟩) from rfl))
private theorem rec16446 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(3),[10],[42],1668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[238]? = some (⟨567,(3),[10],[42],1668⟩) from rfl))
private theorem rec16450 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(4),[10],[42],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[242]? = some (⟨567,(4),[10],[42],396⟩) from rfl))
private theorem rec16453 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(5),[9,10],[42],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[245]? = some (⟨567,(5),[9,10],[42],1649⟩) from rfl))
private theorem rec16457 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(6),[10],[42],1666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[249]? = some (⟨567,(6),[10],[42],1666⟩) from rfl))
private theorem rec16461 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(7),[10],[42],1667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[253]? = some (⟨567,(7),[10],[42],1667⟩) from rfl))
private theorem rec16465 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(8),[10],[42],1668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[257]? = some (⟨567,(8),[10],[42],1668⟩) from rfl))
private theorem rec16469 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 567 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨567,(9),[10],[42],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[261]? = some (⟨567,(9),[10],[42],396⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 32).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 10).plans.drop 5).take 1 = [⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(566,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(567,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(568,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(569,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(570,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec7425 10 32 (by decide) (by decide)
  · left
    exact rec7425 10 33 (by decide) (by decide)
  · left
    exact rec7429 10 34 (by decide) (by decide)
  · left
    exact rec7430 10 35 (by decide) (by decide)
  · left
    exact rec7425 10 36 (by decide) (by decide)
  · left
    exact rec7425 10 37 (by decide) (by decide)
  · left
    exact rec7431 10 38 (by decide) (by decide)
  · left
    exact rec7430 10 39 (by decide) (by decide)
  · left
    exact rec7425 10 40 (by decide) (by decide)
  · left
    exact rec7425 10 41 (by decide) (by decide)
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
        exact rec7442 10 42 (by decide) (by decide)
      · right
        exact rec7445 10 42 (by decide) (by decide)
      · right
        exact rec7448 10 42 (by decide) (by decide)
      · right
        exact rec7451 10 42 (by decide) (by decide)
      · right
        exact rec7454 10 42 (by decide) (by decide)
      · right
        exact rec7457 10 42 (by decide) (by decide)
      · right
        exact rec7460 10 42 (by decide) (by decide)
      · right
        exact rec7463 10 42 (by decide) (by decide)
      · right
        exact rec7466 10 42 (by decide) (by decide)
      · right
        exact rec7469 10 42 (by decide) (by decide)
      · right
        exact rec7472 10 42 (by decide) (by decide)
      · right
        exact rec7475 10 42 (by decide) (by decide)
      · right
        exact rec7478 10 42 (by decide) (by decide)
      · right
        exact rec7481 10 42 (by decide) (by decide)
      · right
        exact rec7484 10 42 (by decide) (by decide)
      · right
        exact rec7487 10 42 (by decide) (by decide)
      · right
        exact rec7490 10 42 (by decide) (by decide)
      · right
        exact rec7493 10 42 (by decide) (by decide)
      · right
        exact rec7496 10 42 (by decide) (by decide)
      · right
        exact rec7499 10 42 (by decide) (by decide)
      · right
        exact rec7502 10 42 (by decide) (by decide)
      · right
        exact rec7505 10 42 (by decide) (by decide)
      · right
        exact rec7508 10 42 (by decide) (by decide)
      · right
        exact rec7511 10 42 (by decide) (by decide)
      · right
        exact rec7514 10 42 (by decide) (by decide)
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
        exact rec16434 10 42 (by decide) (by decide)
      · right
        exact rec16438 10 42 (by decide) (by decide)
      · right
        exact rec16442 10 42 (by decide) (by decide)
      · right
        exact rec16446 10 42 (by decide) (by decide)
      · right
        exact rec16450 10 42 (by decide) (by decide)
      · right
        exact rec16453 10 42 (by decide) (by decide)
      · right
        exact rec16457 10 42 (by decide) (by decide)
      · right
        exact rec16461 10 42 (by decide) (by decide)
      · right
        exact rec16465 10 42 (by decide) (by decide)
      · right
        exact rec16469 10 42 (by decide) (by decide)
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
        exact rec7640 10 42 (by decide) (by decide)
      · right
        exact rec7647 10 42 (by decide) (by decide)
      · right
        exact rec7654 10 42 (by decide) (by decide)
      · right
        exact rec7661 10 42 (by decide) (by decide)
      · right
        exact rec7668 10 42 (by decide) (by decide)
      · right
        exact rec7675 10 42 (by decide) (by decide)
      · right
        exact rec7682 10 42 (by decide) (by decide)
      · right
        exact rec7689 10 42 (by decide) (by decide)
      · right
        exact rec7696 10 42 (by decide) (by decide)
      · right
        exact rec7703 10 42 (by decide) (by decide)
      · right
        exact rec7710 10 42 (by decide) (by decide)
      · right
        exact rec7717 10 42 (by decide) (by decide)
      · right
        exact rec7724 10 42 (by decide) (by decide)
      · right
        exact rec7731 10 42 (by decide) (by decide)
      · right
        exact rec7738 10 42 (by decide) (by decide)
      · right
        exact rec7745 10 42 (by decide) (by decide)
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
        exact rec7753 10 42 (by decide) (by decide)
      · right
        exact rec7761 10 42 (by decide) (by decide)
      · right
        exact rec7769 10 42 (by decide) (by decide)
      · right
        exact rec7777 10 42 (by decide) (by decide)
      · right
        exact rec7785 10 42 (by decide) (by decide)
      · right
        exact rec7793 10 42 (by decide) (by decide)
      · right
        exact rec7801 10 42 (by decide) (by decide)
      · right
        exact rec7809 10 42 (by decide) (by decide)
      · right
        exact rec7817 10 42 (by decide) (by decide)
      · right
        exact rec7825 10 42 (by decide) (by decide)
      · right
        exact rec7833 10 42 (by decide) (by decide)
      · right
        exact rec7841 10 42 (by decide) (by decide)
      · right
        exact rec7849 10 42 (by decide) (by decide)
      · right
        exact rec7857 10 42 (by decide) (by decide)
      · right
        exact rec7865 10 42 (by decide) (by decide)
      · right
        exact rec7873 10 42 (by decide) (by decide)
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
        exact rec7880 10 42 (by decide) (by decide)
      · right
        exact rec7887 10 42 (by decide) (by decide)
      · right
        exact rec7894 10 42 (by decide) (by decide)
      · right
        exact rec7901 10 42 (by decide) (by decide)
      · right
        exact rec7908 10 42 (by decide) (by decide)
      · right
        exact rec7915 10 42 (by decide) (by decide)
      · right
        exact rec7922 10 42 (by decide) (by decide)
      · right
        exact rec7929 10 42 (by decide) (by decide)
      · right
        exact rec7936 10 42 (by decide) (by decide)
      · right
        exact rec7943 10 42 (by decide) (by decide)
      · right
        exact rec7950 10 42 (by decide) (by decide)
      · right
        exact rec7957 10 42 (by decide) (by decide)
      · right
        exact rec7964 10 42 (by decide) (by decide)
      · right
        exact rec7971 10 42 (by decide) (by decide)
      · right
        exact rec7978 10 42 (by decide) (by decide)
      · right
        exact rec7985 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 167)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7993 10 42 (by decide) (by decide)
      · right
        exact rec8001 10 42 (by decide) (by decide)
      · right
        exact rec8009 10 42 (by decide) (by decide)
      · right
        exact rec8017 10 42 (by decide) (by decide)
      · right
        exact rec8025 10 42 (by decide) (by decide)
      · right
        exact rec8033 10 42 (by decide) (by decide)
      · right
        exact rec8041 10 42 (by decide) (by decide)
      · right
        exact rec8049 10 42 (by decide) (by decide)
      · right
        exact rec8057 10 42 (by decide) (by decide)
      · right
        exact rec8065 10 42 (by decide) (by decide)
      · right
        exact rec8073 10 42 (by decide) (by decide)
      · right
        exact rec8081 10 42 (by decide) (by decide)
      · right
        exact rec8089 10 42 (by decide) (by decide)
      · right
        exact rec8097 10 42 (by decide) (by decide)
      · right
        exact rec8105 10 42 (by decide) (by decide)
      · right
        exact rec8113 10 42 (by decide) (by decide)
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
        exact rec8120 10 42 (by decide) (by decide)
      · right
        exact rec8127 10 42 (by decide) (by decide)
      · right
        exact rec8134 10 42 (by decide) (by decide)
      · right
        exact rec8141 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 172)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8149 10 42 (by decide) (by decide)
      · right
        exact rec8157 10 42 (by decide) (by decide)
      · right
        exact rec8165 10 42 (by decide) (by decide)
      · right
        exact rec8173 10 42 (by decide) (by decide)
      · right
        exact rec8181 10 42 (by decide) (by decide)
      · right
        exact rec8189 10 42 (by decide) (by decide)
      · right
        exact rec8197 10 42 (by decide) (by decide)
      · right
        exact rec8205 10 42 (by decide) (by decide)
      · right
        exact rec8213 10 42 (by decide) (by decide)
      · right
        exact rec8221 10 42 (by decide) (by decide)
      · right
        exact rec8229 10 42 (by decide) (by decide)
      · right
        exact rec8237 10 42 (by decide) (by decide)
      · right
        exact rec8245 10 42 (by decide) (by decide)
      · right
        exact rec8253 10 42 (by decide) (by decide)
      · right
        exact rec8261 10 42 (by decide) (by decide)
      · right
        exact rec8269 10 42 (by decide) (by decide)
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
        exact rec8276 10 42 (by decide) (by decide)
      · right
        exact rec8283 10 42 (by decide) (by decide)
      · right
        exact rec8290 10 42 (by decide) (by decide)
      · right
        exact rec8297 10 42 (by decide) (by decide)
      · right
        exact rec8304 10 42 (by decide) (by decide)
      · right
        exact rec8311 10 42 (by decide) (by decide)
      · right
        exact rec8318 10 42 (by decide) (by decide)
      · right
        exact rec8325 10 42 (by decide) (by decide)
      · right
        exact rec8332 10 42 (by decide) (by decide)
      · right
        exact rec8339 10 42 (by decide) (by decide)
      · right
        exact rec8346 10 42 (by decide) (by decide)
      · right
        exact rec8353 10 42 (by decide) (by decide)
      · right
        exact rec8360 10 42 (by decide) (by decide)
      · right
        exact rec8367 10 42 (by decide) (by decide)
      · right
        exact rec8374 10 42 (by decide) (by decide)
      · right
        exact rec8381 10 42 (by decide) (by decide)
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
        exact rec8389 10 42 (by decide) (by decide)
      · right
        exact rec8397 10 42 (by decide) (by decide)
      · right
        exact rec8405 10 42 (by decide) (by decide)
      · right
        exact rec8413 10 42 (by decide) (by decide)
      · right
        exact rec8421 10 42 (by decide) (by decide)
      · right
        exact rec8429 10 42 (by decide) (by decide)
      · right
        exact rec8437 10 42 (by decide) (by decide)
      · right
        exact rec8445 10 42 (by decide) (by decide)
      · right
        exact rec8453 10 42 (by decide) (by decide)
      · right
        exact rec8461 10 42 (by decide) (by decide)
      · right
        exact rec8469 10 42 (by decide) (by decide)
      · right
        exact rec8477 10 42 (by decide) (by decide)
      · right
        exact rec8485 10 42 (by decide) (by decide)
      · right
        exact rec8493 10 42 (by decide) (by decide)
      · right
        exact rec8501 10 42 (by decide) (by decide)
      · right
        exact rec8509 10 42 (by decide) (by decide)
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
        exact rec8516 10 42 (by decide) (by decide)
      · right
        exact rec8523 10 42 (by decide) (by decide)
      · right
        exact rec8530 10 42 (by decide) (by decide)
      · right
        exact rec8537 10 42 (by decide) (by decide)
      · right
        exact rec8544 10 42 (by decide) (by decide)
      · right
        exact rec8551 10 42 (by decide) (by decide)
      · right
        exact rec8558 10 42 (by decide) (by decide)
      · right
        exact rec8565 10 42 (by decide) (by decide)
      · right
        exact rec8572 10 42 (by decide) (by decide)
      · right
        exact rec8579 10 42 (by decide) (by decide)
      · right
        exact rec8586 10 42 (by decide) (by decide)
      · right
        exact rec8593 10 42 (by decide) (by decide)
      · right
        exact rec8600 10 42 (by decide) (by decide)
      · right
        exact rec8607 10 42 (by decide) (by decide)
      · right
        exact rec8614 10 42 (by decide) (by decide)
      · right
        exact rec8621 10 42 (by decide) (by decide)
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
        exact rec8629 10 42 (by decide) (by decide)
      · right
        exact rec8637 10 42 (by decide) (by decide)
      · right
        exact rec8645 10 42 (by decide) (by decide)
      · right
        exact rec8653 10 42 (by decide) (by decide)
      · right
        exact rec8661 10 42 (by decide) (by decide)
      · right
        exact rec8669 10 42 (by decide) (by decide)
      · right
        exact rec8677 10 42 (by decide) (by decide)
      · right
        exact rec8685 10 42 (by decide) (by decide)
      · right
        exact rec8693 10 42 (by decide) (by decide)
      · right
        exact rec8701 10 42 (by decide) (by decide)
      · right
        exact rec8709 10 42 (by decide) (by decide)
      · right
        exact rec8717 10 42 (by decide) (by decide)
      · right
        exact rec8725 10 42 (by decide) (by decide)
      · right
        exact rec8733 10 42 (by decide) (by decide)
      · right
        exact rec8741 10 42 (by decide) (by decide)
      · right
        exact rec8749 10 42 (by decide) (by decide)
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
        exact rec8756 10 42 (by decide) (by decide)
      · right
        exact rec8763 10 42 (by decide) (by decide)
      · right
        exact rec8770 10 42 (by decide) (by decide)
      · right
        exact rec8777 10 42 (by decide) (by decide)
      · right
        exact rec8784 10 42 (by decide) (by decide)
      · right
        exact rec8791 10 42 (by decide) (by decide)
      · right
        exact rec8798 10 42 (by decide) (by decide)
      · right
        exact rec8805 10 42 (by decide) (by decide)
      · right
        exact rec8812 10 42 (by decide) (by decide)
      · right
        exact rec8819 10 42 (by decide) (by decide)
      · right
        exact rec8826 10 42 (by decide) (by decide)
      · right
        exact rec8833 10 42 (by decide) (by decide)
      · right
        exact rec8840 10 42 (by decide) (by decide)
      · right
        exact rec8847 10 42 (by decide) (by decide)
      · right
        exact rec8854 10 42 (by decide) (by decide)
      · right
        exact rec8861 10 42 (by decide) (by decide)
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
        exact rec8869 10 42 (by decide) (by decide)
      · right
        exact rec8877 10 42 (by decide) (by decide)
      · right
        exact rec8885 10 42 (by decide) (by decide)
      · right
        exact rec8893 10 42 (by decide) (by decide)
      · right
        exact rec8901 10 42 (by decide) (by decide)
      · right
        exact rec8909 10 42 (by decide) (by decide)
      · right
        exact rec8917 10 42 (by decide) (by decide)
      · right
        exact rec8925 10 42 (by decide) (by decide)
      · right
        exact rec8933 10 42 (by decide) (by decide)
      · right
        exact rec8941 10 42 (by decide) (by decide)
      · right
        exact rec8949 10 42 (by decide) (by decide)
      · right
        exact rec8957 10 42 (by decide) (by decide)
      · right
        exact rec8965 10 42 (by decide) (by decide)
      · right
        exact rec8973 10 42 (by decide) (by decide)
      · right
        exact rec8981 10 42 (by decide) (by decide)
      · right
        exact rec8989 10 42 (by decide) (by decide)
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
        exact rec8996 10 42 (by decide) (by decide)
      · right
        exact rec9003 10 42 (by decide) (by decide)
      · right
        exact rec9010 10 42 (by decide) (by decide)
      · right
        exact rec9017 10 42 (by decide) (by decide)
      · right
        exact rec9024 10 42 (by decide) (by decide)
      · right
        exact rec9031 10 42 (by decide) (by decide)
      · right
        exact rec9038 10 42 (by decide) (by decide)
      · right
        exact rec9045 10 42 (by decide) (by decide)
      · right
        exact rec9052 10 42 (by decide) (by decide)
      · right
        exact rec9059 10 42 (by decide) (by decide)
      · right
        exact rec9066 10 42 (by decide) (by decide)
      · right
        exact rec9073 10 42 (by decide) (by decide)
      · right
        exact rec9080 10 42 (by decide) (by decide)
      · right
        exact rec9087 10 42 (by decide) (by decide)
      · right
        exact rec9094 10 42 (by decide) (by decide)
      · right
        exact rec9101 10 42 (by decide) (by decide)
      · right
        exact rec9108 10 42 (by decide) (by decide)
      · right
        exact rec9115 10 42 (by decide) (by decide)
      · right
        exact rec9122 10 42 (by decide) (by decide)
      · right
        exact rec9129 10 42 (by decide) (by decide)
      · right
        exact rec9136 10 42 (by decide) (by decide)
      · right
        exact rec9143 10 42 (by decide) (by decide)
      · right
        exact rec9150 10 42 (by decide) (by decide)
      · right
        exact rec9157 10 42 (by decide) (by decide)
      · right
        exact rec9164 10 42 (by decide) (by decide)
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
        exact rec9172 10 42 (by decide) (by decide)
      · right
        exact rec9180 10 42 (by decide) (by decide)
      · right
        exact rec9188 10 42 (by decide) (by decide)
      · right
        exact rec9196 10 42 (by decide) (by decide)
      · right
        exact rec9204 10 42 (by decide) (by decide)
      · right
        exact rec9212 10 42 (by decide) (by decide)
      · right
        exact rec9220 10 42 (by decide) (by decide)
      · right
        exact rec9228 10 42 (by decide) (by decide)
      · right
        exact rec9236 10 42 (by decide) (by decide)
      · right
        exact rec9244 10 42 (by decide) (by decide)
      · right
        exact rec9252 10 42 (by decide) (by decide)
      · right
        exact rec9260 10 42 (by decide) (by decide)
      · right
        exact rec9268 10 42 (by decide) (by decide)
      · right
        exact rec9276 10 42 (by decide) (by decide)
      · right
        exact rec9284 10 42 (by decide) (by decide)
      · right
        exact rec9292 10 42 (by decide) (by decide)
      · right
        exact rec9300 10 42 (by decide) (by decide)
      · right
        exact rec9308 10 42 (by decide) (by decide)
      · right
        exact rec9316 10 42 (by decide) (by decide)
      · right
        exact rec9324 10 42 (by decide) (by decide)
      · right
        exact rec9332 10 42 (by decide) (by decide)
      · right
        exact rec9340 10 42 (by decide) (by decide)
      · right
        exact rec9348 10 42 (by decide) (by decide)
      · right
        exact rec9356 10 42 (by decide) (by decide)
      · right
        exact rec9364 10 42 (by decide) (by decide)
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
        exact rec9371 10 42 (by decide) (by decide)
      · right
        exact rec9378 10 42 (by decide) (by decide)
      · right
        exact rec9385 10 42 (by decide) (by decide)
      · right
        exact rec9392 10 42 (by decide) (by decide)
      · right
        exact rec9399 10 42 (by decide) (by decide)
      · right
        exact rec9406 10 42 (by decide) (by decide)
      · right
        exact rec9413 10 42 (by decide) (by decide)
      · right
        exact rec9420 10 42 (by decide) (by decide)
      · right
        exact rec9427 10 42 (by decide) (by decide)
      · right
        exact rec9434 10 42 (by decide) (by decide)
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
        exact rec9442 10 42 (by decide) (by decide)
      · right
        exact rec9450 10 42 (by decide) (by decide)
      · right
        exact rec9458 10 42 (by decide) (by decide)
      · right
        exact rec9466 10 42 (by decide) (by decide)
      · right
        exact rec9474 10 42 (by decide) (by decide)
      · right
        exact rec9482 10 42 (by decide) (by decide)
      · right
        exact rec9490 10 42 (by decide) (by decide)
      · right
        exact rec9498 10 42 (by decide) (by decide)
      · right
        exact rec9506 10 42 (by decide) (by decide)
      · right
        exact rec9514 10 42 (by decide) (by decide)
      · right
        exact rec9522 10 42 (by decide) (by decide)
      · right
        exact rec9530 10 42 (by decide) (by decide)
      · right
        exact rec9538 10 42 (by decide) (by decide)
      · right
        exact rec9546 10 42 (by decide) (by decide)
      · right
        exact rec9554 10 42 (by decide) (by decide)
      · right
        exact rec9562 10 42 (by decide) (by decide)
      · right
        exact rec9570 10 42 (by decide) (by decide)
      · right
        exact rec9578 10 42 (by decide) (by decide)
      · right
        exact rec9586 10 42 (by decide) (by decide)
      · right
        exact rec9594 10 42 (by decide) (by decide)
      · right
        exact rec9602 10 42 (by decide) (by decide)
      · right
        exact rec9610 10 42 (by decide) (by decide)
      · right
        exact rec9618 10 42 (by decide) (by decide)
      · right
        exact rec9626 10 42 (by decide) (by decide)
      · right
        exact rec9634 10 42 (by decide) (by decide)
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
        exact rec9641 10 42 (by decide) (by decide)
      · right
        exact rec9648 10 42 (by decide) (by decide)
      · right
        exact rec9655 10 42 (by decide) (by decide)
      · right
        exact rec9662 10 42 (by decide) (by decide)
      · right
        exact rec9669 10 42 (by decide) (by decide)
      · right
        exact rec9676 10 42 (by decide) (by decide)
      · right
        exact rec9683 10 42 (by decide) (by decide)
      · right
        exact rec9690 10 42 (by decide) (by decide)
      · right
        exact rec9697 10 42 (by decide) (by decide)
      · right
        exact rec9704 10 42 (by decide) (by decide)
      · right
        exact rec9711 10 42 (by decide) (by decide)
      · right
        exact rec9718 10 42 (by decide) (by decide)
      · right
        exact rec9725 10 42 (by decide) (by decide)
      · right
        exact rec9732 10 42 (by decide) (by decide)
      · right
        exact rec9739 10 42 (by decide) (by decide)
      · right
        exact rec9746 10 42 (by decide) (by decide)
      · right
        exact rec9753 10 42 (by decide) (by decide)
      · right
        exact rec9760 10 42 (by decide) (by decide)
      · right
        exact rec9767 10 42 (by decide) (by decide)
      · right
        exact rec9774 10 42 (by decide) (by decide)
      · right
        exact rec9781 10 42 (by decide) (by decide)
      · right
        exact rec9788 10 42 (by decide) (by decide)
      · right
        exact rec9795 10 42 (by decide) (by decide)
      · right
        exact rec9802 10 42 (by decide) (by decide)
      · right
        exact rec9809 10 42 (by decide) (by decide)
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
        exact rec9817 10 42 (by decide) (by decide)
      · right
        exact rec9825 10 42 (by decide) (by decide)
      · right
        exact rec9833 10 42 (by decide) (by decide)
      · right
        exact rec9841 10 42 (by decide) (by decide)
      · right
        exact rec9849 10 42 (by decide) (by decide)
      · right
        exact rec9857 10 42 (by decide) (by decide)
      · right
        exact rec9865 10 42 (by decide) (by decide)
      · right
        exact rec9873 10 42 (by decide) (by decide)
      · right
        exact rec9881 10 42 (by decide) (by decide)
      · right
        exact rec9889 10 42 (by decide) (by decide)
      · right
        exact rec9897 10 42 (by decide) (by decide)
      · right
        exact rec9905 10 42 (by decide) (by decide)
      · right
        exact rec9913 10 42 (by decide) (by decide)
      · right
        exact rec9921 10 42 (by decide) (by decide)
      · right
        exact rec9929 10 42 (by decide) (by decide)
      · right
        exact rec9937 10 42 (by decide) (by decide)
      · right
        exact rec9945 10 42 (by decide) (by decide)
      · right
        exact rec9953 10 42 (by decide) (by decide)
      · right
        exact rec9961 10 42 (by decide) (by decide)
      · right
        exact rec9969 10 42 (by decide) (by decide)
      · right
        exact rec9977 10 42 (by decide) (by decide)
      · right
        exact rec9985 10 42 (by decide) (by decide)
      · right
        exact rec9993 10 42 (by decide) (by decide)
      · right
        exact rec10001 10 42 (by decide) (by decide)
      · right
        exact rec10009 10 42 (by decide) (by decide)
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
        exact rec10016 10 42 (by decide) (by decide)
      · right
        exact rec10023 10 42 (by decide) (by decide)
      · right
        exact rec10030 10 42 (by decide) (by decide)
      · right
        exact rec10036 10 42 (by decide) (by decide)
      · right
        exact rec10043 10 42 (by decide) (by decide)
      · right
        exact rec10050 10 42 (by decide) (by decide)
      · right
        exact rec10057 10 42 (by decide) (by decide)
      · right
        exact rec10064 10 42 (by decide) (by decide)
      · right
        exact rec10070 10 42 (by decide) (by decide)
      · right
        exact rec10077 10 42 (by decide) (by decide)
      · right
        exact rec10084 10 42 (by decide) (by decide)
      · right
        exact rec10091 10 42 (by decide) (by decide)
      · right
        exact rec10098 10 42 (by decide) (by decide)
      · right
        exact rec10104 10 42 (by decide) (by decide)
      · right
        exact rec10111 10 42 (by decide) (by decide)
      · right
        exact rec10118 10 42 (by decide) (by decide)
      · right
        exact rec10125 10 42 (by decide) (by decide)
      · right
        exact rec10132 10 42 (by decide) (by decide)
      · right
        exact rec10138 10 42 (by decide) (by decide)
      · right
        exact rec10145 10 42 (by decide) (by decide)
      · right
        exact rec10152 10 42 (by decide) (by decide)
      · right
        exact rec10159 10 42 (by decide) (by decide)
      · right
        exact rec10166 10 42 (by decide) (by decide)
      · right
        exact rec10172 10 42 (by decide) (by decide)
      · right
        exact rec10179 10 42 (by decide) (by decide)
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
        exact rec10187 10 42 (by decide) (by decide)
      · right
        exact rec10195 10 42 (by decide) (by decide)
      · right
        exact rec10203 10 42 (by decide) (by decide)
      · right
        exact rec10211 10 42 (by decide) (by decide)
      · right
        exact rec10219 10 42 (by decide) (by decide)
      · right
        exact rec10227 10 42 (by decide) (by decide)
      · right
        exact rec10235 10 42 (by decide) (by decide)
      · right
        exact rec10243 10 42 (by decide) (by decide)
      · right
        exact rec10251 10 42 (by decide) (by decide)
      · right
        exact rec10259 10 42 (by decide) (by decide)
      · right
        exact rec10267 10 42 (by decide) (by decide)
      · right
        exact rec10275 10 42 (by decide) (by decide)
      · right
        exact rec10283 10 42 (by decide) (by decide)
      · right
        exact rec10291 10 42 (by decide) (by decide)
      · right
        exact rec10299 10 42 (by decide) (by decide)
      · right
        exact rec10307 10 42 (by decide) (by decide)
      · right
        exact rec10315 10 42 (by decide) (by decide)
      · right
        exact rec10323 10 42 (by decide) (by decide)
      · right
        exact rec10331 10 42 (by decide) (by decide)
      · right
        exact rec10339 10 42 (by decide) (by decide)
      · right
        exact rec10347 10 42 (by decide) (by decide)
      · right
        exact rec10355 10 42 (by decide) (by decide)
      · right
        exact rec10363 10 42 (by decide) (by decide)
      · right
        exact rec10371 10 42 (by decide) (by decide)
      · right
        exact rec10379 10 42 (by decide) (by decide)
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
        exact rec10384 10 42 (by decide) (by decide)
      · right
        exact rec10388 10 42 (by decide) (by decide)
      · right
        exact rec10392 10 42 (by decide) (by decide)
      · right
        exact rec10396 10 42 (by decide) (by decide)
      · right
        exact rec10400 10 42 (by decide) (by decide)
      · right
        exact rec10404 10 42 (by decide) (by decide)
      · right
        exact rec10408 10 42 (by decide) (by decide)
      · right
        exact rec10412 10 42 (by decide) (by decide)
      · right
        exact rec10416 10 42 (by decide) (by decide)
      · right
        exact rec10420 10 42 (by decide) (by decide)
      · right
        exact rec10424 10 42 (by decide) (by decide)
      · right
        exact rec10428 10 42 (by decide) (by decide)
      · right
        exact rec10432 10 42 (by decide) (by decide)
      · right
        exact rec10436 10 42 (by decide) (by decide)
      · right
        exact rec10440 10 42 (by decide) (by decide)
      · right
        exact rec10444 10 42 (by decide) (by decide)
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
        exact rec10451 10 42 (by decide) (by decide)
      · right
        exact rec10459 10 42 (by decide) (by decide)
      · right
        exact rec10467 10 42 (by decide) (by decide)
      · right
        exact rec10475 10 42 (by decide) (by decide)
      · right
        exact rec10483 10 42 (by decide) (by decide)
      · right
        exact rec10491 10 42 (by decide) (by decide)
      · right
        exact rec10502 10 42 (by decide) (by decide)
      · right
        exact rec10510 10 42 (by decide) (by decide)
      · right
        exact rec10518 10 42 (by decide) (by decide)
      · right
        exact rec10526 10 42 (by decide) (by decide)
      · right
        exact rec10534 10 42 (by decide) (by decide)
      · right
        exact rec10542 10 42 (by decide) (by decide)
      · right
        exact rec10550 10 42 (by decide) (by decide)
      · right
        exact rec10558 10 42 (by decide) (by decide)
      · right
        exact rec10566 10 42 (by decide) (by decide)
      · right
        exact rec10574 10 42 (by decide) (by decide)
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
        exact rec10579 10 42 (by decide) (by decide)
      · right
        exact rec10583 10 42 (by decide) (by decide)
      · right
        exact rec10587 10 42 (by decide) (by decide)
      · right
        exact rec10591 10 42 (by decide) (by decide)
      · right
        exact rec10595 10 42 (by decide) (by decide)
      · right
        exact rec10599 10 42 (by decide) (by decide)
      · right
        exact rec10603 10 42 (by decide) (by decide)
      · right
        exact rec10607 10 42 (by decide) (by decide)
      · right
        exact rec10611 10 42 (by decide) (by decide)
      · right
        exact rec10615 10 42 (by decide) (by decide)
      · right
        exact rec10619 10 42 (by decide) (by decide)
      · right
        exact rec10623 10 42 (by decide) (by decide)
      · right
        exact rec10627 10 42 (by decide) (by decide)
      · right
        exact rec10631 10 42 (by decide) (by decide)
      · right
        exact rec10635 10 42 (by decide) (by decide)
      · right
        exact rec10639 10 42 (by decide) (by decide)
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
        exact rec10646 10 42 (by decide) (by decide)
      · right
        exact rec10654 10 42 (by decide) (by decide)
      · right
        exact rec10662 10 42 (by decide) (by decide)
      · right
        exact rec10670 10 42 (by decide) (by decide)
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
        exact rec10676 10 42 (by decide) (by decide)
      · right
        exact rec10680 10 42 (by decide) (by decide)
      · right
        exact rec10684 10 42 (by decide) (by decide)
      · right
        exact rec10688 10 42 (by decide) (by decide)
      · right
        exact rec10692 10 42 (by decide) (by decide)
      · right
        exact rec10696 10 42 (by decide) (by decide)
      · right
        exact rec10700 10 42 (by decide) (by decide)
      · right
        exact rec10704 10 42 (by decide) (by decide)
      · right
        exact rec10708 10 42 (by decide) (by decide)
      · right
        exact rec10712 10 42 (by decide) (by decide)
      · right
        exact rec10716 10 42 (by decide) (by decide)
      · right
        exact rec10720 10 42 (by decide) (by decide)
      · right
        exact rec10724 10 42 (by decide) (by decide)
      · right
        exact rec10728 10 42 (by decide) (by decide)
      · right
        exact rec10732 10 42 (by decide) (by decide)
      · right
        exact rec10736 10 42 (by decide) (by decide)
      · right
        exact rec10740 10 42 (by decide) (by decide)
      · right
        exact rec10744 10 42 (by decide) (by decide)
      · right
        exact rec10748 10 42 (by decide) (by decide)
      · right
        exact rec10752 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 221)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10759 10 42 (by decide) (by decide)
      · right
        exact rec10767 10 42 (by decide) (by decide)
      · right
        exact rec10775 10 42 (by decide) (by decide)
      · right
        exact rec10783 10 42 (by decide) (by decide)
      · right
        exact rec10791 10 42 (by decide) (by decide)
      · right
        exact rec10799 10 42 (by decide) (by decide)
      · right
        exact rec10807 10 42 (by decide) (by decide)
      · right
        exact rec10815 10 42 (by decide) (by decide)
      · right
        exact rec10823 10 42 (by decide) (by decide)
      · right
        exact rec10831 10 42 (by decide) (by decide)
      · right
        exact rec10839 10 42 (by decide) (by decide)
      · right
        exact rec10847 10 42 (by decide) (by decide)
      · right
        exact rec10855 10 42 (by decide) (by decide)
      · right
        exact rec10863 10 42 (by decide) (by decide)
      · right
        exact rec10871 10 42 (by decide) (by decide)
      · right
        exact rec10879 10 42 (by decide) (by decide)
      · right
        exact rec10887 10 42 (by decide) (by decide)
      · right
        exact rec10895 10 42 (by decide) (by decide)
      · right
        exact rec10903 10 42 (by decide) (by decide)
      · right
        exact rec10912 10 42 (by decide) (by decide)
      · right
        exact rec10920 10 42 (by decide) (by decide)
      · right
        exact rec10928 10 42 (by decide) (by decide)
      · right
        exact rec10936 10 42 (by decide) (by decide)
      · right
        exact rec10944 10 42 (by decide) (by decide)
      · right
        exact rec10953 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 222)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10962 10 42 (by decide) (by decide)
      · right
        exact rec10969 10 42 (by decide) (by decide)
      · right
        exact rec10977 10 42 (by decide) (by decide)
      · right
        exact rec10984 10 42 (by decide) (by decide)
      · right
        exact rec10990 10 42 (by decide) (by decide)
      · right
        exact rec10997 10 42 (by decide) (by decide)
      · right
        exact rec11006 10 42 (by decide) (by decide)
      · right
        exact rec11014 10 42 (by decide) (by decide)
      · right
        exact rec11021 10 42 (by decide) (by decide)
      · right
        exact rec11027 10 42 (by decide) (by decide)
      · right
        exact rec11036 10 42 (by decide) (by decide)
      · right
        exact rec11045 10 42 (by decide) (by decide)
      · right
        exact rec11055 10 42 (by decide) (by decide)
      · right
        exact rec11064 10 42 (by decide) (by decide)
      · right
        exact rec11070 10 42 (by decide) (by decide)
      · right
        exact rec11077 10 42 (by decide) (by decide)
      · right
        exact rec11084 10 42 (by decide) (by decide)
      · right
        exact rec11092 10 42 (by decide) (by decide)
      · right
        exact rec11099 10 42 (by decide) (by decide)
      · right
        exact rec11105 10 42 (by decide) (by decide)
      · right
        exact rec11111 10 42 (by decide) (by decide)
      · right
        exact rec11117 10 42 (by decide) (by decide)
      · right
        exact rec11123 10 42 (by decide) (by decide)
      · right
        exact rec11129 10 42 (by decide) (by decide)
      · right
        exact rec11136 10 42 (by decide) (by decide)
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
        exact rec11142 10 42 (by decide) (by decide)
      · right
        exact rec11148 10 42 (by decide) (by decide)
      · right
        exact rec11154 10 42 (by decide) (by decide)
      · right
        exact rec11160 10 42 (by decide) (by decide)
      · right
        exact rec11166 10 42 (by decide) (by decide)
      · right
        exact rec11174 10 42 (by decide) (by decide)
      · right
        exact rec11182 10 42 (by decide) (by decide)
      · right
        exact rec11190 10 42 (by decide) (by decide)
      · right
        exact rec11198 10 42 (by decide) (by decide)
      · right
        exact rec11206 10 42 (by decide) (by decide)
      · right
        exact rec11214 10 42 (by decide) (by decide)
      · right
        exact rec11222 10 42 (by decide) (by decide)
      · right
        exact rec11230 10 42 (by decide) (by decide)
      · right
        exact rec11238 10 42 (by decide) (by decide)
      · right
        exact rec11246 10 42 (by decide) (by decide)
      · right
        exact rec11254 10 42 (by decide) (by decide)
      · right
        exact rec11262 10 42 (by decide) (by decide)
      · right
        exact rec11270 10 42 (by decide) (by decide)
      · right
        exact rec11278 10 42 (by decide) (by decide)
      · right
        exact rec11286 10 42 (by decide) (by decide)
      · right
        exact rec11294 10 42 (by decide) (by decide)
      · right
        exact rec11302 10 42 (by decide) (by decide)
      · right
        exact rec11310 10 42 (by decide) (by decide)
      · right
        exact rec11318 10 42 (by decide) (by decide)
      · right
        exact rec11326 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 225)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11332 10 42 (by decide) (by decide)
      · right
        exact rec11338 10 42 (by decide) (by decide)
      · right
        exact rec11345 10 42 (by decide) (by decide)
      · right
        exact rec11352 10 42 (by decide) (by decide)
      · right
        exact rec11359 10 42 (by decide) (by decide)
      · right
        exact rec11365 10 42 (by decide) (by decide)
      · right
        exact rec11371 10 42 (by decide) (by decide)
      · right
        exact rec11379 10 42 (by decide) (by decide)
      · right
        exact rec11386 10 42 (by decide) (by decide)
      · right
        exact rec11394 10 42 (by decide) (by decide)
      · right
        exact rec11400 10 42 (by decide) (by decide)
      · right
        exact rec11406 10 42 (by decide) (by decide)
      · right
        exact rec11414 10 42 (by decide) (by decide)
      · right
        exact rec11421 10 42 (by decide) (by decide)
      · right
        exact rec11429 10 42 (by decide) (by decide)
      · right
        exact rec11435 10 42 (by decide) (by decide)
      · right
        exact rec11441 10 42 (by decide) (by decide)
      · right
        exact rec11449 10 42 (by decide) (by decide)
      · right
        exact rec11456 10 42 (by decide) (by decide)
      · right
        exact rec11464 10 42 (by decide) (by decide)
      · right
        exact rec11470 10 42 (by decide) (by decide)
      · right
        exact rec11476 10 42 (by decide) (by decide)
      · right
        exact rec11484 10 42 (by decide) (by decide)
      · right
        exact rec11491 10 42 (by decide) (by decide)
      · right
        exact rec11499 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 226)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11506 10 42 (by decide) (by decide)
      · right
        exact rec11512 10 42 (by decide) (by decide)
      · right
        exact rec11518 10 42 (by decide) (by decide)
      · right
        exact rec11524 10 42 (by decide) (by decide)
      · right
        exact rec11530 10 42 (by decide) (by decide)
      · right
        exact rec11536 10 42 (by decide) (by decide)
      · right
        exact rec11542 10 42 (by decide) (by decide)
      · right
        exact rec11548 10 42 (by decide) (by decide)
      · right
        exact rec11554 10 42 (by decide) (by decide)
      · right
        exact rec11560 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 227)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11566 10 42 (by decide) (by decide)
      · right
        exact rec11572 10 42 (by decide) (by decide)
      · right
        exact rec11580 10 42 (by decide) (by decide)
      · right
        exact rec11586 10 42 (by decide) (by decide)
      · right
        exact rec11594 10 42 (by decide) (by decide)
      · right
        exact rec11600 10 42 (by decide) (by decide)
      · right
        exact rec11606 10 42 (by decide) (by decide)
      · right
        exact rec11614 10 42 (by decide) (by decide)
      · right
        exact rec11620 10 42 (by decide) (by decide)
      · right
        exact rec11628 10 42 (by decide) (by decide)
      · right
        exact rec11634 10 42 (by decide) (by decide)
      · right
        exact rec11640 10 42 (by decide) (by decide)
      · right
        exact rec11648 10 42 (by decide) (by decide)
      · right
        exact rec11654 10 42 (by decide) (by decide)
      · right
        exact rec11662 10 42 (by decide) (by decide)
      · right
        exact rec11668 10 42 (by decide) (by decide)
      · right
        exact rec11674 10 42 (by decide) (by decide)
      · right
        exact rec11682 10 42 (by decide) (by decide)
      · right
        exact rec11688 10 42 (by decide) (by decide)
      · right
        exact rec11696 10 42 (by decide) (by decide)
      · right
        exact rec11702 10 42 (by decide) (by decide)
      · right
        exact rec11708 10 42 (by decide) (by decide)
      · right
        exact rec11716 10 42 (by decide) (by decide)
      · right
        exact rec11722 10 42 (by decide) (by decide)
      · right
        exact rec11730 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 228)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11737 10 42 (by decide) (by decide)
      · right
        exact rec11744 10 42 (by decide) (by decide)
      · right
        exact rec11754 10 42 (by decide) (by decide)
      · right
        exact rec11761 10 42 (by decide) (by decide)
      · right
        exact rec11767 10 42 (by decide) (by decide)
      · right
        exact rec11773 10 42 (by decide) (by decide)
      · right
        exact rec11779 10 42 (by decide) (by decide)
      · right
        exact rec11785 10 42 (by decide) (by decide)
      · right
        exact rec11791 10 42 (by decide) (by decide)
      · right
        exact rec11798 10 42 (by decide) (by decide)
      · right
        exact rec11804 10 42 (by decide) (by decide)
      · right
        exact rec11810 10 42 (by decide) (by decide)
      · right
        exact rec11816 10 42 (by decide) (by decide)
      · right
        exact rec11822 10 42 (by decide) (by decide)
      · right
        exact rec11828 10 42 (by decide) (by decide)
      · right
        exact rec11834 10 42 (by decide) (by decide)
      · right
        exact rec11840 10 42 (by decide) (by decide)
      · right
        exact rec11846 10 42 (by decide) (by decide)
      · right
        exact rec11852 10 42 (by decide) (by decide)
      · right
        exact rec11858 10 42 (by decide) (by decide)
      · right
        exact rec11864 10 42 (by decide) (by decide)
      · right
        exact rec11870 10 42 (by decide) (by decide)
      · right
        exact rec11876 10 42 (by decide) (by decide)
      · right
        exact rec11882 10 42 (by decide) (by decide)
      · right
        exact rec11888 10 42 (by decide) (by decide)
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
        exact rec11894 10 42 (by decide) (by decide)
      · right
        exact rec11900 10 42 (by decide) (by decide)
      · right
        exact rec11907 10 42 (by decide) (by decide)
      · right
        exact rec11913 10 42 (by decide) (by decide)
      · right
        exact rec11919 10 42 (by decide) (by decide)
      · right
        exact rec11925 10 42 (by decide) (by decide)
      · right
        exact rec11931 10 42 (by decide) (by decide)
      · right
        exact rec11940 10 42 (by decide) (by decide)
      · right
        exact rec11947 10 42 (by decide) (by decide)
      · right
        exact rec11956 10 42 (by decide) (by decide)
      · right
        exact rec11962 10 42 (by decide) (by decide)
      · right
        exact rec11968 10 42 (by decide) (by decide)
      · right
        exact rec11976 10 42 (by decide) (by decide)
      · right
        exact rec11982 10 42 (by decide) (by decide)
      · right
        exact rec11991 10 42 (by decide) (by decide)
      · right
        exact rec11997 10 42 (by decide) (by decide)
      · right
        exact rec12003 10 42 (by decide) (by decide)
      · right
        exact rec12011 10 42 (by decide) (by decide)
      · right
        exact rec12017 10 42 (by decide) (by decide)
      · right
        exact rec12025 10 42 (by decide) (by decide)
      · right
        exact rec12031 10 42 (by decide) (by decide)
      · right
        exact rec12037 10 42 (by decide) (by decide)
      · right
        exact rec12045 10 42 (by decide) (by decide)
      · right
        exact rec12051 10 42 (by decide) (by decide)
      · right
        exact rec12059 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 231)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12066 10 42 (by decide) (by decide)
      · right
        exact rec12074 10 42 (by decide) (by decide)
      · right
        exact rec12080 10 42 (by decide) (by decide)
      · right
        exact rec12086 10 42 (by decide) (by decide)
      · right
        exact rec12093 10 42 (by decide) (by decide)
      · right
        exact rec12101 10 42 (by decide) (by decide)
      · right
        exact rec12107 10 42 (by decide) (by decide)
      · right
        exact rec12113 10 42 (by decide) (by decide)
      · right
        exact rec12119 10 42 (by decide) (by decide)
      · right
        exact rec12125 10 42 (by decide) (by decide)
      · right
        exact rec12131 10 42 (by decide) (by decide)
      · right
        exact rec12137 10 42 (by decide) (by decide)
      · right
        exact rec12143 10 42 (by decide) (by decide)
      · right
        exact rec12149 10 42 (by decide) (by decide)
      · right
        exact rec12155 10 42 (by decide) (by decide)
      · right
        exact rec12161 10 42 (by decide) (by decide)
      · right
        exact rec12167 10 42 (by decide) (by decide)
      · right
        exact rec12173 10 42 (by decide) (by decide)
      · right
        exact rec12179 10 42 (by decide) (by decide)
      · right
        exact rec12185 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 232)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12191 10 42 (by decide) (by decide)
      · right
        exact rec12197 10 42 (by decide) (by decide)
      · right
        exact rec12204 10 42 (by decide) (by decide)
      · right
        exact rec12210 10 42 (by decide) (by decide)
      · right
        exact rec12218 10 42 (by decide) (by decide)
      · right
        exact rec12224 10 42 (by decide) (by decide)
      · right
        exact rec12230 10 42 (by decide) (by decide)
      · right
        exact rec12237 10 42 (by decide) (by decide)
      · right
        exact rec12243 10 42 (by decide) (by decide)
      · right
        exact rec12251 10 42 (by decide) (by decide)
      · right
        exact rec12257 10 42 (by decide) (by decide)
      · right
        exact rec12263 10 42 (by decide) (by decide)
      · right
        exact rec12270 10 42 (by decide) (by decide)
      · right
        exact rec12276 10 42 (by decide) (by decide)
      · right
        exact rec12284 10 42 (by decide) (by decide)
      · right
        exact rec12290 10 42 (by decide) (by decide)
      · right
        exact rec12296 10 42 (by decide) (by decide)
      · right
        exact rec12303 10 42 (by decide) (by decide)
      · right
        exact rec12309 10 42 (by decide) (by decide)
      · right
        exact rec12317 10 42 (by decide) (by decide)
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
        exact rec12323 10 42 (by decide) (by decide)
      · right
        exact rec12331 10 42 (by decide) (by decide)
      · right
        exact rec12339 10 42 (by decide) (by decide)
      · right
        exact rec12347 10 42 (by decide) (by decide)
      · right
        exact rec12353 10 42 (by decide) (by decide)
      · right
        exact rec12361 10 42 (by decide) (by decide)
      · right
        exact rec12369 10 42 (by decide) (by decide)
      · right
        exact rec12377 10 42 (by decide) (by decide)
      · right
        exact rec12383 10 42 (by decide) (by decide)
      · right
        exact rec12391 10 42 (by decide) (by decide)
      · right
        exact rec12399 10 42 (by decide) (by decide)
      · right
        exact rec12407 10 42 (by decide) (by decide)
      · right
        exact rec12413 10 42 (by decide) (by decide)
      · right
        exact rec12421 10 42 (by decide) (by decide)
      · right
        exact rec12429 10 42 (by decide) (by decide)
      · right
        exact rec12437 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 235)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12443 10 42 (by decide) (by decide)
      · right
        exact rec12449 10 42 (by decide) (by decide)
      · right
        exact rec12457 10 42 (by decide) (by decide)
      · right
        exact rec12463 10 42 (by decide) (by decide)
      · right
        exact rec12469 10 42 (by decide) (by decide)
      · right
        exact rec12475 10 42 (by decide) (by decide)
      · right
        exact rec12483 10 42 (by decide) (by decide)
      · right
        exact rec12489 10 42 (by decide) (by decide)
      · right
        exact rec12495 10 42 (by decide) (by decide)
      · right
        exact rec12501 10 42 (by decide) (by decide)
      · right
        exact rec12509 10 42 (by decide) (by decide)
      · right
        exact rec12515 10 42 (by decide) (by decide)
      · right
        exact rec12521 10 42 (by decide) (by decide)
      · right
        exact rec12527 10 42 (by decide) (by decide)
      · right
        exact rec12535 10 42 (by decide) (by decide)
      · right
        exact rec12541 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 236)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12548 10 42 (by decide) (by decide)
      · right
        exact rec12555 10 42 (by decide) (by decide)
      · right
        exact rec12564 10 42 (by decide) (by decide)
      · right
        exact rec12571 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 237)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12578 10 42 (by decide) (by decide)
      · right
        exact rec12584 10 42 (by decide) (by decide)
      · right
        exact rec12591 10 42 (by decide) (by decide)
      · right
        exact rec12599 10 42 (by decide) (by decide)
      · right
        exact rec12606 10 42 (by decide) (by decide)
      · right
        exact rec12612 10 42 (by decide) (by decide)
      · right
        exact rec12618 10 42 (by decide) (by decide)
      · right
        exact rec12624 10 42 (by decide) (by decide)
      · right
        exact rec12633 10 42 (by decide) (by decide)
      · right
        exact rec12639 10 42 (by decide) (by decide)
      · right
        exact rec12645 10 42 (by decide) (by decide)
      · right
        exact rec12651 10 42 (by decide) (by decide)
      · right
        exact rec12658 10 42 (by decide) (by decide)
      · right
        exact rec12664 10 42 (by decide) (by decide)
      · right
        exact rec12670 10 42 (by decide) (by decide)
      · right
        exact rec12676 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 238)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12682 10 42 (by decide) (by decide)
      · right
        exact rec12688 10 42 (by decide) (by decide)
      · right
        exact rec12696 10 42 (by decide) (by decide)
      · right
        exact rec12703 10 42 (by decide) (by decide)
      · right
        exact rec12709 10 42 (by decide) (by decide)
      · right
        exact rec12715 10 42 (by decide) (by decide)
      · right
        exact rec12723 10 42 (by decide) (by decide)
      · right
        exact rec12729 10 42 (by decide) (by decide)
      · right
        exact rec12735 10 42 (by decide) (by decide)
      · right
        exact rec12741 10 42 (by decide) (by decide)
      · right
        exact rec12749 10 42 (by decide) (by decide)
      · right
        exact rec12755 10 42 (by decide) (by decide)
      · right
        exact rec12761 10 42 (by decide) (by decide)
      · right
        exact rec12767 10 42 (by decide) (by decide)
      · right
        exact rec12775 10 42 (by decide) (by decide)
      · right
        exact rec12781 10 42 (by decide) (by decide)
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
        exact rec12786 10 42 (by decide) (by decide)
      · right
        exact rec12790 10 42 (by decide) (by decide)
      · right
        exact rec12794 10 42 (by decide) (by decide)
      · right
        exact rec12798 10 42 (by decide) (by decide)
      · right
        exact rec12802 10 42 (by decide) (by decide)
      · right
        exact rec12806 10 42 (by decide) (by decide)
      · right
        exact rec12810 10 42 (by decide) (by decide)
      · right
        exact rec12814 10 42 (by decide) (by decide)
      · right
        exact rec12818 10 42 (by decide) (by decide)
      · right
        exact rec12822 10 42 (by decide) (by decide)
      · right
        exact rec12826 10 42 (by decide) (by decide)
      · right
        exact rec12830 10 42 (by decide) (by decide)
      · right
        exact rec12834 10 42 (by decide) (by decide)
      · right
        exact rec12838 10 42 (by decide) (by decide)
      · right
        exact rec12842 10 42 (by decide) (by decide)
      · right
        exact rec12846 10 42 (by decide) (by decide)
      · right
        exact rec12850 10 42 (by decide) (by decide)
      · right
        exact rec12854 10 42 (by decide) (by decide)
      · right
        exact rec12858 10 42 (by decide) (by decide)
      · right
        exact rec12862 10 42 (by decide) (by decide)
      · right
        exact rec12866 10 42 (by decide) (by decide)
      · right
        exact rec12870 10 42 (by decide) (by decide)
      · right
        exact rec12874 10 42 (by decide) (by decide)
      · right
        exact rec12878 10 42 (by decide) (by decide)
      · right
        exact rec12882 10 42 (by decide) (by decide)
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
    exact rec7430 10 43 (by decide) (by decide)
  · left
    exact rec7425 10 44 (by decide) (by decide)
  · left
    exact rec7425 10 45 (by decide) (by decide)
  · left
    exact rec7432 10 46 (by decide) (by decide)
  · left
    exact rec7430 10 47 (by decide) (by decide)
end Section14Coverage_10_5_p32_48

#print axioms solution
