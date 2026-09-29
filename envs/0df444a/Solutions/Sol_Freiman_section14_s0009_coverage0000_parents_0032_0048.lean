-- Prove2me | solution 1 for Freiman.section14_s0009_coverage0000_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T18:43:07.541228+00:00
-- url     : https://prove2.me/submissions/1869e3a6-2bfa-4734-907c-ecdcfa69a940

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
namespace Section14Coverage_9_0_p32_48
private theorem rec48 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[48]? = some (⟨1,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) from rfl))
private theorem rec51 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[9,10],[34],6⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[51]? = some (⟨1,(-1),[9,10],[34],6⟩) from rfl))
private theorem rec52 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35, 39, 43, 47] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[9,10],[35,39,43,47],8⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[52]? = some (⟨1,(-1),[9,10],[35,39,43,47],8⟩) from rfl))
private theorem rec53 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[9,10],[38],9⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[53]? = some (⟨1,(-1),[9,10],[38],9⟩) from rfl))
private theorem rec54 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 1 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨1,(-1),[9,10],[46],55⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[54]? = some (⟨1,(-1),[9,10],[46],55⟩) from rfl))
private theorem rec61 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(0),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[61]? = some (⟨3,(0),[9,10],[42],3⟩) from rfl))
private theorem rec63 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(1),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[63]? = some (⟨3,(1),[9,10],[42],3⟩) from rfl))
private theorem rec65 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(2),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[65]? = some (⟨3,(2),[9,10],[42],3⟩) from rfl))
private theorem rec67 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(3),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[67]? = some (⟨3,(3),[9,10],[42],3⟩) from rfl))
private theorem rec69 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(4),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[69]? = some (⟨3,(4),[9,10],[42],3⟩) from rfl))
private theorem rec71 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(5),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[71]? = some (⟨3,(5),[9,10],[42],3⟩) from rfl))
private theorem rec73 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(6),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[73]? = some (⟨3,(6),[9,10],[42],3⟩) from rfl))
private theorem rec75 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(7),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[75]? = some (⟨3,(7),[9,10],[42],3⟩) from rfl))
private theorem rec77 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(8),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[77]? = some (⟨3,(8),[9,10],[42],3⟩) from rfl))
private theorem rec79 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(9),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[79]? = some (⟨3,(9),[9,10],[42],3⟩) from rfl))
private theorem rec81 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(10),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[81]? = some (⟨3,(10),[9,10],[42],3⟩) from rfl))
private theorem rec83 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(11),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[83]? = some (⟨3,(11),[9,10],[42],3⟩) from rfl))
private theorem rec85 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(12),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[85]? = some (⟨3,(12),[9,10],[42],3⟩) from rfl))
private theorem rec87 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(13),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[87]? = some (⟨3,(13),[9,10],[42],3⟩) from rfl))
private theorem rec89 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(14),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[89]? = some (⟨3,(14),[9,10],[42],3⟩) from rfl))
private theorem rec91 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(15),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[91]? = some (⟨3,(15),[9,10],[42],3⟩) from rfl))
private theorem rec93 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(16),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[93]? = some (⟨3,(16),[9,10],[42],3⟩) from rfl))
private theorem rec95 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(17),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[95]? = some (⟨3,(17),[9,10],[42],3⟩) from rfl))
private theorem rec97 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(18),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[97]? = some (⟨3,(18),[9,10],[42],3⟩) from rfl))
private theorem rec99 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(19),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[99]? = some (⟨3,(19),[9,10],[42],3⟩) from rfl))
private theorem rec101 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(20),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[101]? = some (⟨3,(20),[9,10],[42],3⟩) from rfl))
private theorem rec103 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(21),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[103]? = some (⟨3,(21),[9,10],[42],3⟩) from rfl))
private theorem rec105 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(22),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[105]? = some (⟨3,(22),[9,10],[42],3⟩) from rfl))
private theorem rec107 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(23),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[107]? = some (⟨3,(23),[9,10],[42],3⟩) from rfl))
private theorem rec109 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 3 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨3,(24),[9,10],[42],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[109]? = some (⟨3,(24),[9,10],[42],3⟩) from rfl))
private theorem rec168 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(0),[9,10],[42],6⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[168]? = some (⟨9,(0),[9,10],[42],6⟩) from rfl))
private theorem rec171 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(1),[9,10],[42],27⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[171]? = some (⟨9,(1),[9,10],[42],27⟩) from rfl))
private theorem rec174 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(2),[9,10],[42],28⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[174]? = some (⟨9,(2),[9,10],[42],28⟩) from rfl))
private theorem rec177 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(3),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[177]? = some (⟨9,(3),[9,10],[42],29⟩) from rfl))
private theorem rec180 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(4),[9,10],[42],30⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[180]? = some (⟨9,(4),[9,10],[42],30⟩) from rfl))
private theorem rec183 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(5),[9,10],[42],6⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[183]? = some (⟨9,(5),[9,10],[42],6⟩) from rfl))
private theorem rec186 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(6),[9,10],[42],27⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[186]? = some (⟨9,(6),[9,10],[42],27⟩) from rfl))
private theorem rec189 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(7),[9,10],[42],31⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[189]? = some (⟨9,(7),[9,10],[42],31⟩) from rfl))
private theorem rec192 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(8),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[192]? = some (⟨9,(8),[9,10],[42],29⟩) from rfl))
private theorem rec195 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(9),[9,10],[42],32⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[195]? = some (⟨9,(9),[9,10],[42],32⟩) from rfl))
private theorem rec198 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(10),[9,10],[42],6⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[198]? = some (⟨9,(10),[9,10],[42],6⟩) from rfl))
private theorem rec201 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(11),[9,10],[42],27⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[201]? = some (⟨9,(11),[9,10],[42],27⟩) from rfl))
private theorem rec204 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(12),[9,10],[42],33⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[204]? = some (⟨9,(12),[9,10],[42],33⟩) from rfl))
private theorem rec207 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(13),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[207]? = some (⟨9,(13),[9,10],[42],29⟩) from rfl))
private theorem rec210 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(14),[9,10],[42],34⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[210]? = some (⟨9,(14),[9,10],[42],34⟩) from rfl))
private theorem rec213 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(15),[9,10],[42],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[213]? = some (⟨9,(15),[9,10],[42],35⟩) from rfl))
private theorem rec216 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(16),[9,10],[42],36⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[216]? = some (⟨9,(16),[9,10],[42],36⟩) from rfl))
private theorem rec219 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(17),[9,10],[42],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[219]? = some (⟨9,(17),[9,10],[42],37⟩) from rfl))
private theorem rec222 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(18),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[222]? = some (⟨9,(18),[9,10],[42],29⟩) from rfl))
private theorem rec225 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(19),[9,10],[42],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[225]? = some (⟨9,(19),[9,10],[42],37⟩) from rfl))
private theorem rec228 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(20),[9,10],[42],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[228]? = some (⟨9,(20),[9,10],[42],38⟩) from rfl))
private theorem rec231 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(21),[9,10],[42],39⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[231]? = some (⟨9,(21),[9,10],[42],39⟩) from rfl))
private theorem rec234 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(22),[9,10],[42],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[234]? = some (⟨9,(22),[9,10],[42],40⟩) from rfl))
private theorem rec237 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(23),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[237]? = some (⟨9,(23),[9,10],[42],29⟩) from rfl))
private theorem rec240 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 9 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨9,(24),[9,10],[42],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[240]? = some (⟨9,(24),[9,10],[42],40⟩) from rfl))
private theorem rec321 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 15 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(1),[9,10],[42],49⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[321]? = some (⟨15,(1),[9,10],[42],49⟩) from rfl))
private theorem rec324 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 15 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(3),[9,10],[42],50⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[324]? = some (⟨15,(3),[9,10],[42],50⟩) from rfl))
private theorem rec329 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 15 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(5),[9,10],[42],51⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[329]? = some (⟨15,(5),[9,10],[42],51⟩) from rfl))
private theorem rec334 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 15 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(7),[9],[42],52⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[334]? = some (⟨15,(7),[9],[42],52⟩) from rfl))
private theorem rec340 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 15 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(11),[9],[42],52⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[340]? = some (⟨15,(11),[9],[42],52⟩) from rfl))
private theorem rec346 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 15 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(13),[9],[42],52⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[346]? = some (⟨15,(13),[9],[42],52⟩) from rfl))
private theorem rec351 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 15 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(15),[9,10],[42],53⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[351]? = some (⟨15,(15),[9,10],[42],53⟩) from rfl))
private theorem rec357 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 15 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨15,(17),[9],[42],52⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[357]? = some (⟨15,(17),[9],[42],52⟩) from rfl))
private theorem rec16204 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(0),[9,10],[42],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1283]? = some (⟨537,(0),[9,10],[42],1649⟩) from rfl))
private theorem rec16207 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(1),[9,10],[42],1650⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1286]? = some (⟨537,(1),[9,10],[42],1650⟩) from rfl))
private theorem rec16210 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(2),[9,10],[42],1651⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[2]? = some (⟨537,(2),[9,10],[42],1651⟩) from rfl))
private theorem rec16213 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(3),[9,10],[42],1652⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[5]? = some (⟨537,(3),[9,10],[42],1652⟩) from rfl))
private theorem rec16216 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(4),[9,10],[42],17⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[8]? = some (⟨537,(4),[9,10],[42],17⟩) from rfl))
private theorem rec16219 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(5),[9,10],[42],1649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[11]? = some (⟨537,(5),[9,10],[42],1649⟩) from rfl))
private theorem rec16222 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(6),[9,10],[42],1650⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[14]? = some (⟨537,(6),[9,10],[42],1650⟩) from rfl))
private theorem rec16225 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(7),[9,10],[42],1651⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[17]? = some (⟨537,(7),[9,10],[42],1651⟩) from rfl))
private theorem rec16228 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(8),[9,10],[42],1652⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[20]? = some (⟨537,(8),[9,10],[42],1652⟩) from rfl))
private theorem rec16231 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 537 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨537,(9),[9,10],[42],17⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[23]? = some (⟨537,(9),[9,10],[42],17⟩) from rfl))
private theorem rec16234 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(0),[9,10],[42],46⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[26]? = some (⟨542,(0),[9,10],[42],46⟩) from rfl))
private theorem rec16237 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(1),[9,10],[42],46⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[29]? = some (⟨542,(1),[9,10],[42],46⟩) from rfl))
private theorem rec16240 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(2),[9,10],[42],42⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[32]? = some (⟨542,(2),[9,10],[42],42⟩) from rfl))
private theorem rec16243 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(3),[9,10],[42],43⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[35]? = some (⟨542,(3),[9,10],[42],43⟩) from rfl))
private theorem rec16246 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(4),[9,10],[42],44⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[38]? = some (⟨542,(4),[9,10],[42],44⟩) from rfl))
private theorem rec16249 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(5),[9,10],[42],47⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[41]? = some (⟨542,(5),[9,10],[42],47⟩) from rfl))
private theorem rec16252 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(6),[9,10],[42],47⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[44]? = some (⟨542,(6),[9,10],[42],47⟩) from rfl))
private theorem rec16255 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(7),[9,10],[42],47⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[47]? = some (⟨542,(7),[9,10],[42],47⟩) from rfl))
private theorem rec16258 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(8),[9,10],[42],43⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[50]? = some (⟨542,(8),[9,10],[42],43⟩) from rfl))
private theorem rec16261 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 542 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨542,(9),[9,10],[42],44⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[53]? = some (⟨542,(9),[9,10],[42],44⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 9).plans.drop 0).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 32).take 16, section14Recorded section14Catalog 9 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 9 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 9).plans.drop 0).take 1 = [⟨1,1,[([1],[]),([],[1])],false,[(536,⟨([1],[]),true,([1],[]),false,false,[]⟩),(3,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(4,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(537,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(538,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(539,⟨([],[1]),true,([],[1]),false,false,[]⟩),(540,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(9,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(541,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(542,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(543,⟨([1],[]),true,([],[1]),false,false,[]⟩),(544,⟨([],[1]),true,([1],[]),false,false,[]⟩),(545,⟨([1],[]),true,([],[]),true,false,[]⟩),(15,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec48 9 32 (by decide) (by decide)
  · left
    exact rec48 9 33 (by decide) (by decide)
  · left
    exact rec51 9 34 (by decide) (by decide)
  · left
    exact rec52 9 35 (by decide) (by decide)
  · left
    exact rec48 9 36 (by decide) (by decide)
  · left
    exact rec48 9 37 (by decide) (by decide)
  · left
    exact rec53 9 38 (by decide) (by decide)
  · left
    exact rec52 9 39 (by decide) (by decide)
  · left
    exact rec48 9 40 (by decide) (by decide)
  · left
    exact rec48 9 41 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(536,⟨([1],[]),true,([1],[]),false,false,[]⟩),(3,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(4,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(537,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(538,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(539,⟨([],[1]),true,([],[1]),false,false,[]⟩),(540,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(9,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(541,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(542,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(543,⟨([1],[]),true,([],[1]),false,false,[]⟩),(544,⟨([],[1]),true,([1],[]),false,false,[]⟩),(545,⟨([1],[]),true,([],[]),true,false,[]⟩),(15,⟨([],[]),false,([],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 536)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 3)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec61 9 42 (by decide) (by decide)
      · right
        exact rec63 9 42 (by decide) (by decide)
      · right
        exact rec65 9 42 (by decide) (by decide)
      · right
        exact rec67 9 42 (by decide) (by decide)
      · right
        exact rec69 9 42 (by decide) (by decide)
      · right
        exact rec71 9 42 (by decide) (by decide)
      · right
        exact rec73 9 42 (by decide) (by decide)
      · right
        exact rec75 9 42 (by decide) (by decide)
      · right
        exact rec77 9 42 (by decide) (by decide)
      · right
        exact rec79 9 42 (by decide) (by decide)
      · right
        exact rec81 9 42 (by decide) (by decide)
      · right
        exact rec83 9 42 (by decide) (by decide)
      · right
        exact rec85 9 42 (by decide) (by decide)
      · right
        exact rec87 9 42 (by decide) (by decide)
      · right
        exact rec89 9 42 (by decide) (by decide)
      · right
        exact rec91 9 42 (by decide) (by decide)
      · right
        exact rec93 9 42 (by decide) (by decide)
      · right
        exact rec95 9 42 (by decide) (by decide)
      · right
        exact rec97 9 42 (by decide) (by decide)
      · right
        exact rec99 9 42 (by decide) (by decide)
      · right
        exact rec101 9 42 (by decide) (by decide)
      · right
        exact rec103 9 42 (by decide) (by decide)
      · right
        exact rec105 9 42 (by decide) (by decide)
      · right
        exact rec107 9 42 (by decide) (by decide)
      · right
        exact rec109 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 4)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 537)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16204 9 42 (by decide) (by decide)
      · right
        exact rec16207 9 42 (by decide) (by decide)
      · right
        exact rec16210 9 42 (by decide) (by decide)
      · right
        exact rec16213 9 42 (by decide) (by decide)
      · right
        exact rec16216 9 42 (by decide) (by decide)
      · right
        exact rec16219 9 42 (by decide) (by decide)
      · right
        exact rec16222 9 42 (by decide) (by decide)
      · right
        exact rec16225 9 42 (by decide) (by decide)
      · right
        exact rec16228 9 42 (by decide) (by decide)
      · right
        exact rec16231 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 538)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 539)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 540)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 9)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec168 9 42 (by decide) (by decide)
      · right
        exact rec171 9 42 (by decide) (by decide)
      · right
        exact rec174 9 42 (by decide) (by decide)
      · right
        exact rec177 9 42 (by decide) (by decide)
      · right
        exact rec180 9 42 (by decide) (by decide)
      · right
        exact rec183 9 42 (by decide) (by decide)
      · right
        exact rec186 9 42 (by decide) (by decide)
      · right
        exact rec189 9 42 (by decide) (by decide)
      · right
        exact rec192 9 42 (by decide) (by decide)
      · right
        exact rec195 9 42 (by decide) (by decide)
      · right
        exact rec198 9 42 (by decide) (by decide)
      · right
        exact rec201 9 42 (by decide) (by decide)
      · right
        exact rec204 9 42 (by decide) (by decide)
      · right
        exact rec207 9 42 (by decide) (by decide)
      · right
        exact rec210 9 42 (by decide) (by decide)
      · right
        exact rec213 9 42 (by decide) (by decide)
      · right
        exact rec216 9 42 (by decide) (by decide)
      · right
        exact rec219 9 42 (by decide) (by decide)
      · right
        exact rec222 9 42 (by decide) (by decide)
      · right
        exact rec225 9 42 (by decide) (by decide)
      · right
        exact rec228 9 42 (by decide) (by decide)
      · right
        exact rec231 9 42 (by decide) (by decide)
      · right
        exact rec234 9 42 (by decide) (by decide)
      · right
        exact rec237 9 42 (by decide) (by decide)
      · right
        exact rec240 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 541)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 542)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16234 9 42 (by decide) (by decide)
      · right
        exact rec16237 9 42 (by decide) (by decide)
      · right
        exact rec16240 9 42 (by decide) (by decide)
      · right
        exact rec16243 9 42 (by decide) (by decide)
      · right
        exact rec16246 9 42 (by decide) (by decide)
      · right
        exact rec16249 9 42 (by decide) (by decide)
      · right
        exact rec16252 9 42 (by decide) (by decide)
      · right
        exact rec16255 9 42 (by decide) (by decide)
      · right
        exact rec16258 9 42 (by decide) (by decide)
      · right
        exact rec16261 9 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 543)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 544)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 545)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 15)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · right
        exact rec321 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec324 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec329 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec334 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · right
        exact rec340 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec346 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec351 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec357 9 42 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec52 9 43 (by decide) (by decide)
  · left
    exact rec48 9 44 (by decide) (by decide)
  · left
    exact rec48 9 45 (by decide) (by decide)
  · left
    exact rec54 9 46 (by decide) (by decide)
  · left
    exact rec52 9 47 (by decide) (by decide)
end Section14Coverage_9_0_p32_48

#print axioms solution
