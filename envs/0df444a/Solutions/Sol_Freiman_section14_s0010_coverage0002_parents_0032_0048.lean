-- Prove2me | solution 1 for Freiman.section14_s0010_coverage0002_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T15:53:29.652839+00:00
-- url     : https://prove2.me/submissions/6952692d-2239-41bb-ba83-aa9944578bd1

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
namespace Section14Coverage_10_2_p32_48
private theorem rec3066 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[623]? = some (⟨38,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) from rfl))
private theorem rec3070 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([43] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[9,10],[43],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[627]? = some (⟨38,(-1),[9,10],[43],207⟩) from rfl))
private theorem rec3073 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[9,10],[34],249⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[630]? = some (⟨38,(-1),[9,10],[34],249⟩) from rfl))
private theorem rec3074 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35, 39] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[9,10],[35,39],251⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[631]? = some (⟨38,(-1),[9,10],[35,39],251⟩) from rfl))
private theorem rec3081 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([47, 63] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[10],[47,63],239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[638]? = some (⟨38,(-1),[10],[47,63],239⟩) from rfl))
private theorem rec3089 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(0),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[646]? = some (⟨40,(0),[9,10],[42,46],3⟩) from rfl))
private theorem rec3090 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(0),[9,10],[38],1532⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[647]? = some (⟨40,(0),[9,10],[38],1532⟩) from rfl))
private theorem rec3094 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(1),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[651]? = some (⟨40,(1),[9,10],[42,46],3⟩) from rfl))
private theorem rec3095 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(1),[9,10],[38],1532⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[652]? = some (⟨40,(1),[9,10],[38],1532⟩) from rfl))
private theorem rec3099 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(2),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[656]? = some (⟨40,(2),[9,10],[42,46],3⟩) from rfl))
private theorem rec3100 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(2),[9,10],[38],1532⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[657]? = some (⟨40,(2),[9,10],[38],1532⟩) from rfl))
private theorem rec3104 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(3),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[661]? = some (⟨40,(3),[9,10],[42,46],3⟩) from rfl))
private theorem rec3105 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(3),[9,10],[38],1532⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[662]? = some (⟨40,(3),[9,10],[38],1532⟩) from rfl))
private theorem rec3109 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(4),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[666]? = some (⟨40,(4),[9,10],[42,46],3⟩) from rfl))
private theorem rec3110 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(4),[9,10],[38],1532⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[667]? = some (⟨40,(4),[9,10],[38],1532⟩) from rfl))
private theorem rec3114 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(5),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[671]? = some (⟨40,(5),[9,10],[42,46],3⟩) from rfl))
private theorem rec3115 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(5),[9,10],[38],1533⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[672]? = some (⟨40,(5),[9,10],[38],1533⟩) from rfl))
private theorem rec3119 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(6),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[676]? = some (⟨40,(6),[9,10],[42,46],3⟩) from rfl))
private theorem rec3120 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(6),[9,10],[38],1533⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[677]? = some (⟨40,(6),[9,10],[38],1533⟩) from rfl))
private theorem rec3124 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(7),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[681]? = some (⟨40,(7),[9,10],[42,46],3⟩) from rfl))
private theorem rec3125 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(7),[9,10],[38],1533⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[682]? = some (⟨40,(7),[9,10],[38],1533⟩) from rfl))
private theorem rec3129 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(8),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[686]? = some (⟨40,(8),[9,10],[42,46],3⟩) from rfl))
private theorem rec3130 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(8),[9,10],[38],1533⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[687]? = some (⟨40,(8),[9,10],[38],1533⟩) from rfl))
private theorem rec3134 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(9),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[691]? = some (⟨40,(9),[9,10],[42,46],3⟩) from rfl))
private theorem rec3135 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(9),[9,10],[38],1533⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[692]? = some (⟨40,(9),[9,10],[38],1533⟩) from rfl))
private theorem rec3139 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(10),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[696]? = some (⟨40,(10),[9,10],[42,46],3⟩) from rfl))
private theorem rec3140 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(10),[9,10],[38],1534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[697]? = some (⟨40,(10),[9,10],[38],1534⟩) from rfl))
private theorem rec3144 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(11),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[701]? = some (⟨40,(11),[9,10],[42,46],3⟩) from rfl))
private theorem rec3145 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(11),[9,10],[38],1535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[702]? = some (⟨40,(11),[9,10],[38],1535⟩) from rfl))
private theorem rec3149 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(12),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[706]? = some (⟨40,(12),[9,10],[42,46],3⟩) from rfl))
private theorem rec3150 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(12),[9,10],[38],1536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[707]? = some (⟨40,(12),[9,10],[38],1536⟩) from rfl))
private theorem rec3154 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(13),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[711]? = some (⟨40,(13),[9,10],[42,46],3⟩) from rfl))
private theorem rec3155 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(13),[9,10],[38],1535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[712]? = some (⟨40,(13),[9,10],[38],1535⟩) from rfl))
private theorem rec3159 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(14),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[716]? = some (⟨40,(14),[9,10],[42,46],3⟩) from rfl))
private theorem rec3160 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(14),[9,10],[38],1537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[717]? = some (⟨40,(14),[9,10],[38],1537⟩) from rfl))
private theorem rec3164 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(15),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[721]? = some (⟨40,(15),[9,10],[42,46],3⟩) from rfl))
private theorem rec3165 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(15),[9,10],[38],1534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[722]? = some (⟨40,(15),[9,10],[38],1534⟩) from rfl))
private theorem rec3169 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(16),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[726]? = some (⟨40,(16),[9,10],[42,46],3⟩) from rfl))
private theorem rec3170 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(16),[9,10],[38],1538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[727]? = some (⟨40,(16),[9,10],[38],1538⟩) from rfl))
private theorem rec3174 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(17),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[731]? = some (⟨40,(17),[9,10],[42,46],3⟩) from rfl))
private theorem rec3175 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(17),[9,10],[38],1538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[732]? = some (⟨40,(17),[9,10],[38],1538⟩) from rfl))
private theorem rec3179 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(18),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[736]? = some (⟨40,(18),[9,10],[42,46],3⟩) from rfl))
private theorem rec3180 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(18),[9,10],[38],1538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[737]? = some (⟨40,(18),[9,10],[38],1538⟩) from rfl))
private theorem rec3184 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(19),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[741]? = some (⟨40,(19),[9,10],[42,46],3⟩) from rfl))
private theorem rec3185 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(19),[9,10],[38],1538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[742]? = some (⟨40,(19),[9,10],[38],1538⟩) from rfl))
private theorem rec3189 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(20),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[746]? = some (⟨40,(20),[9,10],[42,46],3⟩) from rfl))
private theorem rec3190 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(20),[9,10],[38],1534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[747]? = some (⟨40,(20),[9,10],[38],1534⟩) from rfl))
private theorem rec3194 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(21),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[751]? = some (⟨40,(21),[9,10],[42,46],3⟩) from rfl))
private theorem rec3195 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(21),[9,10],[38],1535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[752]? = some (⟨40,(21),[9,10],[38],1535⟩) from rfl))
private theorem rec3199 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(22),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[756]? = some (⟨40,(22),[9,10],[42,46],3⟩) from rfl))
private theorem rec3200 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(22),[9,10],[38],1536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[757]? = some (⟨40,(22),[9,10],[38],1536⟩) from rfl))
private theorem rec3204 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(23),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[761]? = some (⟨40,(23),[9,10],[42,46],3⟩) from rfl))
private theorem rec3205 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(23),[9,10],[38],1535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[762]? = some (⟨40,(23),[9,10],[38],1535⟩) from rfl))
private theorem rec3209 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 40 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(24),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[766]? = some (⟨40,(24),[9,10],[42,46],3⟩) from rfl))
private theorem rec3210 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 40 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(24),[9,10],[38],1537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[767]? = some (⟨40,(24),[9,10],[38],1537⟩) from rfl))
private theorem rec3469 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(0),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1026]? = some (⟨45,(0),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3473 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(1),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1030]? = some (⟨45,(1),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3477 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(2),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1034]? = some (⟨45,(2),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3481 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(3),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1038]? = some (⟨45,(3),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3485 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(4),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1042]? = some (⟨45,(4),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3489 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(5),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1046]? = some (⟨45,(5),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3493 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(6),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1050]? = some (⟨45,(6),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3497 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(7),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1054]? = some (⟨45,(7),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3501 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(8),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1058]? = some (⟨45,(8),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3505 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(9),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1062]? = some (⟨45,(9),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3509 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(10),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1066]? = some (⟨45,(10),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3513 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(11),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1070]? = some (⟨45,(11),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3517 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(12),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1074]? = some (⟨45,(12),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3521 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(13),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1078]? = some (⟨45,(13),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3525 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(14),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1082]? = some (⟨45,(14),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3529 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(15),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1086]? = some (⟨45,(15),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3533 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(16),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1090]? = some (⟨45,(16),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3537 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(17),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1094]? = some (⟨45,(17),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3541 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(18),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1098]? = some (⟨45,(18),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3545 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(19),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1102]? = some (⟨45,(19),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3549 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(20),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1106]? = some (⟨45,(20),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3553 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(21),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1110]? = some (⟨45,(21),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3557 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(22),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1114]? = some (⟨45,(22),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3561 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(23),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1118]? = some (⟨45,(23),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3565 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 45 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(24),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1122]? = some (⟨45,(24),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec3573 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[9,10],[38,42,46],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1130]? = some (⟨47,(0),[9,10],[38,42,46],189⟩) from rfl))
private theorem rec3583 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[9,10],[38,42,46],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1140]? = some (⟨47,(1),[9,10],[38,42,46],260⟩) from rfl))
private theorem rec3593 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[9,10],[38],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1150]? = some (⟨47,(2),[9,10],[38],191⟩) from rfl))
private theorem rec3594 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[9,10],[42,46],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1151]? = some (⟨47,(2),[9,10],[42,46],261⟩) from rfl))
private theorem rec3604 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[9,10],[38],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1161]? = some (⟨47,(3),[9,10],[38],192⟩) from rfl))
private theorem rec3605 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[9,10],[42,46],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1162]? = some (⟨47,(3),[9,10],[42,46],262⟩) from rfl))
private theorem rec3615 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[9,10],[38],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1172]? = some (⟨47,(4),[9,10],[38],193⟩) from rfl))
private theorem rec3616 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[9,10],[42,46],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1173]? = some (⟨47,(4),[9,10],[42,46],263⟩) from rfl))
private theorem rec3626 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[9,10],[38,42,46],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1183]? = some (⟨47,(5),[9,10],[38,42,46],189⟩) from rfl))
private theorem rec3636 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[9,10],[38,42,46],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1193]? = some (⟨47,(6),[9,10],[38,42,46],260⟩) from rfl))
private theorem rec3650 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[9,10],[38],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[11]? = some (⟨47,(7),[9,10],[38],191⟩) from rfl))
private theorem rec3651 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[9,10],[42],264⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[12]? = some (⟨47,(7),[9,10],[42],264⟩) from rfl))
private theorem rec3652 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[9,10],[46],319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[13]? = some (⟨47,(7),[9,10],[46],319⟩) from rfl))
private theorem rec3667 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[9,10],[38],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[28]? = some (⟨47,(8),[9,10],[38],192⟩) from rfl))
private theorem rec3668 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[9,10],[46],320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[29]? = some (⟨47,(8),[9,10],[46],320⟩) from rfl))
private theorem rec3669 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[10],[42],265⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[30]? = some (⟨47,(8),[10],[42],265⟩) from rfl))
private theorem rec3684 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[9,10],[38],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[45]? = some (⟨47,(9),[9,10],[38],193⟩) from rfl))
private theorem rec3685 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[9,10],[42],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[46]? = some (⟨47,(9),[9,10],[42],266⟩) from rfl))
private theorem rec3686 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[9,10],[46],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[47]? = some (⟨47,(9),[9,10],[46],321⟩) from rfl))
private theorem rec3696 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[9,10],[38,42,46],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[57]? = some (⟨47,(10),[9,10],[38,42,46],194⟩) from rfl))
private theorem rec3706 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[9,10],[38,42,46],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[67]? = some (⟨47,(11),[9,10],[38,42,46],267⟩) from rfl))
private theorem rec3720 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[9,10],[38],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[81]? = some (⟨47,(12),[9,10],[38],195⟩) from rfl))
private theorem rec3721 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[9,10],[42],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[82]? = some (⟨47,(12),[9,10],[42],268⟩) from rfl))
private theorem rec3722 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[9,10],[46],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[83]? = some (⟨47,(12),[9,10],[46],322⟩) from rfl))
private theorem rec3738 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[9,10],[38],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[99]? = some (⟨47,(13),[9,10],[38],195⟩) from rfl))
private theorem rec3739 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[9,10],[46],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[100]? = some (⟨47,(13),[9,10],[46],322⟩) from rfl))
private theorem rec3740 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[10],[42],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[101]? = some (⟨47,(13),[10],[42],268⟩) from rfl))
private theorem rec3754 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[9,10],[38],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[115]? = some (⟨47,(14),[9,10],[38],193⟩) from rfl))
private theorem rec3755 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[9,10],[42],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[116]? = some (⟨47,(14),[9,10],[42],266⟩) from rfl))
private theorem rec3756 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[9,10],[46],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[117]? = some (⟨47,(14),[9,10],[46],321⟩) from rfl))
private theorem rec3766 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[9,10],[38,42,46],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[127]? = some (⟨47,(15),[9,10],[38,42,46],196⟩) from rfl))
private theorem rec3776 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[9,10],[38,42,46],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[137]? = some (⟨47,(16),[9,10],[38,42,46],269⟩) from rfl))
private theorem rec3789 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[9,10],[38],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[150]? = some (⟨47,(17),[9,10],[38],197⟩) from rfl))
private theorem rec3790 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[9,10],[42],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[151]? = some (⟨47,(17),[9,10],[42],270⟩) from rfl))
private theorem rec3791 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[9,10],[46],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[152]? = some (⟨47,(17),[9,10],[46],323⟩) from rfl))
private theorem rec3806 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[9,10],[38],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[167]? = some (⟨47,(18),[9,10],[38],197⟩) from rfl))
private theorem rec3807 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[9,10],[46],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[168]? = some (⟨47,(18),[9,10],[46],323⟩) from rfl))
private theorem rec3808 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[10],[42],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[169]? = some (⟨47,(18),[10],[42],270⟩) from rfl))
private theorem rec3821 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[9,10],[38],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[182]? = some (⟨47,(19),[9,10],[38],197⟩) from rfl))
private theorem rec3822 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[9,10],[42],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[183]? = some (⟨47,(19),[9,10],[42],270⟩) from rfl))
private theorem rec3823 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[9,10],[46],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[184]? = some (⟨47,(19),[9,10],[46],323⟩) from rfl))
private theorem rec3833 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[9,10],[38,42,46],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[194]? = some (⟨47,(20),[9,10],[38,42,46],198⟩) from rfl))
private theorem rec3843 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[9,10],[38,42,46],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[204]? = some (⟨47,(21),[9,10],[38,42,46],271⟩) from rfl))
private theorem rec3856 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[9,10],[38],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[217]? = some (⟨47,(22),[9,10],[38],199⟩) from rfl))
private theorem rec3857 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[9,10],[42],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[218]? = some (⟨47,(22),[9,10],[42],272⟩) from rfl))
private theorem rec3858 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[9,10],[46],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[219]? = some (⟨47,(22),[9,10],[46],324⟩) from rfl))
private theorem rec3873 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[9,10],[38],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[234]? = some (⟨47,(23),[9,10],[38],199⟩) from rfl))
private theorem rec3874 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[9,10],[46],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[235]? = some (⟨47,(23),[9,10],[46],324⟩) from rfl))
private theorem rec3875 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[10],[42],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[236]? = some (⟨47,(23),[10],[42],272⟩) from rfl))
private theorem rec3888 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[9,10],[38],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[249]? = some (⟨47,(24),[9,10],[38],199⟩) from rfl))
private theorem rec3889 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[9,10],[42],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[250]? = some (⟨47,(24),[9,10],[42],272⟩) from rfl))
private theorem rec3890 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[9,10],[46],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[251]? = some (⟨47,(24),[9,10],[46],324⟩) from rfl))
private theorem rec3901 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[9,10],[42],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[262]? = some (⟨50,(0),[9,10],[42],301⟩) from rfl))
private theorem rec3902 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[9,10],[38],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[263]? = some (⟨50,(0),[9,10],[38],331⟩) from rfl))
private theorem rec3903 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[10],[46],1399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[264]? = some (⟨50,(0),[10],[46],1399⟩) from rfl))
private theorem rec3913 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[9,10],[42],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[274]? = some (⟨50,(1),[9,10],[42],302⟩) from rfl))
private theorem rec3914 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[9,10],[38],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[275]? = some (⟨50,(1),[9,10],[38],332⟩) from rfl))
private theorem rec3915 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[10],[46],1400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[276]? = some (⟨50,(1),[10],[46],1400⟩) from rfl))
private theorem rec3925 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[9,10],[42],303⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[286]? = some (⟨50,(2),[9,10],[42],303⟩) from rfl))
private theorem rec3926 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[9,10],[38],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[287]? = some (⟨50,(2),[9,10],[38],333⟩) from rfl))
private theorem rec3927 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[10],[46],1401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[288]? = some (⟨50,(2),[10],[46],1401⟩) from rfl))
private theorem rec3937 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[9,10],[42],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[298]? = some (⟨50,(3),[9,10],[42],304⟩) from rfl))
private theorem rec3938 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[9,10],[38],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[299]? = some (⟨50,(3),[9,10],[38],334⟩) from rfl))
private theorem rec3939 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[10],[46],1402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[300]? = some (⟨50,(3),[10],[46],1402⟩) from rfl))
private theorem rec3949 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[9,10],[42],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[310]? = some (⟨50,(4),[9,10],[42],301⟩) from rfl))
private theorem rec3950 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[9,10],[38],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[311]? = some (⟨50,(4),[9,10],[38],331⟩) from rfl))
private theorem rec3951 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[10],[46],1399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[312]? = some (⟨50,(4),[10],[46],1399⟩) from rfl))
private theorem rec3961 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[9,10],[42],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[322]? = some (⟨50,(5),[9,10],[42],302⟩) from rfl))
private theorem rec3962 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[9,10],[38],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[323]? = some (⟨50,(5),[9,10],[38],332⟩) from rfl))
private theorem rec3963 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[10],[46],1400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[324]? = some (⟨50,(5),[10],[46],1400⟩) from rfl))
private theorem rec3973 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[9,10],[42],305⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[334]? = some (⟨50,(6),[9,10],[42],305⟩) from rfl))
private theorem rec3974 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[9,10],[38],335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[335]? = some (⟨50,(6),[9,10],[38],335⟩) from rfl))
private theorem rec3975 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[10],[46],1403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[336]? = some (⟨50,(6),[10],[46],1403⟩) from rfl))
private theorem rec3985 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[9,10],[42],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[346]? = some (⟨50,(7),[9,10],[42],304⟩) from rfl))
private theorem rec3986 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[9,10],[38],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[347]? = some (⟨50,(7),[9,10],[38],334⟩) from rfl))
private theorem rec3987 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[10],[46],1402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[348]? = some (⟨50,(7),[10],[46],1402⟩) from rfl))
private theorem rec3997 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[9,10],[42],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[358]? = some (⟨50,(8),[9,10],[42],301⟩) from rfl))
private theorem rec3998 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[9,10],[38],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[359]? = some (⟨50,(8),[9,10],[38],331⟩) from rfl))
private theorem rec3999 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[10],[46],1399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[360]? = some (⟨50,(8),[10],[46],1399⟩) from rfl))
private theorem rec4009 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[9,10],[42],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[370]? = some (⟨50,(9),[9,10],[42],302⟩) from rfl))
private theorem rec4010 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[9,10],[38],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[371]? = some (⟨50,(9),[9,10],[38],332⟩) from rfl))
private theorem rec4011 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[10],[46],1400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[372]? = some (⟨50,(9),[10],[46],1400⟩) from rfl))
private theorem rec4021 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[9,10],[42],303⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[382]? = some (⟨50,(10),[9,10],[42],303⟩) from rfl))
private theorem rec4022 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[9,10],[38],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[383]? = some (⟨50,(10),[9,10],[38],333⟩) from rfl))
private theorem rec4023 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[10],[46],1401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[384]? = some (⟨50,(10),[10],[46],1401⟩) from rfl))
private theorem rec4033 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[9,10],[42],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[394]? = some (⟨50,(11),[9,10],[42],304⟩) from rfl))
private theorem rec4034 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[9,10],[38],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[395]? = some (⟨50,(11),[9,10],[38],334⟩) from rfl))
private theorem rec4035 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[10],[46],1402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[396]? = some (⟨50,(11),[10],[46],1402⟩) from rfl))
private theorem rec4045 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[9,10],[42],301⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[406]? = some (⟨50,(12),[9,10],[42],301⟩) from rfl))
private theorem rec4046 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[9,10],[38],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[407]? = some (⟨50,(12),[9,10],[38],331⟩) from rfl))
private theorem rec4047 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[10],[46],1399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[408]? = some (⟨50,(12),[10],[46],1399⟩) from rfl))
private theorem rec4057 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[9,10],[42],302⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[418]? = some (⟨50,(13),[9,10],[42],302⟩) from rfl))
private theorem rec4058 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[9,10],[38],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[419]? = some (⟨50,(13),[9,10],[38],332⟩) from rfl))
private theorem rec4059 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[10],[46],1400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[420]? = some (⟨50,(13),[10],[46],1400⟩) from rfl))
private theorem rec4069 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[9,10],[42],306⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[430]? = some (⟨50,(14),[9,10],[42],306⟩) from rfl))
private theorem rec4070 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[9,10],[38],336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[431]? = some (⟨50,(14),[9,10],[38],336⟩) from rfl))
private theorem rec4071 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[10],[46],1404⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[432]? = some (⟨50,(14),[10],[46],1404⟩) from rfl))
private theorem rec4081 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[9,10],[42],304⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[442]? = some (⟨50,(15),[9,10],[42],304⟩) from rfl))
private theorem rec4082 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[9,10],[38],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[443]? = some (⟨50,(15),[9,10],[38],334⟩) from rfl))
private theorem rec4083 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[10],[46],1402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[444]? = some (⟨50,(15),[10],[46],1402⟩) from rfl))
private theorem rec4096 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[9,10],[42],279⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[457]? = some (⟨53,(0),[9,10],[42],279⟩) from rfl))
private theorem rec4097 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[9,10],[46],325⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[458]? = some (⟨53,(0),[9,10],[46],325⟩) from rfl))
private theorem rec4098 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[9,10],[38],360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[459]? = some (⟨53,(0),[9,10],[38],360⟩) from rfl))
private theorem rec4112 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[9,10],[42],280⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[473]? = some (⟨53,(1),[9,10],[42],280⟩) from rfl))
private theorem rec4113 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[9,10],[46],326⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[474]? = some (⟨53,(1),[9,10],[46],326⟩) from rfl))
private theorem rec4114 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[9,10],[38],361⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[475]? = some (⟨53,(1),[9,10],[38],361⟩) from rfl))
private theorem rec4127 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[9,10],[42],281⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[488]? = some (⟨53,(2),[9,10],[42],281⟩) from rfl))
private theorem rec4128 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[9,10],[46],327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[489]? = some (⟨53,(2),[9,10],[46],327⟩) from rfl))
private theorem rec4129 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[9,10],[38],362⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[490]? = some (⟨53,(2),[9,10],[38],362⟩) from rfl))
private theorem rec4143 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[9,10],[42],282⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[504]? = some (⟨53,(3),[9,10],[42],282⟩) from rfl))
private theorem rec4144 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[9,10],[46],328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[505]? = some (⟨53,(3),[9,10],[46],328⟩) from rfl))
private theorem rec4145 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[9,10],[38],363⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[506]? = some (⟨53,(3),[9,10],[38],363⟩) from rfl))
private theorem rec4156 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(0),[10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[7]? = some (⟨55,(0),[10],[38],2⟩) from rfl))
private theorem rec4157 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(0),[10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[8]? = some (⟨55,(0),[10],[42,46],3⟩) from rfl))
private theorem rec4163 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(1),[9,10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[14]? = some (⟨55,(1),[9,10],[38],2⟩) from rfl))
private theorem rec4164 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(1),[10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[15]? = some (⟨55,(1),[10],[42,46],3⟩) from rfl))
private theorem rec4171 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 55 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(2),[9,10],[42],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[22]? = some (⟨55,(2),[9,10],[42],2⟩) from rfl))
private theorem rec4172 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(2),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[23]? = some (⟨55,(2),[9,10],[38],3⟩) from rfl))
private theorem rec4173 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(2),[10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[24]? = some (⟨55,(2),[10],[46],2⟩) from rfl))
private theorem rec4181 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(3),[9,10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[32]? = some (⟨55,(3),[9,10],[46],2⟩) from rfl))
private theorem rec4182 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(3),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[33]? = some (⟨55,(3),[9,10],[38],3⟩) from rfl))
private theorem rec4183 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 55 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(3),[10],[42],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[34]? = some (⟨55,(3),[10],[42],2⟩) from rfl))
private theorem rec4191 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(4),[10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[42]? = some (⟨55,(4),[10],[38],2⟩) from rfl))
private theorem rec4192 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(4),[10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[43]? = some (⟨55,(4),[10],[42,46],3⟩) from rfl))
private theorem rec4198 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(5),[9,10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[49]? = some (⟨55,(5),[9,10],[38],2⟩) from rfl))
private theorem rec4199 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(5),[10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[50]? = some (⟨55,(5),[10],[42,46],3⟩) from rfl))
private theorem rec4206 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 55 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(6),[9,10],[42],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[57]? = some (⟨55,(6),[9,10],[42],2⟩) from rfl))
private theorem rec4207 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(6),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[58]? = some (⟨55,(6),[9,10],[38],3⟩) from rfl))
private theorem rec4208 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(6),[10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[59]? = some (⟨55,(6),[10],[46],2⟩) from rfl))
private theorem rec4216 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(7),[9,10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[67]? = some (⟨55,(7),[9,10],[46],2⟩) from rfl))
private theorem rec4217 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(7),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[68]? = some (⟨55,(7),[9,10],[38],3⟩) from rfl))
private theorem rec4218 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 55 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(7),[10],[42],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[69]? = some (⟨55,(7),[10],[42],2⟩) from rfl))
private theorem rec4224 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(8),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[75]? = some (⟨55,(8),[9,10],[42,46],3⟩) from rfl))
private theorem rec4225 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(8),[9,10],[38],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[76]? = some (⟨55,(8),[9,10],[38],98⟩) from rfl))
private theorem rec4229 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(9),[9,10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[80]? = some (⟨55,(9),[9,10],[42,46],3⟩) from rfl))
private theorem rec4230 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(9),[9,10],[38],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[81]? = some (⟨55,(9),[9,10],[38],159⟩) from rfl))
private theorem rec4235 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(10),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[86]? = some (⟨55,(10),[9,10],[38],3⟩) from rfl))
private theorem rec4236 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(10),[9,10],[46],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[87]? = some (⟨55,(10),[9,10],[46],29⟩) from rfl))
private theorem rec4237 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 55 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(10),[9,10],[42],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[88]? = some (⟨55,(10),[9,10],[42],97⟩) from rfl))
private theorem rec4242 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(11),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[93]? = some (⟨55,(11),[9,10],[38],3⟩) from rfl))
private theorem rec4243 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 55 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(11),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[94]? = some (⟨55,(11),[9,10],[42],29⟩) from rfl))
private theorem rec4244 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(11),[9,10],[46],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[95]? = some (⟨55,(11),[9,10],[46],234⟩) from rfl))
private theorem rec4252 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(12),[10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[103]? = some (⟨55,(12),[10],[42,46],3⟩) from rfl))
private theorem rec4253 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(12),[10],[38],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[104]? = some (⟨55,(12),[10],[38],99⟩) from rfl))
private theorem rec4260 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(13),[9,10],[38],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[111]? = some (⟨55,(13),[9,10],[38],99⟩) from rfl))
private theorem rec4261 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(13),[10],[42,46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[112]? = some (⟨55,(13),[10],[42,46],3⟩) from rfl))
private theorem rec4266 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(14),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[117]? = some (⟨55,(14),[9,10],[38],3⟩) from rfl))
private theorem rec4267 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(14),[9,10],[46],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[118]? = some (⟨55,(14),[9,10],[46],29⟩) from rfl))
private theorem rec4268 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 55 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(14),[9,10],[42],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[119]? = some (⟨55,(14),[9,10],[42],99⟩) from rfl))
private theorem rec4274 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 55 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(15),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[125]? = some (⟨55,(15),[9,10],[38],3⟩) from rfl))
private theorem rec4275 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 55 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(15),[9,10],[42],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[126]? = some (⟨55,(15),[9,10],[42],29⟩) from rfl))
private theorem rec4276 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 55 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(15),[9,10],[46],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[127]? = some (⟨55,(15),[9,10],[46],99⟩) from rfl))
private theorem rec4282 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(0),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[133]? = some (⟨57,(0),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4288 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(1),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[139]? = some (⟨57,(1),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4298 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[9,10],[42],311⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[149]? = some (⟨57,(2),[9,10],[42],311⟩) from rfl))
private theorem rec4299 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[9,10],[38],337⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[150]? = some (⟨57,(2),[9,10],[38],337⟩) from rfl))
private theorem rec4300 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[10],[46],1405⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[151]? = some (⟨57,(2),[10],[46],1405⟩) from rfl))
private theorem rec4306 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(3),[9,10],[38,42,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[157]? = some (⟨57,(3),[9,10],[38,42,46],101⟩) from rfl))
private theorem rec4312 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(4),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[163]? = some (⟨57,(4),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4318 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(5),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[169]? = some (⟨57,(5),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4329 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[9,10],[42],284⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[180]? = some (⟨57,(6),[9,10],[42],284⟩) from rfl))
private theorem rec4330 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[9,10],[38],338⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[181]? = some (⟨57,(6),[9,10],[38],338⟩) from rfl))
private theorem rec4331 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[10],[46],1406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[182]? = some (⟨57,(6),[10],[46],1406⟩) from rfl))
private theorem rec4337 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(7),[9,10],[38,42,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[188]? = some (⟨57,(7),[9,10],[38,42,46],101⟩) from rfl))
private theorem rec4343 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(8),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[194]? = some (⟨57,(8),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4349 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(9),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[200]? = some (⟨57,(9),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4360 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[9,10],[42],285⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[211]? = some (⟨57,(10),[9,10],[42],285⟩) from rfl))
private theorem rec4361 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[9,10],[38],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[212]? = some (⟨57,(10),[9,10],[38],339⟩) from rfl))
private theorem rec4362 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[10],[46],1680⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[213]? = some (⟨57,(10),[10],[46],1680⟩) from rfl))
private theorem rec4368 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(11),[9,10],[38,42,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[219]? = some (⟨57,(11),[9,10],[38,42,46],101⟩) from rfl))
private theorem rec4374 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(12),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[225]? = some (⟨57,(12),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4380 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(13),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[231]? = some (⟨57,(13),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4386 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(14),[9,10],[38,42,46],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[237]? = some (⟨57,(14),[9,10],[38,42,46],286⟩) from rfl))
private theorem rec4392 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(15),[9,10],[38,42,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[243]? = some (⟨57,(15),[9,10],[38,42,46],101⟩) from rfl))
private theorem rec4398 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(16),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[249]? = some (⟨57,(16),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4404 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(17),[9,10],[38,42,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[255]? = some (⟨57,(17),[9,10],[38,42,46],2⟩) from rfl))
private theorem rec4410 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(18),[9,10],[38,42,46],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[261]? = some (⟨57,(18),[9,10],[38,42,46],287⟩) from rfl))
private theorem rec4416 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 42, 46] : List ℕ)) : section14Recorded section14Catalog si parent 57 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(19),[9,10],[38,42,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[267]? = some (⟨57,(19),[9,10],[38,42,46],101⟩) from rfl))
private theorem rec16294 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(0),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[86]? = some (⟨552,(0),[9,10],[38],3⟩) from rfl))
private theorem rec16295 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(0),[9,10],[42],1657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[87]? = some (⟨552,(0),[9,10],[42],1657⟩) from rfl))
private theorem rec16296 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(0),[9,10],[46],1660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[88]? = some (⟨552,(0),[9,10],[46],1660⟩) from rfl))
private theorem rec16301 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(1),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[93]? = some (⟨552,(1),[9,10],[38],3⟩) from rfl))
private theorem rec16302 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(1),[9,10],[42],1658⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[94]? = some (⟨552,(1),[9,10],[42],1658⟩) from rfl))
private theorem rec16303 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(1),[9,10],[46],1661⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[95]? = some (⟨552,(1),[9,10],[46],1661⟩) from rfl))
private theorem rec16308 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(2),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[100]? = some (⟨552,(2),[9,10],[38],3⟩) from rfl))
private theorem rec16309 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(2),[9,10],[42],1657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[101]? = some (⟨552,(2),[9,10],[42],1657⟩) from rfl))
private theorem rec16310 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(2),[9,10],[46],1660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[102]? = some (⟨552,(2),[9,10],[46],1660⟩) from rfl))
private theorem rec16315 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(3),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[107]? = some (⟨552,(3),[9,10],[38],3⟩) from rfl))
private theorem rec16316 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(3),[9,10],[42],1659⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[108]? = some (⟨552,(3),[9,10],[42],1659⟩) from rfl))
private theorem rec16317 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(3),[9,10],[46],1662⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[109]? = some (⟨552,(3),[9,10],[46],1662⟩) from rfl))
private theorem rec16322 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(4),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[114]? = some (⟨552,(4),[9,10],[38],3⟩) from rfl))
private theorem rec16323 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(4),[9,10],[42],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[115]? = some (⟨552,(4),[9,10],[42],256⟩) from rfl))
private theorem rec16324 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(4),[9,10],[46],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[116]? = some (⟨552,(4),[9,10],[46],315⟩) from rfl))
private theorem rec16329 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(5),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[121]? = some (⟨552,(5),[9,10],[38],3⟩) from rfl))
private theorem rec16330 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(5),[9,10],[42],1657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[122]? = some (⟨552,(5),[9,10],[42],1657⟩) from rfl))
private theorem rec16331 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(5),[9,10],[46],1660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[123]? = some (⟨552,(5),[9,10],[46],1660⟩) from rfl))
private theorem rec16336 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(6),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[128]? = some (⟨552,(6),[9,10],[38],3⟩) from rfl))
private theorem rec16337 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(6),[9,10],[42],1658⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[129]? = some (⟨552,(6),[9,10],[42],1658⟩) from rfl))
private theorem rec16338 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(6),[9,10],[46],1661⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[130]? = some (⟨552,(6),[9,10],[46],1661⟩) from rfl))
private theorem rec16343 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(7),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[135]? = some (⟨552,(7),[9,10],[38],3⟩) from rfl))
private theorem rec16344 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(7),[9,10],[42],1657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[136]? = some (⟨552,(7),[9,10],[42],1657⟩) from rfl))
private theorem rec16345 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(7),[9,10],[46],1660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[137]? = some (⟨552,(7),[9,10],[46],1660⟩) from rfl))
private theorem rec16350 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(8),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[142]? = some (⟨552,(8),[9,10],[38],3⟩) from rfl))
private theorem rec16351 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(8),[9,10],[42],1659⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[143]? = some (⟨552,(8),[9,10],[42],1659⟩) from rfl))
private theorem rec16352 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(8),[9,10],[46],1662⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[144]? = some (⟨552,(8),[9,10],[46],1662⟩) from rfl))
private theorem rec16357 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 552 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(9),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[149]? = some (⟨552,(9),[9,10],[38],3⟩) from rfl))
private theorem rec16358 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 552 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(9),[9,10],[42],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[150]? = some (⟨552,(9),[9,10],[42],256⟩) from rfl))
private theorem rec16359 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 552 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨552,(9),[9,10],[46],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[151]? = some (⟨552,(9),[9,10],[46],315⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 32).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 10).plans.drop 2).take 1 = [⟨3,38,[([1],[]),([2],[]),([3],[1])],false,[(551,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(552,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(553,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(554,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(56,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(555,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec3066 10 32 (by decide) (by decide)
  · left
    exact rec3066 10 33 (by decide) (by decide)
  · left
    exact rec3073 10 34 (by decide) (by decide)
  · left
    exact rec3074 10 35 (by decide) (by decide)
  · left
    exact rec3066 10 36 (by decide) (by decide)
  · left
    exact rec3066 10 37 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(551,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(552,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(553,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(554,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(56,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(555,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 551)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 40)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3090 10 38 (by decide) (by decide)
      · right
        exact rec3095 10 38 (by decide) (by decide)
      · right
        exact rec3100 10 38 (by decide) (by decide)
      · right
        exact rec3105 10 38 (by decide) (by decide)
      · right
        exact rec3110 10 38 (by decide) (by decide)
      · right
        exact rec3115 10 38 (by decide) (by decide)
      · right
        exact rec3120 10 38 (by decide) (by decide)
      · right
        exact rec3125 10 38 (by decide) (by decide)
      · right
        exact rec3130 10 38 (by decide) (by decide)
      · right
        exact rec3135 10 38 (by decide) (by decide)
      · right
        exact rec3140 10 38 (by decide) (by decide)
      · right
        exact rec3145 10 38 (by decide) (by decide)
      · right
        exact rec3150 10 38 (by decide) (by decide)
      · right
        exact rec3155 10 38 (by decide) (by decide)
      · right
        exact rec3160 10 38 (by decide) (by decide)
      · right
        exact rec3165 10 38 (by decide) (by decide)
      · right
        exact rec3170 10 38 (by decide) (by decide)
      · right
        exact rec3175 10 38 (by decide) (by decide)
      · right
        exact rec3180 10 38 (by decide) (by decide)
      · right
        exact rec3185 10 38 (by decide) (by decide)
      · right
        exact rec3190 10 38 (by decide) (by decide)
      · right
        exact rec3195 10 38 (by decide) (by decide)
      · right
        exact rec3200 10 38 (by decide) (by decide)
      · right
        exact rec3205 10 38 (by decide) (by decide)
      · right
        exact rec3210 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 41)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 552)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16294 10 38 (by decide) (by decide)
      · right
        exact rec16301 10 38 (by decide) (by decide)
      · right
        exact rec16308 10 38 (by decide) (by decide)
      · right
        exact rec16315 10 38 (by decide) (by decide)
      · right
        exact rec16322 10 38 (by decide) (by decide)
      · right
        exact rec16329 10 38 (by decide) (by decide)
      · right
        exact rec16336 10 38 (by decide) (by decide)
      · right
        exact rec16343 10 38 (by decide) (by decide)
      · right
        exact rec16350 10 38 (by decide) (by decide)
      · right
        exact rec16357 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 553)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 44)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 45)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3469 10 38 (by decide) (by decide)
      · right
        exact rec3473 10 38 (by decide) (by decide)
      · right
        exact rec3477 10 38 (by decide) (by decide)
      · right
        exact rec3481 10 38 (by decide) (by decide)
      · right
        exact rec3485 10 38 (by decide) (by decide)
      · right
        exact rec3489 10 38 (by decide) (by decide)
      · right
        exact rec3493 10 38 (by decide) (by decide)
      · right
        exact rec3497 10 38 (by decide) (by decide)
      · right
        exact rec3501 10 38 (by decide) (by decide)
      · right
        exact rec3505 10 38 (by decide) (by decide)
      · right
        exact rec3509 10 38 (by decide) (by decide)
      · right
        exact rec3513 10 38 (by decide) (by decide)
      · right
        exact rec3517 10 38 (by decide) (by decide)
      · right
        exact rec3521 10 38 (by decide) (by decide)
      · right
        exact rec3525 10 38 (by decide) (by decide)
      · right
        exact rec3529 10 38 (by decide) (by decide)
      · right
        exact rec3533 10 38 (by decide) (by decide)
      · right
        exact rec3537 10 38 (by decide) (by decide)
      · right
        exact rec3541 10 38 (by decide) (by decide)
      · right
        exact rec3545 10 38 (by decide) (by decide)
      · right
        exact rec3549 10 38 (by decide) (by decide)
      · right
        exact rec3553 10 38 (by decide) (by decide)
      · right
        exact rec3557 10 38 (by decide) (by decide)
      · right
        exact rec3561 10 38 (by decide) (by decide)
      · right
        exact rec3565 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 46)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 47)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3573 10 38 (by decide) (by decide)
      · right
        exact rec3583 10 38 (by decide) (by decide)
      · right
        exact rec3593 10 38 (by decide) (by decide)
      · right
        exact rec3604 10 38 (by decide) (by decide)
      · right
        exact rec3615 10 38 (by decide) (by decide)
      · right
        exact rec3626 10 38 (by decide) (by decide)
      · right
        exact rec3636 10 38 (by decide) (by decide)
      · right
        exact rec3650 10 38 (by decide) (by decide)
      · right
        exact rec3667 10 38 (by decide) (by decide)
      · right
        exact rec3684 10 38 (by decide) (by decide)
      · right
        exact rec3696 10 38 (by decide) (by decide)
      · right
        exact rec3706 10 38 (by decide) (by decide)
      · right
        exact rec3720 10 38 (by decide) (by decide)
      · right
        exact rec3738 10 38 (by decide) (by decide)
      · right
        exact rec3754 10 38 (by decide) (by decide)
      · right
        exact rec3766 10 38 (by decide) (by decide)
      · right
        exact rec3776 10 38 (by decide) (by decide)
      · right
        exact rec3789 10 38 (by decide) (by decide)
      · right
        exact rec3806 10 38 (by decide) (by decide)
      · right
        exact rec3821 10 38 (by decide) (by decide)
      · right
        exact rec3833 10 38 (by decide) (by decide)
      · right
        exact rec3843 10 38 (by decide) (by decide)
      · right
        exact rec3856 10 38 (by decide) (by decide)
      · right
        exact rec3873 10 38 (by decide) (by decide)
      · right
        exact rec3888 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 48)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 49)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 50)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3902 10 38 (by decide) (by decide)
      · right
        exact rec3914 10 38 (by decide) (by decide)
      · right
        exact rec3926 10 38 (by decide) (by decide)
      · right
        exact rec3938 10 38 (by decide) (by decide)
      · right
        exact rec3950 10 38 (by decide) (by decide)
      · right
        exact rec3962 10 38 (by decide) (by decide)
      · right
        exact rec3974 10 38 (by decide) (by decide)
      · right
        exact rec3986 10 38 (by decide) (by decide)
      · right
        exact rec3998 10 38 (by decide) (by decide)
      · right
        exact rec4010 10 38 (by decide) (by decide)
      · right
        exact rec4022 10 38 (by decide) (by decide)
      · right
        exact rec4034 10 38 (by decide) (by decide)
      · right
        exact rec4046 10 38 (by decide) (by decide)
      · right
        exact rec4058 10 38 (by decide) (by decide)
      · right
        exact rec4070 10 38 (by decide) (by decide)
      · right
        exact rec4082 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 51)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 52)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 53)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4098 10 38 (by decide) (by decide)
      · right
        exact rec4114 10 38 (by decide) (by decide)
      · right
        exact rec4129 10 38 (by decide) (by decide)
      · right
        exact rec4145 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 554)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 55)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4156 10 38 (by decide) (by decide)
      · right
        exact rec4163 10 38 (by decide) (by decide)
      · right
        exact rec4172 10 38 (by decide) (by decide)
      · right
        exact rec4182 10 38 (by decide) (by decide)
      · right
        exact rec4191 10 38 (by decide) (by decide)
      · right
        exact rec4198 10 38 (by decide) (by decide)
      · right
        exact rec4207 10 38 (by decide) (by decide)
      · right
        exact rec4217 10 38 (by decide) (by decide)
      · right
        exact rec4225 10 38 (by decide) (by decide)
      · right
        exact rec4230 10 38 (by decide) (by decide)
      · right
        exact rec4235 10 38 (by decide) (by decide)
      · right
        exact rec4242 10 38 (by decide) (by decide)
      · right
        exact rec4253 10 38 (by decide) (by decide)
      · right
        exact rec4260 10 38 (by decide) (by decide)
      · right
        exact rec4266 10 38 (by decide) (by decide)
      · right
        exact rec4274 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 56)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 57)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4282 10 38 (by decide) (by decide)
      · right
        exact rec4288 10 38 (by decide) (by decide)
      · right
        exact rec4299 10 38 (by decide) (by decide)
      · right
        exact rec4306 10 38 (by decide) (by decide)
      · right
        exact rec4312 10 38 (by decide) (by decide)
      · right
        exact rec4318 10 38 (by decide) (by decide)
      · right
        exact rec4330 10 38 (by decide) (by decide)
      · right
        exact rec4337 10 38 (by decide) (by decide)
      · right
        exact rec4343 10 38 (by decide) (by decide)
      · right
        exact rec4349 10 38 (by decide) (by decide)
      · right
        exact rec4361 10 38 (by decide) (by decide)
      · right
        exact rec4368 10 38 (by decide) (by decide)
      · right
        exact rec4374 10 38 (by decide) (by decide)
      · right
        exact rec4380 10 38 (by decide) (by decide)
      · right
        exact rec4386 10 38 (by decide) (by decide)
      · right
        exact rec4392 10 38 (by decide) (by decide)
      · right
        exact rec4398 10 38 (by decide) (by decide)
      · right
        exact rec4404 10 38 (by decide) (by decide)
      · right
        exact rec4410 10 38 (by decide) (by decide)
      · right
        exact rec4416 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 555)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 59)).length = 10 := by decide +kernel
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
    exact rec3074 10 39 (by decide) (by decide)
  · left
    exact rec3066 10 40 (by decide) (by decide)
  · left
    exact rec3066 10 41 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(551,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(552,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(553,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(554,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(56,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(555,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 551)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 40)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3089 10 42 (by decide) (by decide)
      · right
        exact rec3094 10 42 (by decide) (by decide)
      · right
        exact rec3099 10 42 (by decide) (by decide)
      · right
        exact rec3104 10 42 (by decide) (by decide)
      · right
        exact rec3109 10 42 (by decide) (by decide)
      · right
        exact rec3114 10 42 (by decide) (by decide)
      · right
        exact rec3119 10 42 (by decide) (by decide)
      · right
        exact rec3124 10 42 (by decide) (by decide)
      · right
        exact rec3129 10 42 (by decide) (by decide)
      · right
        exact rec3134 10 42 (by decide) (by decide)
      · right
        exact rec3139 10 42 (by decide) (by decide)
      · right
        exact rec3144 10 42 (by decide) (by decide)
      · right
        exact rec3149 10 42 (by decide) (by decide)
      · right
        exact rec3154 10 42 (by decide) (by decide)
      · right
        exact rec3159 10 42 (by decide) (by decide)
      · right
        exact rec3164 10 42 (by decide) (by decide)
      · right
        exact rec3169 10 42 (by decide) (by decide)
      · right
        exact rec3174 10 42 (by decide) (by decide)
      · right
        exact rec3179 10 42 (by decide) (by decide)
      · right
        exact rec3184 10 42 (by decide) (by decide)
      · right
        exact rec3189 10 42 (by decide) (by decide)
      · right
        exact rec3194 10 42 (by decide) (by decide)
      · right
        exact rec3199 10 42 (by decide) (by decide)
      · right
        exact rec3204 10 42 (by decide) (by decide)
      · right
        exact rec3209 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 41)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 552)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16295 10 42 (by decide) (by decide)
      · right
        exact rec16302 10 42 (by decide) (by decide)
      · right
        exact rec16309 10 42 (by decide) (by decide)
      · right
        exact rec16316 10 42 (by decide) (by decide)
      · right
        exact rec16323 10 42 (by decide) (by decide)
      · right
        exact rec16330 10 42 (by decide) (by decide)
      · right
        exact rec16337 10 42 (by decide) (by decide)
      · right
        exact rec16344 10 42 (by decide) (by decide)
      · right
        exact rec16351 10 42 (by decide) (by decide)
      · right
        exact rec16358 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 553)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 44)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 45)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3469 10 42 (by decide) (by decide)
      · right
        exact rec3473 10 42 (by decide) (by decide)
      · right
        exact rec3477 10 42 (by decide) (by decide)
      · right
        exact rec3481 10 42 (by decide) (by decide)
      · right
        exact rec3485 10 42 (by decide) (by decide)
      · right
        exact rec3489 10 42 (by decide) (by decide)
      · right
        exact rec3493 10 42 (by decide) (by decide)
      · right
        exact rec3497 10 42 (by decide) (by decide)
      · right
        exact rec3501 10 42 (by decide) (by decide)
      · right
        exact rec3505 10 42 (by decide) (by decide)
      · right
        exact rec3509 10 42 (by decide) (by decide)
      · right
        exact rec3513 10 42 (by decide) (by decide)
      · right
        exact rec3517 10 42 (by decide) (by decide)
      · right
        exact rec3521 10 42 (by decide) (by decide)
      · right
        exact rec3525 10 42 (by decide) (by decide)
      · right
        exact rec3529 10 42 (by decide) (by decide)
      · right
        exact rec3533 10 42 (by decide) (by decide)
      · right
        exact rec3537 10 42 (by decide) (by decide)
      · right
        exact rec3541 10 42 (by decide) (by decide)
      · right
        exact rec3545 10 42 (by decide) (by decide)
      · right
        exact rec3549 10 42 (by decide) (by decide)
      · right
        exact rec3553 10 42 (by decide) (by decide)
      · right
        exact rec3557 10 42 (by decide) (by decide)
      · right
        exact rec3561 10 42 (by decide) (by decide)
      · right
        exact rec3565 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 46)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 47)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3573 10 42 (by decide) (by decide)
      · right
        exact rec3583 10 42 (by decide) (by decide)
      · right
        exact rec3594 10 42 (by decide) (by decide)
      · right
        exact rec3605 10 42 (by decide) (by decide)
      · right
        exact rec3616 10 42 (by decide) (by decide)
      · right
        exact rec3626 10 42 (by decide) (by decide)
      · right
        exact rec3636 10 42 (by decide) (by decide)
      · right
        exact rec3651 10 42 (by decide) (by decide)
      · right
        exact rec3669 10 42 (by decide) (by decide)
      · right
        exact rec3685 10 42 (by decide) (by decide)
      · right
        exact rec3696 10 42 (by decide) (by decide)
      · right
        exact rec3706 10 42 (by decide) (by decide)
      · right
        exact rec3721 10 42 (by decide) (by decide)
      · right
        exact rec3740 10 42 (by decide) (by decide)
      · right
        exact rec3755 10 42 (by decide) (by decide)
      · right
        exact rec3766 10 42 (by decide) (by decide)
      · right
        exact rec3776 10 42 (by decide) (by decide)
      · right
        exact rec3790 10 42 (by decide) (by decide)
      · right
        exact rec3808 10 42 (by decide) (by decide)
      · right
        exact rec3822 10 42 (by decide) (by decide)
      · right
        exact rec3833 10 42 (by decide) (by decide)
      · right
        exact rec3843 10 42 (by decide) (by decide)
      · right
        exact rec3857 10 42 (by decide) (by decide)
      · right
        exact rec3875 10 42 (by decide) (by decide)
      · right
        exact rec3889 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 48)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 49)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 50)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3901 10 42 (by decide) (by decide)
      · right
        exact rec3913 10 42 (by decide) (by decide)
      · right
        exact rec3925 10 42 (by decide) (by decide)
      · right
        exact rec3937 10 42 (by decide) (by decide)
      · right
        exact rec3949 10 42 (by decide) (by decide)
      · right
        exact rec3961 10 42 (by decide) (by decide)
      · right
        exact rec3973 10 42 (by decide) (by decide)
      · right
        exact rec3985 10 42 (by decide) (by decide)
      · right
        exact rec3997 10 42 (by decide) (by decide)
      · right
        exact rec4009 10 42 (by decide) (by decide)
      · right
        exact rec4021 10 42 (by decide) (by decide)
      · right
        exact rec4033 10 42 (by decide) (by decide)
      · right
        exact rec4045 10 42 (by decide) (by decide)
      · right
        exact rec4057 10 42 (by decide) (by decide)
      · right
        exact rec4069 10 42 (by decide) (by decide)
      · right
        exact rec4081 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 51)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 52)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 53)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4096 10 42 (by decide) (by decide)
      · right
        exact rec4112 10 42 (by decide) (by decide)
      · right
        exact rec4127 10 42 (by decide) (by decide)
      · right
        exact rec4143 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 554)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 55)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4157 10 42 (by decide) (by decide)
      · right
        exact rec4164 10 42 (by decide) (by decide)
      · right
        exact rec4171 10 42 (by decide) (by decide)
      · right
        exact rec4183 10 42 (by decide) (by decide)
      · right
        exact rec4192 10 42 (by decide) (by decide)
      · right
        exact rec4199 10 42 (by decide) (by decide)
      · right
        exact rec4206 10 42 (by decide) (by decide)
      · right
        exact rec4218 10 42 (by decide) (by decide)
      · right
        exact rec4224 10 42 (by decide) (by decide)
      · right
        exact rec4229 10 42 (by decide) (by decide)
      · right
        exact rec4237 10 42 (by decide) (by decide)
      · right
        exact rec4243 10 42 (by decide) (by decide)
      · right
        exact rec4252 10 42 (by decide) (by decide)
      · right
        exact rec4261 10 42 (by decide) (by decide)
      · right
        exact rec4268 10 42 (by decide) (by decide)
      · right
        exact rec4275 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 56)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 57)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4282 10 42 (by decide) (by decide)
      · right
        exact rec4288 10 42 (by decide) (by decide)
      · right
        exact rec4298 10 42 (by decide) (by decide)
      · right
        exact rec4306 10 42 (by decide) (by decide)
      · right
        exact rec4312 10 42 (by decide) (by decide)
      · right
        exact rec4318 10 42 (by decide) (by decide)
      · right
        exact rec4329 10 42 (by decide) (by decide)
      · right
        exact rec4337 10 42 (by decide) (by decide)
      · right
        exact rec4343 10 42 (by decide) (by decide)
      · right
        exact rec4349 10 42 (by decide) (by decide)
      · right
        exact rec4360 10 42 (by decide) (by decide)
      · right
        exact rec4368 10 42 (by decide) (by decide)
      · right
        exact rec4374 10 42 (by decide) (by decide)
      · right
        exact rec4380 10 42 (by decide) (by decide)
      · right
        exact rec4386 10 42 (by decide) (by decide)
      · right
        exact rec4392 10 42 (by decide) (by decide)
      · right
        exact rec4398 10 42 (by decide) (by decide)
      · right
        exact rec4404 10 42 (by decide) (by decide)
      · right
        exact rec4410 10 42 (by decide) (by decide)
      · right
        exact rec4416 10 42 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 555)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 59)).length = 10 := by decide +kernel
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
    exact rec3070 10 43 (by decide) (by decide)
  · left
    exact rec3066 10 44 (by decide) (by decide)
  · left
    exact rec3066 10 45 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(551,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(552,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(553,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(554,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(56,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(555,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 551)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 40)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3089 10 46 (by decide) (by decide)
      · right
        exact rec3094 10 46 (by decide) (by decide)
      · right
        exact rec3099 10 46 (by decide) (by decide)
      · right
        exact rec3104 10 46 (by decide) (by decide)
      · right
        exact rec3109 10 46 (by decide) (by decide)
      · right
        exact rec3114 10 46 (by decide) (by decide)
      · right
        exact rec3119 10 46 (by decide) (by decide)
      · right
        exact rec3124 10 46 (by decide) (by decide)
      · right
        exact rec3129 10 46 (by decide) (by decide)
      · right
        exact rec3134 10 46 (by decide) (by decide)
      · right
        exact rec3139 10 46 (by decide) (by decide)
      · right
        exact rec3144 10 46 (by decide) (by decide)
      · right
        exact rec3149 10 46 (by decide) (by decide)
      · right
        exact rec3154 10 46 (by decide) (by decide)
      · right
        exact rec3159 10 46 (by decide) (by decide)
      · right
        exact rec3164 10 46 (by decide) (by decide)
      · right
        exact rec3169 10 46 (by decide) (by decide)
      · right
        exact rec3174 10 46 (by decide) (by decide)
      · right
        exact rec3179 10 46 (by decide) (by decide)
      · right
        exact rec3184 10 46 (by decide) (by decide)
      · right
        exact rec3189 10 46 (by decide) (by decide)
      · right
        exact rec3194 10 46 (by decide) (by decide)
      · right
        exact rec3199 10 46 (by decide) (by decide)
      · right
        exact rec3204 10 46 (by decide) (by decide)
      · right
        exact rec3209 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 41)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 552)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16296 10 46 (by decide) (by decide)
      · right
        exact rec16303 10 46 (by decide) (by decide)
      · right
        exact rec16310 10 46 (by decide) (by decide)
      · right
        exact rec16317 10 46 (by decide) (by decide)
      · right
        exact rec16324 10 46 (by decide) (by decide)
      · right
        exact rec16331 10 46 (by decide) (by decide)
      · right
        exact rec16338 10 46 (by decide) (by decide)
      · right
        exact rec16345 10 46 (by decide) (by decide)
      · right
        exact rec16352 10 46 (by decide) (by decide)
      · right
        exact rec16359 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 553)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 44)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 45)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3469 10 46 (by decide) (by decide)
      · right
        exact rec3473 10 46 (by decide) (by decide)
      · right
        exact rec3477 10 46 (by decide) (by decide)
      · right
        exact rec3481 10 46 (by decide) (by decide)
      · right
        exact rec3485 10 46 (by decide) (by decide)
      · right
        exact rec3489 10 46 (by decide) (by decide)
      · right
        exact rec3493 10 46 (by decide) (by decide)
      · right
        exact rec3497 10 46 (by decide) (by decide)
      · right
        exact rec3501 10 46 (by decide) (by decide)
      · right
        exact rec3505 10 46 (by decide) (by decide)
      · right
        exact rec3509 10 46 (by decide) (by decide)
      · right
        exact rec3513 10 46 (by decide) (by decide)
      · right
        exact rec3517 10 46 (by decide) (by decide)
      · right
        exact rec3521 10 46 (by decide) (by decide)
      · right
        exact rec3525 10 46 (by decide) (by decide)
      · right
        exact rec3529 10 46 (by decide) (by decide)
      · right
        exact rec3533 10 46 (by decide) (by decide)
      · right
        exact rec3537 10 46 (by decide) (by decide)
      · right
        exact rec3541 10 46 (by decide) (by decide)
      · right
        exact rec3545 10 46 (by decide) (by decide)
      · right
        exact rec3549 10 46 (by decide) (by decide)
      · right
        exact rec3553 10 46 (by decide) (by decide)
      · right
        exact rec3557 10 46 (by decide) (by decide)
      · right
        exact rec3561 10 46 (by decide) (by decide)
      · right
        exact rec3565 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 46)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 47)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3573 10 46 (by decide) (by decide)
      · right
        exact rec3583 10 46 (by decide) (by decide)
      · right
        exact rec3594 10 46 (by decide) (by decide)
      · right
        exact rec3605 10 46 (by decide) (by decide)
      · right
        exact rec3616 10 46 (by decide) (by decide)
      · right
        exact rec3626 10 46 (by decide) (by decide)
      · right
        exact rec3636 10 46 (by decide) (by decide)
      · right
        exact rec3652 10 46 (by decide) (by decide)
      · right
        exact rec3668 10 46 (by decide) (by decide)
      · right
        exact rec3686 10 46 (by decide) (by decide)
      · right
        exact rec3696 10 46 (by decide) (by decide)
      · right
        exact rec3706 10 46 (by decide) (by decide)
      · right
        exact rec3722 10 46 (by decide) (by decide)
      · right
        exact rec3739 10 46 (by decide) (by decide)
      · right
        exact rec3756 10 46 (by decide) (by decide)
      · right
        exact rec3766 10 46 (by decide) (by decide)
      · right
        exact rec3776 10 46 (by decide) (by decide)
      · right
        exact rec3791 10 46 (by decide) (by decide)
      · right
        exact rec3807 10 46 (by decide) (by decide)
      · right
        exact rec3823 10 46 (by decide) (by decide)
      · right
        exact rec3833 10 46 (by decide) (by decide)
      · right
        exact rec3843 10 46 (by decide) (by decide)
      · right
        exact rec3858 10 46 (by decide) (by decide)
      · right
        exact rec3874 10 46 (by decide) (by decide)
      · right
        exact rec3890 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 48)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 49)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 50)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3903 10 46 (by decide) (by decide)
      · right
        exact rec3915 10 46 (by decide) (by decide)
      · right
        exact rec3927 10 46 (by decide) (by decide)
      · right
        exact rec3939 10 46 (by decide) (by decide)
      · right
        exact rec3951 10 46 (by decide) (by decide)
      · right
        exact rec3963 10 46 (by decide) (by decide)
      · right
        exact rec3975 10 46 (by decide) (by decide)
      · right
        exact rec3987 10 46 (by decide) (by decide)
      · right
        exact rec3999 10 46 (by decide) (by decide)
      · right
        exact rec4011 10 46 (by decide) (by decide)
      · right
        exact rec4023 10 46 (by decide) (by decide)
      · right
        exact rec4035 10 46 (by decide) (by decide)
      · right
        exact rec4047 10 46 (by decide) (by decide)
      · right
        exact rec4059 10 46 (by decide) (by decide)
      · right
        exact rec4071 10 46 (by decide) (by decide)
      · right
        exact rec4083 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 51)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 52)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 53)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4097 10 46 (by decide) (by decide)
      · right
        exact rec4113 10 46 (by decide) (by decide)
      · right
        exact rec4128 10 46 (by decide) (by decide)
      · right
        exact rec4144 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 554)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 55)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4157 10 46 (by decide) (by decide)
      · right
        exact rec4164 10 46 (by decide) (by decide)
      · right
        exact rec4173 10 46 (by decide) (by decide)
      · right
        exact rec4181 10 46 (by decide) (by decide)
      · right
        exact rec4192 10 46 (by decide) (by decide)
      · right
        exact rec4199 10 46 (by decide) (by decide)
      · right
        exact rec4208 10 46 (by decide) (by decide)
      · right
        exact rec4216 10 46 (by decide) (by decide)
      · right
        exact rec4224 10 46 (by decide) (by decide)
      · right
        exact rec4229 10 46 (by decide) (by decide)
      · right
        exact rec4236 10 46 (by decide) (by decide)
      · right
        exact rec4244 10 46 (by decide) (by decide)
      · right
        exact rec4252 10 46 (by decide) (by decide)
      · right
        exact rec4261 10 46 (by decide) (by decide)
      · right
        exact rec4267 10 46 (by decide) (by decide)
      · right
        exact rec4276 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 56)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
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
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 57)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4282 10 46 (by decide) (by decide)
      · right
        exact rec4288 10 46 (by decide) (by decide)
      · right
        exact rec4300 10 46 (by decide) (by decide)
      · right
        exact rec4306 10 46 (by decide) (by decide)
      · right
        exact rec4312 10 46 (by decide) (by decide)
      · right
        exact rec4318 10 46 (by decide) (by decide)
      · right
        exact rec4331 10 46 (by decide) (by decide)
      · right
        exact rec4337 10 46 (by decide) (by decide)
      · right
        exact rec4343 10 46 (by decide) (by decide)
      · right
        exact rec4349 10 46 (by decide) (by decide)
      · right
        exact rec4362 10 46 (by decide) (by decide)
      · right
        exact rec4368 10 46 (by decide) (by decide)
      · right
        exact rec4374 10 46 (by decide) (by decide)
      · right
        exact rec4380 10 46 (by decide) (by decide)
      · right
        exact rec4386 10 46 (by decide) (by decide)
      · right
        exact rec4392 10 46 (by decide) (by decide)
      · right
        exact rec4398 10 46 (by decide) (by decide)
      · right
        exact rec4404 10 46 (by decide) (by decide)
      · right
        exact rec4410 10 46 (by decide) (by decide)
      · right
        exact rec4416 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 555)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 59)).length = 10 := by decide +kernel
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
    exact rec3081 10 47 (by decide) (by decide)
end Section14Coverage_10_2_p32_48

#print axioms solution
