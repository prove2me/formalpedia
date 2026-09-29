-- Prove2me | solution 1 for Freiman.section14_s0010_coverage0003_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:51:13.551677+00:00
-- url     : https://prove2.me/submissions/6a9fcaa5-667f-48a6-84d6-fdee79d3c4c6

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
namespace Section14Coverage_10_3_p32_48
private theorem rec4582 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([32, 33, 36, 37, 40, 41, 44, 45, 48, 49, 52, 53, 56, 57, 60, 61] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[433]? = some (⟨60,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) from rfl))
private theorem rec4589 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([43] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[9,10],[43],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[440]? = some (⟨60,(-1),[9,10],[43],207⟩) from rfl))
private theorem rec4590 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([47] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[9,10],[47],239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[441]? = some (⟨60,(-1),[9,10],[47],239⟩) from rfl))
private theorem rec4594 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([34] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[9,10],[34],344⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[445]? = some (⟨60,(-1),[9,10],[34],344⟩) from rfl))
private theorem rec4595 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([35, 39] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[9,10],[35,39],345⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[446]? = some (⟨60,(-1),[9,10],[35,39],345⟩) from rfl))
private theorem rec4596 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([42] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[9,10],[42],366⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[447]? = some (⟨60,(-1),[9,10],[42],366⟩) from rfl))
private theorem rec4610 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(0),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[461]? = some (⟨62,(0),[9,10],[46],3⟩) from rfl))
private theorem rec4611 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(0),[9,10],[38],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[462]? = some (⟨62,(0),[9,10],[38],347⟩) from rfl))
private theorem rec4614 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(1),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[465]? = some (⟨62,(1),[9,10],[46],3⟩) from rfl))
private theorem rec4615 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(1),[9,10],[38],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[466]? = some (⟨62,(1),[9,10],[38],347⟩) from rfl))
private theorem rec4618 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(2),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[469]? = some (⟨62,(2),[9,10],[46],3⟩) from rfl))
private theorem rec4619 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(2),[9,10],[38],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[470]? = some (⟨62,(2),[9,10],[38],347⟩) from rfl))
private theorem rec4622 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(3),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[473]? = some (⟨62,(3),[9,10],[46],3⟩) from rfl))
private theorem rec4623 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(3),[9,10],[38],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[474]? = some (⟨62,(3),[9,10],[38],347⟩) from rfl))
private theorem rec4626 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(4),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[477]? = some (⟨62,(4),[9,10],[46],3⟩) from rfl))
private theorem rec4627 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(4),[9,10],[38],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[478]? = some (⟨62,(4),[9,10],[38],347⟩) from rfl))
private theorem rec4630 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(5),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[481]? = some (⟨62,(5),[9,10],[46],3⟩) from rfl))
private theorem rec4631 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(5),[9,10],[38],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[482]? = some (⟨62,(5),[9,10],[38],348⟩) from rfl))
private theorem rec4634 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(6),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[485]? = some (⟨62,(6),[9,10],[46],3⟩) from rfl))
private theorem rec4635 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(6),[9,10],[38],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[486]? = some (⟨62,(6),[9,10],[38],348⟩) from rfl))
private theorem rec4638 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(7),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[489]? = some (⟨62,(7),[9,10],[46],3⟩) from rfl))
private theorem rec4639 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(7),[9,10],[38],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[490]? = some (⟨62,(7),[9,10],[38],348⟩) from rfl))
private theorem rec4642 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(8),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[493]? = some (⟨62,(8),[9,10],[46],3⟩) from rfl))
private theorem rec4643 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(8),[9,10],[38],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[494]? = some (⟨62,(8),[9,10],[38],348⟩) from rfl))
private theorem rec4646 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(9),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[497]? = some (⟨62,(9),[9,10],[46],3⟩) from rfl))
private theorem rec4647 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(9),[9,10],[38],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[498]? = some (⟨62,(9),[9,10],[38],348⟩) from rfl))
private theorem rec4650 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(10),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[501]? = some (⟨62,(10),[9,10],[46],3⟩) from rfl))
private theorem rec4651 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(10),[9,10],[38],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[502]? = some (⟨62,(10),[9,10],[38],349⟩) from rfl))
private theorem rec4654 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(11),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[505]? = some (⟨62,(11),[9,10],[46],3⟩) from rfl))
private theorem rec4655 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(11),[9,10],[38],350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[506]? = some (⟨62,(11),[9,10],[38],350⟩) from rfl))
private theorem rec4658 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(12),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[509]? = some (⟨62,(12),[9,10],[46],3⟩) from rfl))
private theorem rec4659 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(12),[9,10],[38],351⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[510]? = some (⟨62,(12),[9,10],[38],351⟩) from rfl))
private theorem rec4662 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(13),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[513]? = some (⟨62,(13),[9,10],[46],3⟩) from rfl))
private theorem rec4663 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(13),[9,10],[38],350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[514]? = some (⟨62,(13),[9,10],[38],350⟩) from rfl))
private theorem rec4666 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(14),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[517]? = some (⟨62,(14),[9,10],[46],3⟩) from rfl))
private theorem rec4667 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(14),[9,10],[38],352⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[518]? = some (⟨62,(14),[9,10],[38],352⟩) from rfl))
private theorem rec4670 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(15),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[521]? = some (⟨62,(15),[9,10],[46],3⟩) from rfl))
private theorem rec4671 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(15),[9,10],[38],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[522]? = some (⟨62,(15),[9,10],[38],349⟩) from rfl))
private theorem rec4674 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(16),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[525]? = some (⟨62,(16),[9,10],[46],3⟩) from rfl))
private theorem rec4675 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(16),[9,10],[38],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[526]? = some (⟨62,(16),[9,10],[38],353⟩) from rfl))
private theorem rec4678 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(17),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[529]? = some (⟨62,(17),[9,10],[46],3⟩) from rfl))
private theorem rec4679 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(17),[9,10],[38],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[530]? = some (⟨62,(17),[9,10],[38],353⟩) from rfl))
private theorem rec4682 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(18),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[533]? = some (⟨62,(18),[9,10],[46],3⟩) from rfl))
private theorem rec4683 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(18),[9,10],[38],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[534]? = some (⟨62,(18),[9,10],[38],353⟩) from rfl))
private theorem rec4686 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(19),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[537]? = some (⟨62,(19),[9,10],[46],3⟩) from rfl))
private theorem rec4687 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(19),[9,10],[38],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[538]? = some (⟨62,(19),[9,10],[38],353⟩) from rfl))
private theorem rec4690 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(20),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[541]? = some (⟨62,(20),[9,10],[46],3⟩) from rfl))
private theorem rec4691 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(20),[9,10],[38],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[542]? = some (⟨62,(20),[9,10],[38],349⟩) from rfl))
private theorem rec4694 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(21),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[545]? = some (⟨62,(21),[9,10],[46],3⟩) from rfl))
private theorem rec4695 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(21),[9,10],[38],350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[546]? = some (⟨62,(21),[9,10],[38],350⟩) from rfl))
private theorem rec4698 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(22),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[549]? = some (⟨62,(22),[9,10],[46],3⟩) from rfl))
private theorem rec4699 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(22),[9,10],[38],351⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[550]? = some (⟨62,(22),[9,10],[38],351⟩) from rfl))
private theorem rec4702 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(23),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[553]? = some (⟨62,(23),[9,10],[46],3⟩) from rfl))
private theorem rec4703 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(23),[9,10],[38],350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[554]? = some (⟨62,(23),[9,10],[38],350⟩) from rfl))
private theorem rec4706 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 62 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(24),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[557]? = some (⟨62,(24),[9,10],[46],3⟩) from rfl))
private theorem rec4707 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 62 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(24),[9,10],[38],352⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[558]? = some (⟨62,(24),[9,10],[38],352⟩) from rfl))
private theorem rec4860 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(0),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[711]? = some (⟨67,(0),[9,10],[38,46],2⟩) from rfl))
private theorem rec4863 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(1),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[714]? = some (⟨67,(1),[9,10],[38,46],2⟩) from rfl))
private theorem rec4866 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(2),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[717]? = some (⟨67,(2),[9,10],[38,46],2⟩) from rfl))
private theorem rec4869 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(3),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[720]? = some (⟨67,(3),[9,10],[38,46],2⟩) from rfl))
private theorem rec4872 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(4),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[723]? = some (⟨67,(4),[9,10],[38,46],2⟩) from rfl))
private theorem rec4875 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(5),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[726]? = some (⟨67,(5),[9,10],[38,46],2⟩) from rfl))
private theorem rec4878 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(6),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[729]? = some (⟨67,(6),[9,10],[38,46],2⟩) from rfl))
private theorem rec4881 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(7),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[732]? = some (⟨67,(7),[9,10],[38,46],2⟩) from rfl))
private theorem rec4884 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(8),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[735]? = some (⟨67,(8),[9,10],[38,46],2⟩) from rfl))
private theorem rec4887 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(9),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[738]? = some (⟨67,(9),[9,10],[38,46],2⟩) from rfl))
private theorem rec4890 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(10),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[741]? = some (⟨67,(10),[9,10],[38,46],2⟩) from rfl))
private theorem rec4893 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(11),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[744]? = some (⟨67,(11),[9,10],[38,46],2⟩) from rfl))
private theorem rec4896 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(12),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[747]? = some (⟨67,(12),[9,10],[38,46],2⟩) from rfl))
private theorem rec4899 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(13),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[750]? = some (⟨67,(13),[9,10],[38,46],2⟩) from rfl))
private theorem rec4902 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(14),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[753]? = some (⟨67,(14),[9,10],[38,46],2⟩) from rfl))
private theorem rec4905 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(15),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[756]? = some (⟨67,(15),[9,10],[38,46],2⟩) from rfl))
private theorem rec4908 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(16),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[759]? = some (⟨67,(16),[9,10],[38,46],2⟩) from rfl))
private theorem rec4911 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(17),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[762]? = some (⟨67,(17),[9,10],[38,46],2⟩) from rfl))
private theorem rec4914 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(18),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[765]? = some (⟨67,(18),[9,10],[38,46],2⟩) from rfl))
private theorem rec4917 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(19),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[768]? = some (⟨67,(19),[9,10],[38,46],2⟩) from rfl))
private theorem rec4920 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(20),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[771]? = some (⟨67,(20),[9,10],[38,46],2⟩) from rfl))
private theorem rec4923 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(21),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[774]? = some (⟨67,(21),[9,10],[38,46],2⟩) from rfl))
private theorem rec4926 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(22),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[777]? = some (⟨67,(22),[9,10],[38,46],2⟩) from rfl))
private theorem rec4929 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(23),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[780]? = some (⟨67,(23),[9,10],[38,46],2⟩) from rfl))
private theorem rec4932 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 67 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(24),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[783]? = some (⟨67,(24),[9,10],[38,46],2⟩) from rfl))
private theorem rec4939 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(0),[9,10],[38,46],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[790]? = some (⟨69,(0),[9,10],[38,46],189⟩) from rfl))
private theorem rec4948 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(1),[9,10],[38,46],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[799]? = some (⟨69,(1),[9,10],[38,46],260⟩) from rfl))
private theorem rec4959 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[9,10],[46],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[810]? = some (⟨69,(2),[9,10],[46],375⟩) from rfl))
private theorem rec4960 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[10],[38],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[811]? = some (⟨69,(2),[10],[38],375⟩) from rfl))
private theorem rec4971 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[9,10],[46],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[822]? = some (⟨69,(3),[9,10],[46],376⟩) from rfl))
private theorem rec4972 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[10],[38],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[823]? = some (⟨69,(3),[10],[38],376⟩) from rfl))
private theorem rec4983 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[9,10],[46],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[834]? = some (⟨69,(4),[9,10],[46],377⟩) from rfl))
private theorem rec4984 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[10],[38],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[835]? = some (⟨69,(4),[10],[38],377⟩) from rfl))
private theorem rec4992 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(5),[9,10],[38,46],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[843]? = some (⟨69,(5),[9,10],[38,46],189⟩) from rfl))
private theorem rec5001 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(6),[9,10],[38,46],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[852]? = some (⟨69,(6),[9,10],[38,46],260⟩) from rfl))
private theorem rec5010 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[9,10],[46],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[861]? = some (⟨69,(7),[9,10],[46],375⟩) from rfl))
private theorem rec5011 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[10],[38],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[862]? = some (⟨69,(7),[10],[38],375⟩) from rfl))
private theorem rec5020 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[9,10],[46],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[871]? = some (⟨69,(8),[9,10],[46],376⟩) from rfl))
private theorem rec5021 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[10],[38],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[872]? = some (⟨69,(8),[10],[38],376⟩) from rfl))
private theorem rec5030 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[9,10],[46],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[881]? = some (⟨69,(9),[9,10],[46],377⟩) from rfl))
private theorem rec5031 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[10],[38],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[882]? = some (⟨69,(9),[10],[38],377⟩) from rfl))
private theorem rec5039 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(10),[9,10],[38,46],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[890]? = some (⟨69,(10),[9,10],[38,46],194⟩) from rfl))
private theorem rec5048 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(11),[9,10],[38,46],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[899]? = some (⟨69,(11),[9,10],[38,46],267⟩) from rfl))
private theorem rec5057 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[9,10],[46],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[908]? = some (⟨69,(12),[9,10],[46],378⟩) from rfl))
private theorem rec5058 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[10],[38],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[909]? = some (⟨69,(12),[10],[38],378⟩) from rfl))
private theorem rec5067 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[9,10],[46],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[918]? = some (⟨69,(13),[9,10],[46],378⟩) from rfl))
private theorem rec5068 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[10],[38],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[919]? = some (⟨69,(13),[10],[38],378⟩) from rfl))
private theorem rec5077 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[9,10],[46],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[928]? = some (⟨69,(14),[9,10],[46],377⟩) from rfl))
private theorem rec5078 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[10],[38],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[929]? = some (⟨69,(14),[10],[38],377⟩) from rfl))
private theorem rec5086 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(15),[9,10],[38,46],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[937]? = some (⟨69,(15),[9,10],[38,46],196⟩) from rfl))
private theorem rec5095 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(16),[9,10],[38,46],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[946]? = some (⟨69,(16),[9,10],[38,46],269⟩) from rfl))
private theorem rec5104 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[9,10],[46],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[955]? = some (⟨69,(17),[9,10],[46],379⟩) from rfl))
private theorem rec5105 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[10],[38],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[956]? = some (⟨69,(17),[10],[38],379⟩) from rfl))
private theorem rec5114 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[9,10],[46],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[965]? = some (⟨69,(18),[9,10],[46],379⟩) from rfl))
private theorem rec5115 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[10],[38],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[966]? = some (⟨69,(18),[10],[38],379⟩) from rfl))
private theorem rec5124 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[9,10],[46],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[975]? = some (⟨69,(19),[9,10],[46],379⟩) from rfl))
private theorem rec5125 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[10],[38],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[976]? = some (⟨69,(19),[10],[38],379⟩) from rfl))
private theorem rec5133 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(20),[9,10],[38,46],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[984]? = some (⟨69,(20),[9,10],[38,46],198⟩) from rfl))
private theorem rec5142 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(21),[9,10],[38,46],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[993]? = some (⟨69,(21),[9,10],[38,46],271⟩) from rfl))
private theorem rec5151 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[9,10],[46],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1002]? = some (⟨69,(22),[9,10],[46],380⟩) from rfl))
private theorem rec5152 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[10],[38],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1003]? = some (⟨69,(22),[10],[38],380⟩) from rfl))
private theorem rec5161 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[9,10],[46],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1012]? = some (⟨69,(23),[9,10],[46],380⟩) from rfl))
private theorem rec5162 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[10],[38],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1013]? = some (⟨69,(23),[10],[38],380⟩) from rfl))
private theorem rec5171 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[9,10],[46],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1022]? = some (⟨69,(24),[9,10],[46],380⟩) from rfl))
private theorem rec5172 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[10],[38],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1023]? = some (⟨69,(24),[10],[38],380⟩) from rfl))
private theorem rec5180 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(0),[9,10],[38],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1031]? = some (⟨72,(0),[9,10],[38],354⟩) from rfl))
private theorem rec5181 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(0),[9,10],[46],1399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1032]? = some (⟨72,(0),[9,10],[46],1399⟩) from rfl))
private theorem rec5188 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(1),[9,10],[38],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1039]? = some (⟨72,(1),[9,10],[38],355⟩) from rfl))
private theorem rec5189 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(1),[9,10],[46],1400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1040]? = some (⟨72,(1),[9,10],[46],1400⟩) from rfl))
private theorem rec5196 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(2),[9,10],[38],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1047]? = some (⟨72,(2),[9,10],[38],356⟩) from rfl))
private theorem rec5197 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(2),[9,10],[46],1401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1048]? = some (⟨72,(2),[9,10],[46],1401⟩) from rfl))
private theorem rec5204 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(3),[9,10],[38],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1055]? = some (⟨72,(3),[9,10],[38],357⟩) from rfl))
private theorem rec5205 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(3),[9,10],[46],1402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1056]? = some (⟨72,(3),[9,10],[46],1402⟩) from rfl))
private theorem rec5212 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(4),[9,10],[38],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1063]? = some (⟨72,(4),[9,10],[38],354⟩) from rfl))
private theorem rec5213 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(4),[9,10],[46],1399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1064]? = some (⟨72,(4),[9,10],[46],1399⟩) from rfl))
private theorem rec5220 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(5),[9,10],[38],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1071]? = some (⟨72,(5),[9,10],[38],355⟩) from rfl))
private theorem rec5221 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(5),[9,10],[46],1400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1072]? = some (⟨72,(5),[9,10],[46],1400⟩) from rfl))
private theorem rec5228 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(6),[9,10],[38],358⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1079]? = some (⟨72,(6),[9,10],[38],358⟩) from rfl))
private theorem rec5229 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(6),[9,10],[46],1403⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1080]? = some (⟨72,(6),[9,10],[46],1403⟩) from rfl))
private theorem rec5236 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(7),[9,10],[38],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1087]? = some (⟨72,(7),[9,10],[38],357⟩) from rfl))
private theorem rec5237 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(7),[9,10],[46],1402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1088]? = some (⟨72,(7),[9,10],[46],1402⟩) from rfl))
private theorem rec5244 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(8),[9,10],[38],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1095]? = some (⟨72,(8),[9,10],[38],354⟩) from rfl))
private theorem rec5245 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(8),[9,10],[46],1399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1096]? = some (⟨72,(8),[9,10],[46],1399⟩) from rfl))
private theorem rec5252 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(9),[9,10],[38],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1103]? = some (⟨72,(9),[9,10],[38],355⟩) from rfl))
private theorem rec5253 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(9),[9,10],[46],1400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1104]? = some (⟨72,(9),[9,10],[46],1400⟩) from rfl))
private theorem rec5260 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(10),[9,10],[38],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1111]? = some (⟨72,(10),[9,10],[38],356⟩) from rfl))
private theorem rec5261 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(10),[9,10],[46],1401⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1112]? = some (⟨72,(10),[9,10],[46],1401⟩) from rfl))
private theorem rec5268 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(11),[9,10],[38],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1119]? = some (⟨72,(11),[9,10],[38],357⟩) from rfl))
private theorem rec5269 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(11),[9,10],[46],1402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1120]? = some (⟨72,(11),[9,10],[46],1402⟩) from rfl))
private theorem rec5276 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(12),[9,10],[38],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1127]? = some (⟨72,(12),[9,10],[38],354⟩) from rfl))
private theorem rec5277 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(12),[9,10],[46],1399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1128]? = some (⟨72,(12),[9,10],[46],1399⟩) from rfl))
private theorem rec5284 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(13),[9,10],[38],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1135]? = some (⟨72,(13),[9,10],[38],355⟩) from rfl))
private theorem rec5285 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(13),[9,10],[46],1400⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1136]? = some (⟨72,(13),[9,10],[46],1400⟩) from rfl))
private theorem rec5292 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(14),[9,10],[38],359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1143]? = some (⟨72,(14),[9,10],[38],359⟩) from rfl))
private theorem rec5293 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(14),[9,10],[46],1404⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1144]? = some (⟨72,(14),[9,10],[46],1404⟩) from rfl))
private theorem rec5300 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 72 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(15),[9,10],[38],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1151]? = some (⟨72,(15),[9,10],[38],357⟩) from rfl))
private theorem rec5301 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 72 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(15),[9,10],[46],1402⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1152]? = some (⟨72,(15),[9,10],[46],1402⟩) from rfl))
private theorem rec5309 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[9,10],[46],381⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1160]? = some (⟨75,(0),[9,10],[46],381⟩) from rfl))
private theorem rec5310 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[10],[38],381⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1161]? = some (⟨75,(0),[10],[38],381⟩) from rfl))
private theorem rec5319 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[9,10],[46],382⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1170]? = some (⟨75,(1),[9,10],[46],382⟩) from rfl))
private theorem rec5320 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[10],[38],382⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1171]? = some (⟨75,(1),[10],[38],382⟩) from rfl))
private theorem rec5329 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[9,10],[46],383⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1180]? = some (⟨75,(2),[9,10],[46],383⟩) from rfl))
private theorem rec5330 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[10],[38],383⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1181]? = some (⟨75,(2),[10],[38],383⟩) from rfl))
private theorem rec5339 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[9,10],[46],384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1190]? = some (⟨75,(3),[9,10],[46],384⟩) from rfl))
private theorem rec5340 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[10],[38],384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1191]? = some (⟨75,(3),[10],[38],384⟩) from rfl))
private theorem rec5347 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(0),[10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1198]? = some (⟨77,(0),[10],[38],2⟩) from rfl))
private theorem rec5348 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(0),[10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1199]? = some (⟨77,(0),[10],[46],3⟩) from rfl))
private theorem rec5354 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(1),[9,10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1205]? = some (⟨77,(1),[9,10],[38],2⟩) from rfl))
private theorem rec5355 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(1),[10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1206]? = some (⟨77,(1),[10],[46],3⟩) from rfl))
private theorem rec5362 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(2),[10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1213]? = some (⟨77,(2),[10],[46],2⟩) from rfl))
private theorem rec5363 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(2),[10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1214]? = some (⟨77,(2),[10],[38],3⟩) from rfl))
private theorem rec5368 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(3),[9,10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1219]? = some (⟨77,(3),[9,10],[46],2⟩) from rfl))
private theorem rec5369 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(3),[10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1220]? = some (⟨77,(3),[10],[38],3⟩) from rfl))
private theorem rec5376 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(4),[10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[1]? = some (⟨77,(4),[10],[38],2⟩) from rfl))
private theorem rec5377 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(4),[10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[2]? = some (⟨77,(4),[10],[46],3⟩) from rfl))
private theorem rec5382 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(5),[9,10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[7]? = some (⟨77,(5),[9,10],[38],2⟩) from rfl))
private theorem rec5383 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(5),[10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[8]? = some (⟨77,(5),[10],[46],3⟩) from rfl))
private theorem rec5390 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(6),[10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[15]? = some (⟨77,(6),[10],[46],2⟩) from rfl))
private theorem rec5391 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(6),[10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[16]? = some (⟨77,(6),[10],[38],3⟩) from rfl))
private theorem rec5396 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(7),[9,10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[21]? = some (⟨77,(7),[9,10],[46],2⟩) from rfl))
private theorem rec5397 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(7),[10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[22]? = some (⟨77,(7),[10],[38],3⟩) from rfl))
private theorem rec5400 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(8),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[25]? = some (⟨77,(8),[9,10],[46],3⟩) from rfl))
private theorem rec5401 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(8),[9,10],[38],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[26]? = some (⟨77,(8),[9,10],[38],98⟩) from rfl))
private theorem rec5404 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(9),[9,10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[29]? = some (⟨77,(9),[9,10],[46],3⟩) from rfl))
private theorem rec5405 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(9),[9,10],[38],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[30]? = some (⟨77,(9),[9,10],[38],159⟩) from rfl))
private theorem rec5408 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(10),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[33]? = some (⟨77,(10),[9,10],[38],3⟩) from rfl))
private theorem rec5409 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(10),[9,10],[46],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[34]? = some (⟨77,(10),[9,10],[46],29⟩) from rfl))
private theorem rec5412 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(11),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[37]? = some (⟨77,(11),[9,10],[38],3⟩) from rfl))
private theorem rec5413 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(11),[9,10],[46],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[38]? = some (⟨77,(11),[9,10],[46],234⟩) from rfl))
private theorem rec5419 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(12),[10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[44]? = some (⟨77,(12),[10],[46],3⟩) from rfl))
private theorem rec5420 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(12),[10],[38],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[45]? = some (⟨77,(12),[10],[38],99⟩) from rfl))
private theorem rec5425 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(13),[9,10],[38],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[50]? = some (⟨77,(13),[9,10],[38],99⟩) from rfl))
private theorem rec5426 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(13),[10],[46],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[51]? = some (⟨77,(13),[10],[46],3⟩) from rfl))
private theorem rec5430 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(14),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[55]? = some (⟨77,(14),[9,10],[38],3⟩) from rfl))
private theorem rec5431 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(14),[9,10],[46],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[56]? = some (⟨77,(14),[9,10],[46],29⟩) from rfl))
private theorem rec5436 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(15),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[61]? = some (⟨77,(15),[9,10],[38],3⟩) from rfl))
private theorem rec5437 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(15),[9,10],[46],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[62]? = some (⟨77,(15),[9,10],[46],99⟩) from rfl))
private theorem rec5440 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(0),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[65]? = some (⟨79,(0),[9,10],[38,46],2⟩) from rfl))
private theorem rec5443 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(1),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[68]? = some (⟨79,(1),[9,10],[38,46],2⟩) from rfl))
private theorem rec5450 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 79 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(2),[9,10],[38],364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[75]? = some (⟨79,(2),[9,10],[38],364⟩) from rfl))
private theorem rec5451 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(2),[9,10],[46],1405⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[76]? = some (⟨79,(2),[9,10],[46],1405⟩) from rfl))
private theorem rec5454 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(3),[9,10],[38,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[79]? = some (⟨79,(3),[9,10],[38,46],101⟩) from rfl))
private theorem rec5457 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(4),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[82]? = some (⟨79,(4),[9,10],[38,46],2⟩) from rfl))
private theorem rec5460 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(5),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[85]? = some (⟨79,(5),[9,10],[38,46],2⟩) from rfl))
private theorem rec5467 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 79 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(6),[9,10],[38],365⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[92]? = some (⟨79,(6),[9,10],[38],365⟩) from rfl))
private theorem rec5468 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(6),[9,10],[46],1406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[93]? = some (⟨79,(6),[9,10],[46],1406⟩) from rfl))
private theorem rec5471 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(7),[9,10],[38,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[96]? = some (⟨79,(7),[9,10],[38,46],101⟩) from rfl))
private theorem rec5474 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(8),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[99]? = some (⟨79,(8),[9,10],[38,46],2⟩) from rfl))
private theorem rec5477 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(9),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[102]? = some (⟨79,(9),[9,10],[38,46],2⟩) from rfl))
private theorem rec5481 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 79 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(10),[9,10],[38],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[106]? = some (⟨79,(10),[9,10],[38],339⟩) from rfl))
private theorem rec5482 (si parent : ℕ) (hs : si ∈ ([10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(10),[10],[46],1680⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[107]? = some (⟨79,(10),[10],[46],1680⟩) from rfl))
private theorem rec5485 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(11),[9,10],[38,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[110]? = some (⟨79,(11),[9,10],[38,46],101⟩) from rfl))
private theorem rec5488 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(12),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[113]? = some (⟨79,(12),[9,10],[38,46],2⟩) from rfl))
private theorem rec5491 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(13),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[116]? = some (⟨79,(13),[9,10],[38,46],2⟩) from rfl))
private theorem rec5494 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(14),[9,10],[38,46],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[119]? = some (⟨79,(14),[9,10],[38,46],286⟩) from rfl))
private theorem rec5497 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(15),[9,10],[38,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[122]? = some (⟨79,(15),[9,10],[38,46],101⟩) from rfl))
private theorem rec5500 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(16),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[125]? = some (⟨79,(16),[9,10],[38,46],2⟩) from rfl))
private theorem rec5503 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(17),[9,10],[38,46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[128]? = some (⟨79,(17),[9,10],[38,46],2⟩) from rfl))
private theorem rec5508 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(18),[9,10],[38,46],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[133]? = some (⟨79,(18),[9,10],[38,46],287⟩) from rfl))
private theorem rec5511 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(19),[9,10],[38,46],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[136]? = some (⟨79,(19),[9,10],[38,46],101⟩) from rfl))
private theorem rec16364 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(0),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[156]? = some (⟨557,(0),[9,10],[38],3⟩) from rfl))
private theorem rec16365 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(0),[9,10],[46],1663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[157]? = some (⟨557,(0),[9,10],[46],1663⟩) from rfl))
private theorem rec16369 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(1),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[161]? = some (⟨557,(1),[9,10],[38],3⟩) from rfl))
private theorem rec16370 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(1),[9,10],[46],1664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[162]? = some (⟨557,(1),[9,10],[46],1664⟩) from rfl))
private theorem rec16374 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(2),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[166]? = some (⟨557,(2),[9,10],[38],3⟩) from rfl))
private theorem rec16375 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(2),[9,10],[46],1663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[167]? = some (⟨557,(2),[9,10],[46],1663⟩) from rfl))
private theorem rec16379 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(3),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[171]? = some (⟨557,(3),[9,10],[38],3⟩) from rfl))
private theorem rec16380 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(3),[9,10],[46],1665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[172]? = some (⟨557,(3),[9,10],[46],1665⟩) from rfl))
private theorem rec16384 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(4),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[176]? = some (⟨557,(4),[9,10],[38],3⟩) from rfl))
private theorem rec16385 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(4),[9,10],[46],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[177]? = some (⟨557,(4),[9,10],[46],371⟩) from rfl))
private theorem rec16389 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(5),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[181]? = some (⟨557,(5),[9,10],[38],3⟩) from rfl))
private theorem rec16390 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(5),[9,10],[46],1663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[182]? = some (⟨557,(5),[9,10],[46],1663⟩) from rfl))
private theorem rec16394 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(6),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[186]? = some (⟨557,(6),[9,10],[38],3⟩) from rfl))
private theorem rec16395 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(6),[9,10],[46],1664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[187]? = some (⟨557,(6),[9,10],[46],1664⟩) from rfl))
private theorem rec16399 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(7),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[191]? = some (⟨557,(7),[9,10],[38],3⟩) from rfl))
private theorem rec16400 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(7),[9,10],[46],1663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[192]? = some (⟨557,(7),[9,10],[46],1663⟩) from rfl))
private theorem rec16404 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(8),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[196]? = some (⟨557,(8),[9,10],[38],3⟩) from rfl))
private theorem rec16405 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(8),[9,10],[46],1665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[197]? = some (⟨557,(8),[9,10],[46],1665⟩) from rfl))
private theorem rec16409 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 557 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(9),[9,10],[38],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[201]? = some (⟨557,(9),[9,10],[38],3⟩) from rfl))
private theorem rec16410 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 557 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨557,(9),[9,10],[46],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[202]? = some (⟨557,(9),[9,10],[46],371⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 10).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 10)).drop 32).take 16, section14Recorded section14Catalog 10 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 10 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 10).plans.drop 3).take 1 = [⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(556,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(557,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(558,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(559,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(560,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec4582 10 32 (by decide) (by decide)
  · left
    exact rec4582 10 33 (by decide) (by decide)
  · left
    exact rec4594 10 34 (by decide) (by decide)
  · left
    exact rec4595 10 35 (by decide) (by decide)
  · left
    exact rec4582 10 36 (by decide) (by decide)
  · left
    exact rec4582 10 37 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(556,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(557,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(558,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(559,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(560,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 556)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 62)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4611 10 38 (by decide) (by decide)
      · right
        exact rec4615 10 38 (by decide) (by decide)
      · right
        exact rec4619 10 38 (by decide) (by decide)
      · right
        exact rec4623 10 38 (by decide) (by decide)
      · right
        exact rec4627 10 38 (by decide) (by decide)
      · right
        exact rec4631 10 38 (by decide) (by decide)
      · right
        exact rec4635 10 38 (by decide) (by decide)
      · right
        exact rec4639 10 38 (by decide) (by decide)
      · right
        exact rec4643 10 38 (by decide) (by decide)
      · right
        exact rec4647 10 38 (by decide) (by decide)
      · right
        exact rec4651 10 38 (by decide) (by decide)
      · right
        exact rec4655 10 38 (by decide) (by decide)
      · right
        exact rec4659 10 38 (by decide) (by decide)
      · right
        exact rec4663 10 38 (by decide) (by decide)
      · right
        exact rec4667 10 38 (by decide) (by decide)
      · right
        exact rec4671 10 38 (by decide) (by decide)
      · right
        exact rec4675 10 38 (by decide) (by decide)
      · right
        exact rec4679 10 38 (by decide) (by decide)
      · right
        exact rec4683 10 38 (by decide) (by decide)
      · right
        exact rec4687 10 38 (by decide) (by decide)
      · right
        exact rec4691 10 38 (by decide) (by decide)
      · right
        exact rec4695 10 38 (by decide) (by decide)
      · right
        exact rec4699 10 38 (by decide) (by decide)
      · right
        exact rec4703 10 38 (by decide) (by decide)
      · right
        exact rec4707 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 63)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 557)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16364 10 38 (by decide) (by decide)
      · right
        exact rec16369 10 38 (by decide) (by decide)
      · right
        exact rec16374 10 38 (by decide) (by decide)
      · right
        exact rec16379 10 38 (by decide) (by decide)
      · right
        exact rec16384 10 38 (by decide) (by decide)
      · right
        exact rec16389 10 38 (by decide) (by decide)
      · right
        exact rec16394 10 38 (by decide) (by decide)
      · right
        exact rec16399 10 38 (by decide) (by decide)
      · right
        exact rec16404 10 38 (by decide) (by decide)
      · right
        exact rec16409 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 558)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 66)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 67)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4860 10 38 (by decide) (by decide)
      · right
        exact rec4863 10 38 (by decide) (by decide)
      · right
        exact rec4866 10 38 (by decide) (by decide)
      · right
        exact rec4869 10 38 (by decide) (by decide)
      · right
        exact rec4872 10 38 (by decide) (by decide)
      · right
        exact rec4875 10 38 (by decide) (by decide)
      · right
        exact rec4878 10 38 (by decide) (by decide)
      · right
        exact rec4881 10 38 (by decide) (by decide)
      · right
        exact rec4884 10 38 (by decide) (by decide)
      · right
        exact rec4887 10 38 (by decide) (by decide)
      · right
        exact rec4890 10 38 (by decide) (by decide)
      · right
        exact rec4893 10 38 (by decide) (by decide)
      · right
        exact rec4896 10 38 (by decide) (by decide)
      · right
        exact rec4899 10 38 (by decide) (by decide)
      · right
        exact rec4902 10 38 (by decide) (by decide)
      · right
        exact rec4905 10 38 (by decide) (by decide)
      · right
        exact rec4908 10 38 (by decide) (by decide)
      · right
        exact rec4911 10 38 (by decide) (by decide)
      · right
        exact rec4914 10 38 (by decide) (by decide)
      · right
        exact rec4917 10 38 (by decide) (by decide)
      · right
        exact rec4920 10 38 (by decide) (by decide)
      · right
        exact rec4923 10 38 (by decide) (by decide)
      · right
        exact rec4926 10 38 (by decide) (by decide)
      · right
        exact rec4929 10 38 (by decide) (by decide)
      · right
        exact rec4932 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 68)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 69)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4939 10 38 (by decide) (by decide)
      · right
        exact rec4948 10 38 (by decide) (by decide)
      · right
        exact rec4960 10 38 (by decide) (by decide)
      · right
        exact rec4972 10 38 (by decide) (by decide)
      · right
        exact rec4984 10 38 (by decide) (by decide)
      · right
        exact rec4992 10 38 (by decide) (by decide)
      · right
        exact rec5001 10 38 (by decide) (by decide)
      · right
        exact rec5011 10 38 (by decide) (by decide)
      · right
        exact rec5021 10 38 (by decide) (by decide)
      · right
        exact rec5031 10 38 (by decide) (by decide)
      · right
        exact rec5039 10 38 (by decide) (by decide)
      · right
        exact rec5048 10 38 (by decide) (by decide)
      · right
        exact rec5058 10 38 (by decide) (by decide)
      · right
        exact rec5068 10 38 (by decide) (by decide)
      · right
        exact rec5078 10 38 (by decide) (by decide)
      · right
        exact rec5086 10 38 (by decide) (by decide)
      · right
        exact rec5095 10 38 (by decide) (by decide)
      · right
        exact rec5105 10 38 (by decide) (by decide)
      · right
        exact rec5115 10 38 (by decide) (by decide)
      · right
        exact rec5125 10 38 (by decide) (by decide)
      · right
        exact rec5133 10 38 (by decide) (by decide)
      · right
        exact rec5142 10 38 (by decide) (by decide)
      · right
        exact rec5152 10 38 (by decide) (by decide)
      · right
        exact rec5162 10 38 (by decide) (by decide)
      · right
        exact rec5172 10 38 (by decide) (by decide)
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
        exact rec5180 10 38 (by decide) (by decide)
      · right
        exact rec5188 10 38 (by decide) (by decide)
      · right
        exact rec5196 10 38 (by decide) (by decide)
      · right
        exact rec5204 10 38 (by decide) (by decide)
      · right
        exact rec5212 10 38 (by decide) (by decide)
      · right
        exact rec5220 10 38 (by decide) (by decide)
      · right
        exact rec5228 10 38 (by decide) (by decide)
      · right
        exact rec5236 10 38 (by decide) (by decide)
      · right
        exact rec5244 10 38 (by decide) (by decide)
      · right
        exact rec5252 10 38 (by decide) (by decide)
      · right
        exact rec5260 10 38 (by decide) (by decide)
      · right
        exact rec5268 10 38 (by decide) (by decide)
      · right
        exact rec5276 10 38 (by decide) (by decide)
      · right
        exact rec5284 10 38 (by decide) (by decide)
      · right
        exact rec5292 10 38 (by decide) (by decide)
      · right
        exact rec5300 10 38 (by decide) (by decide)
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
        exact rec5310 10 38 (by decide) (by decide)
      · right
        exact rec5320 10 38 (by decide) (by decide)
      · right
        exact rec5330 10 38 (by decide) (by decide)
      · right
        exact rec5340 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 559)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 77)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5347 10 38 (by decide) (by decide)
      · right
        exact rec5354 10 38 (by decide) (by decide)
      · right
        exact rec5363 10 38 (by decide) (by decide)
      · right
        exact rec5369 10 38 (by decide) (by decide)
      · right
        exact rec5376 10 38 (by decide) (by decide)
      · right
        exact rec5382 10 38 (by decide) (by decide)
      · right
        exact rec5391 10 38 (by decide) (by decide)
      · right
        exact rec5397 10 38 (by decide) (by decide)
      · right
        exact rec5401 10 38 (by decide) (by decide)
      · right
        exact rec5405 10 38 (by decide) (by decide)
      · right
        exact rec5408 10 38 (by decide) (by decide)
      · right
        exact rec5412 10 38 (by decide) (by decide)
      · right
        exact rec5420 10 38 (by decide) (by decide)
      · right
        exact rec5425 10 38 (by decide) (by decide)
      · right
        exact rec5430 10 38 (by decide) (by decide)
      · right
        exact rec5436 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 78)).length = 8 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 79)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5440 10 38 (by decide) (by decide)
      · right
        exact rec5443 10 38 (by decide) (by decide)
      · right
        exact rec5450 10 38 (by decide) (by decide)
      · right
        exact rec5454 10 38 (by decide) (by decide)
      · right
        exact rec5457 10 38 (by decide) (by decide)
      · right
        exact rec5460 10 38 (by decide) (by decide)
      · right
        exact rec5467 10 38 (by decide) (by decide)
      · right
        exact rec5471 10 38 (by decide) (by decide)
      · right
        exact rec5474 10 38 (by decide) (by decide)
      · right
        exact rec5477 10 38 (by decide) (by decide)
      · right
        exact rec5481 10 38 (by decide) (by decide)
      · right
        exact rec5485 10 38 (by decide) (by decide)
      · right
        exact rec5488 10 38 (by decide) (by decide)
      · right
        exact rec5491 10 38 (by decide) (by decide)
      · right
        exact rec5494 10 38 (by decide) (by decide)
      · right
        exact rec5497 10 38 (by decide) (by decide)
      · right
        exact rec5500 10 38 (by decide) (by decide)
      · right
        exact rec5503 10 38 (by decide) (by decide)
      · right
        exact rec5508 10 38 (by decide) (by decide)
      · right
        exact rec5511 10 38 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 560)).length = 2 := by decide +kernel
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
    exact rec4595 10 39 (by decide) (by decide)
  · left
    exact rec4582 10 40 (by decide) (by decide)
  · left
    exact rec4582 10 41 (by decide) (by decide)
  · left
    exact rec4596 10 42 (by decide) (by decide)
  · left
    exact rec4589 10 43 (by decide) (by decide)
  · left
    exact rec4582 10 44 (by decide) (by decide)
  · left
    exact rec4582 10 45 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(556,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(557,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(558,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(559,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(560,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 556)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 62)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4610 10 46 (by decide) (by decide)
      · right
        exact rec4614 10 46 (by decide) (by decide)
      · right
        exact rec4618 10 46 (by decide) (by decide)
      · right
        exact rec4622 10 46 (by decide) (by decide)
      · right
        exact rec4626 10 46 (by decide) (by decide)
      · right
        exact rec4630 10 46 (by decide) (by decide)
      · right
        exact rec4634 10 46 (by decide) (by decide)
      · right
        exact rec4638 10 46 (by decide) (by decide)
      · right
        exact rec4642 10 46 (by decide) (by decide)
      · right
        exact rec4646 10 46 (by decide) (by decide)
      · right
        exact rec4650 10 46 (by decide) (by decide)
      · right
        exact rec4654 10 46 (by decide) (by decide)
      · right
        exact rec4658 10 46 (by decide) (by decide)
      · right
        exact rec4662 10 46 (by decide) (by decide)
      · right
        exact rec4666 10 46 (by decide) (by decide)
      · right
        exact rec4670 10 46 (by decide) (by decide)
      · right
        exact rec4674 10 46 (by decide) (by decide)
      · right
        exact rec4678 10 46 (by decide) (by decide)
      · right
        exact rec4682 10 46 (by decide) (by decide)
      · right
        exact rec4686 10 46 (by decide) (by decide)
      · right
        exact rec4690 10 46 (by decide) (by decide)
      · right
        exact rec4694 10 46 (by decide) (by decide)
      · right
        exact rec4698 10 46 (by decide) (by decide)
      · right
        exact rec4702 10 46 (by decide) (by decide)
      · right
        exact rec4706 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 63)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 557)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16365 10 46 (by decide) (by decide)
      · right
        exact rec16370 10 46 (by decide) (by decide)
      · right
        exact rec16375 10 46 (by decide) (by decide)
      · right
        exact rec16380 10 46 (by decide) (by decide)
      · right
        exact rec16385 10 46 (by decide) (by decide)
      · right
        exact rec16390 10 46 (by decide) (by decide)
      · right
        exact rec16395 10 46 (by decide) (by decide)
      · right
        exact rec16400 10 46 (by decide) (by decide)
      · right
        exact rec16405 10 46 (by decide) (by decide)
      · right
        exact rec16410 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 558)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 66)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 67)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4860 10 46 (by decide) (by decide)
      · right
        exact rec4863 10 46 (by decide) (by decide)
      · right
        exact rec4866 10 46 (by decide) (by decide)
      · right
        exact rec4869 10 46 (by decide) (by decide)
      · right
        exact rec4872 10 46 (by decide) (by decide)
      · right
        exact rec4875 10 46 (by decide) (by decide)
      · right
        exact rec4878 10 46 (by decide) (by decide)
      · right
        exact rec4881 10 46 (by decide) (by decide)
      · right
        exact rec4884 10 46 (by decide) (by decide)
      · right
        exact rec4887 10 46 (by decide) (by decide)
      · right
        exact rec4890 10 46 (by decide) (by decide)
      · right
        exact rec4893 10 46 (by decide) (by decide)
      · right
        exact rec4896 10 46 (by decide) (by decide)
      · right
        exact rec4899 10 46 (by decide) (by decide)
      · right
        exact rec4902 10 46 (by decide) (by decide)
      · right
        exact rec4905 10 46 (by decide) (by decide)
      · right
        exact rec4908 10 46 (by decide) (by decide)
      · right
        exact rec4911 10 46 (by decide) (by decide)
      · right
        exact rec4914 10 46 (by decide) (by decide)
      · right
        exact rec4917 10 46 (by decide) (by decide)
      · right
        exact rec4920 10 46 (by decide) (by decide)
      · right
        exact rec4923 10 46 (by decide) (by decide)
      · right
        exact rec4926 10 46 (by decide) (by decide)
      · right
        exact rec4929 10 46 (by decide) (by decide)
      · right
        exact rec4932 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 68)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 69)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4939 10 46 (by decide) (by decide)
      · right
        exact rec4948 10 46 (by decide) (by decide)
      · right
        exact rec4959 10 46 (by decide) (by decide)
      · right
        exact rec4971 10 46 (by decide) (by decide)
      · right
        exact rec4983 10 46 (by decide) (by decide)
      · right
        exact rec4992 10 46 (by decide) (by decide)
      · right
        exact rec5001 10 46 (by decide) (by decide)
      · right
        exact rec5010 10 46 (by decide) (by decide)
      · right
        exact rec5020 10 46 (by decide) (by decide)
      · right
        exact rec5030 10 46 (by decide) (by decide)
      · right
        exact rec5039 10 46 (by decide) (by decide)
      · right
        exact rec5048 10 46 (by decide) (by decide)
      · right
        exact rec5057 10 46 (by decide) (by decide)
      · right
        exact rec5067 10 46 (by decide) (by decide)
      · right
        exact rec5077 10 46 (by decide) (by decide)
      · right
        exact rec5086 10 46 (by decide) (by decide)
      · right
        exact rec5095 10 46 (by decide) (by decide)
      · right
        exact rec5104 10 46 (by decide) (by decide)
      · right
        exact rec5114 10 46 (by decide) (by decide)
      · right
        exact rec5124 10 46 (by decide) (by decide)
      · right
        exact rec5133 10 46 (by decide) (by decide)
      · right
        exact rec5142 10 46 (by decide) (by decide)
      · right
        exact rec5151 10 46 (by decide) (by decide)
      · right
        exact rec5161 10 46 (by decide) (by decide)
      · right
        exact rec5171 10 46 (by decide) (by decide)
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
        exact rec5181 10 46 (by decide) (by decide)
      · right
        exact rec5189 10 46 (by decide) (by decide)
      · right
        exact rec5197 10 46 (by decide) (by decide)
      · right
        exact rec5205 10 46 (by decide) (by decide)
      · right
        exact rec5213 10 46 (by decide) (by decide)
      · right
        exact rec5221 10 46 (by decide) (by decide)
      · right
        exact rec5229 10 46 (by decide) (by decide)
      · right
        exact rec5237 10 46 (by decide) (by decide)
      · right
        exact rec5245 10 46 (by decide) (by decide)
      · right
        exact rec5253 10 46 (by decide) (by decide)
      · right
        exact rec5261 10 46 (by decide) (by decide)
      · right
        exact rec5269 10 46 (by decide) (by decide)
      · right
        exact rec5277 10 46 (by decide) (by decide)
      · right
        exact rec5285 10 46 (by decide) (by decide)
      · right
        exact rec5293 10 46 (by decide) (by decide)
      · right
        exact rec5301 10 46 (by decide) (by decide)
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
        exact rec5309 10 46 (by decide) (by decide)
      · right
        exact rec5319 10 46 (by decide) (by decide)
      · right
        exact rec5329 10 46 (by decide) (by decide)
      · right
        exact rec5339 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 559)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 77)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5348 10 46 (by decide) (by decide)
      · right
        exact rec5355 10 46 (by decide) (by decide)
      · right
        exact rec5362 10 46 (by decide) (by decide)
      · right
        exact rec5368 10 46 (by decide) (by decide)
      · right
        exact rec5377 10 46 (by decide) (by decide)
      · right
        exact rec5383 10 46 (by decide) (by decide)
      · right
        exact rec5390 10 46 (by decide) (by decide)
      · right
        exact rec5396 10 46 (by decide) (by decide)
      · right
        exact rec5400 10 46 (by decide) (by decide)
      · right
        exact rec5404 10 46 (by decide) (by decide)
      · right
        exact rec5409 10 46 (by decide) (by decide)
      · right
        exact rec5413 10 46 (by decide) (by decide)
      · right
        exact rec5419 10 46 (by decide) (by decide)
      · right
        exact rec5426 10 46 (by decide) (by decide)
      · right
        exact rec5431 10 46 (by decide) (by decide)
      · right
        exact rec5437 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 78)).length = 8 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 79)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5440 10 46 (by decide) (by decide)
      · right
        exact rec5443 10 46 (by decide) (by decide)
      · right
        exact rec5451 10 46 (by decide) (by decide)
      · right
        exact rec5454 10 46 (by decide) (by decide)
      · right
        exact rec5457 10 46 (by decide) (by decide)
      · right
        exact rec5460 10 46 (by decide) (by decide)
      · right
        exact rec5468 10 46 (by decide) (by decide)
      · right
        exact rec5471 10 46 (by decide) (by decide)
      · right
        exact rec5474 10 46 (by decide) (by decide)
      · right
        exact rec5477 10 46 (by decide) (by decide)
      · right
        exact rec5482 10 46 (by decide) (by decide)
      · right
        exact rec5485 10 46 (by decide) (by decide)
      · right
        exact rec5488 10 46 (by decide) (by decide)
      · right
        exact rec5491 10 46 (by decide) (by decide)
      · right
        exact rec5494 10 46 (by decide) (by decide)
      · right
        exact rec5497 10 46 (by decide) (by decide)
      · right
        exact rec5500 10 46 (by decide) (by decide)
      · right
        exact rec5503 10 46 (by decide) (by decide)
      · right
        exact rec5508 10 46 (by decide) (by decide)
      · right
        exact rec5511 10 46 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 560)).length = 2 := by decide +kernel
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
    exact rec4590 10 47 (by decide) (by decide)
end Section14Coverage_10_3_p32_48

#print axioms solution
