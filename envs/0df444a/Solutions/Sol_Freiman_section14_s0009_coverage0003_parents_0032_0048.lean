-- Prove2me | solution 1 for Freiman.section14_s0009_coverage0003_parents_0032_0048
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T19:02:19.009352+00:00
-- url     : https://prove2.me/submissions/9111460a-4b53-431d-9bad-78e8d3c87664

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
namespace Section14Coverage_9_3_p32_48
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
private theorem rec4958 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[9],[38],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[809]? = some (⟨69,(2),[9],[38],191⟩) from rfl))
private theorem rec4959 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[9,10],[46],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[810]? = some (⟨69,(2),[9,10],[46],375⟩) from rfl))
private theorem rec4970 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[9],[38],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[821]? = some (⟨69,(3),[9],[38],192⟩) from rfl))
private theorem rec4971 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[9,10],[46],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[822]? = some (⟨69,(3),[9,10],[46],376⟩) from rfl))
private theorem rec4982 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[9],[38],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[833]? = some (⟨69,(4),[9],[38],193⟩) from rfl))
private theorem rec4983 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[9,10],[46],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[834]? = some (⟨69,(4),[9,10],[46],377⟩) from rfl))
private theorem rec4992 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(5),[9,10],[38,46],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[843]? = some (⟨69,(5),[9,10],[38,46],189⟩) from rfl))
private theorem rec5001 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(6),[9,10],[38,46],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[852]? = some (⟨69,(6),[9,10],[38,46],260⟩) from rfl))
private theorem rec5009 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[9],[38],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[860]? = some (⟨69,(7),[9],[38],191⟩) from rfl))
private theorem rec5010 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[9,10],[46],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[861]? = some (⟨69,(7),[9,10],[46],375⟩) from rfl))
private theorem rec5019 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[9],[38],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[870]? = some (⟨69,(8),[9],[38],192⟩) from rfl))
private theorem rec5020 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[9,10],[46],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[871]? = some (⟨69,(8),[9,10],[46],376⟩) from rfl))
private theorem rec5029 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[9],[38],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[880]? = some (⟨69,(9),[9],[38],193⟩) from rfl))
private theorem rec5030 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[9,10],[46],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[881]? = some (⟨69,(9),[9,10],[46],377⟩) from rfl))
private theorem rec5039 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(10),[9,10],[38,46],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[890]? = some (⟨69,(10),[9,10],[38,46],194⟩) from rfl))
private theorem rec5048 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(11),[9,10],[38,46],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[899]? = some (⟨69,(11),[9,10],[38,46],267⟩) from rfl))
private theorem rec5056 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[9],[38],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[907]? = some (⟨69,(12),[9],[38],195⟩) from rfl))
private theorem rec5057 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[9,10],[46],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[908]? = some (⟨69,(12),[9,10],[46],378⟩) from rfl))
private theorem rec5066 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[9],[38],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[917]? = some (⟨69,(13),[9],[38],195⟩) from rfl))
private theorem rec5067 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[9,10],[46],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[918]? = some (⟨69,(13),[9,10],[46],378⟩) from rfl))
private theorem rec5076 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[9],[38],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[927]? = some (⟨69,(14),[9],[38],193⟩) from rfl))
private theorem rec5077 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[9,10],[46],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[928]? = some (⟨69,(14),[9,10],[46],377⟩) from rfl))
private theorem rec5086 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(15),[9,10],[38,46],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[937]? = some (⟨69,(15),[9,10],[38,46],196⟩) from rfl))
private theorem rec5095 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(16),[9,10],[38,46],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[946]? = some (⟨69,(16),[9,10],[38,46],269⟩) from rfl))
private theorem rec5103 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[9],[38],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[954]? = some (⟨69,(17),[9],[38],197⟩) from rfl))
private theorem rec5104 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[9,10],[46],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[955]? = some (⟨69,(17),[9,10],[46],379⟩) from rfl))
private theorem rec5113 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[9],[38],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[964]? = some (⟨69,(18),[9],[38],197⟩) from rfl))
private theorem rec5114 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[9,10],[46],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[965]? = some (⟨69,(18),[9,10],[46],379⟩) from rfl))
private theorem rec5123 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[9],[38],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[974]? = some (⟨69,(19),[9],[38],197⟩) from rfl))
private theorem rec5124 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[9,10],[46],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[975]? = some (⟨69,(19),[9,10],[46],379⟩) from rfl))
private theorem rec5133 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(20),[9,10],[38,46],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[984]? = some (⟨69,(20),[9,10],[38,46],198⟩) from rfl))
private theorem rec5142 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38, 46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(21),[9,10],[38,46],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[993]? = some (⟨69,(21),[9,10],[38,46],271⟩) from rfl))
private theorem rec5150 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[9],[38],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1001]? = some (⟨69,(22),[9],[38],199⟩) from rfl))
private theorem rec5151 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[9,10],[46],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1002]? = some (⟨69,(22),[9,10],[46],380⟩) from rfl))
private theorem rec5160 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[9],[38],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1011]? = some (⟨69,(23),[9],[38],199⟩) from rfl))
private theorem rec5161 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[9,10],[46],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1012]? = some (⟨69,(23),[9,10],[46],380⟩) from rfl))
private theorem rec5170 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[9],[38],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1021]? = some (⟨69,(24),[9],[38],199⟩) from rfl))
private theorem rec5171 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[9,10],[46],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1022]? = some (⟨69,(24),[9,10],[46],380⟩) from rfl))
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
private theorem rec5308 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[9],[38],360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1159]? = some (⟨75,(0),[9],[38],360⟩) from rfl))
private theorem rec5309 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[9,10],[46],381⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1160]? = some (⟨75,(0),[9,10],[46],381⟩) from rfl))
private theorem rec5318 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[9],[38],361⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1169]? = some (⟨75,(1),[9],[38],361⟩) from rfl))
private theorem rec5319 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[9,10],[46],382⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1170]? = some (⟨75,(1),[9,10],[46],382⟩) from rfl))
private theorem rec5328 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[9],[38],362⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1179]? = some (⟨75,(2),[9],[38],362⟩) from rfl))
private theorem rec5329 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[9,10],[46],383⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1180]? = some (⟨75,(2),[9,10],[46],383⟩) from rfl))
private theorem rec5338 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[9],[38],363⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1189]? = some (⟨75,(3),[9],[38],363⟩) from rfl))
private theorem rec5339 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[9,10],[46],384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1190]? = some (⟨75,(3),[9,10],[46],384⟩) from rfl))
private theorem rec5345 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(0),[9],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1196]? = some (⟨77,(0),[9],[46],2⟩) from rfl))
private theorem rec5346 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(0),[9],[38],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1197]? = some (⟨77,(0),[9],[38],98⟩) from rfl))
private theorem rec5353 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(1),[9],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1204]? = some (⟨77,(1),[9],[46],2⟩) from rfl))
private theorem rec5354 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(1),[9,10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1205]? = some (⟨77,(1),[9,10],[38],2⟩) from rfl))
private theorem rec5360 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(2),[9],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1211]? = some (⟨77,(2),[9],[38],2⟩) from rfl))
private theorem rec5361 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(2),[9],[46],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1212]? = some (⟨77,(2),[9],[46],29⟩) from rfl))
private theorem rec5367 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(3),[9],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1218]? = some (⟨77,(3),[9],[38],2⟩) from rfl))
private theorem rec5368 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(3),[9,10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1219]? = some (⟨77,(3),[9,10],[46],2⟩) from rfl))
private theorem rec5374 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(4),[9],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1225]? = some (⟨77,(4),[9],[46],2⟩) from rfl))
private theorem rec5375 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(4),[9],[38],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[0]? = some (⟨77,(4),[9],[38],98⟩) from rfl))
private theorem rec5381 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(5),[9],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[6]? = some (⟨77,(5),[9],[46],2⟩) from rfl))
private theorem rec5382 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(5),[9,10],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[7]? = some (⟨77,(5),[9,10],[38],2⟩) from rfl))
private theorem rec5388 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(6),[9],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[13]? = some (⟨77,(6),[9],[38],2⟩) from rfl))
private theorem rec5389 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(6),[9],[46],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[14]? = some (⟨77,(6),[9],[46],29⟩) from rfl))
private theorem rec5395 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(7),[9],[38],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[20]? = some (⟨77,(7),[9],[38],2⟩) from rfl))
private theorem rec5396 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(7),[9,10],[46],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[21]? = some (⟨77,(7),[9,10],[46],2⟩) from rfl))
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
private theorem rec5417 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(12),[9],[38],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[42]? = some (⟨77,(12),[9],[38],98⟩) from rfl))
private theorem rec5418 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(12),[9],[46],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[43]? = some (⟨77,(12),[9],[46],99⟩) from rfl))
private theorem rec5424 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 77 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(13),[9],[46],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[49]? = some (⟨77,(13),[9],[46],99⟩) from rfl))
private theorem rec5425 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 77 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(13),[9,10],[38],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[50]? = some (⟨77,(13),[9,10],[38],99⟩) from rfl))
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
private theorem rec5480 (si parent : ℕ) (hs : si ∈ ([9] : List ℕ)) (hp : parent ∈ ([46] : List ℕ)) : section14Recorded section14Catalog si parent 79 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(10),[9],[46],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[105]? = some (⟨79,(10),[9],[46],339⟩) from rfl))
private theorem rec5481 (si parent : ℕ) (hs : si ∈ ([9, 10] : List ℕ)) (hp : parent ∈ ([38] : List ℕ)) : section14Recorded section14Catalog si parent 79 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(10),[9,10],[38],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[106]? = some (⟨79,(10),[9,10],[38],339⟩) from rfl))
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
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 9).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 9)).drop 32).take 16, section14Recorded section14Catalog 9 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 9 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 9).plans.drop 3).take 1 = [⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(556,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(557,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(558,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(559,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(560,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec4582 9 32 (by decide) (by decide)
  · left
    exact rec4582 9 33 (by decide) (by decide)
  · left
    exact rec4594 9 34 (by decide) (by decide)
  · left
    exact rec4595 9 35 (by decide) (by decide)
  · left
    exact rec4582 9 36 (by decide) (by decide)
  · left
    exact rec4582 9 37 (by decide) (by decide)
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
        exact rec4611 9 38 (by decide) (by decide)
      · right
        exact rec4615 9 38 (by decide) (by decide)
      · right
        exact rec4619 9 38 (by decide) (by decide)
      · right
        exact rec4623 9 38 (by decide) (by decide)
      · right
        exact rec4627 9 38 (by decide) (by decide)
      · right
        exact rec4631 9 38 (by decide) (by decide)
      · right
        exact rec4635 9 38 (by decide) (by decide)
      · right
        exact rec4639 9 38 (by decide) (by decide)
      · right
        exact rec4643 9 38 (by decide) (by decide)
      · right
        exact rec4647 9 38 (by decide) (by decide)
      · right
        exact rec4651 9 38 (by decide) (by decide)
      · right
        exact rec4655 9 38 (by decide) (by decide)
      · right
        exact rec4659 9 38 (by decide) (by decide)
      · right
        exact rec4663 9 38 (by decide) (by decide)
      · right
        exact rec4667 9 38 (by decide) (by decide)
      · right
        exact rec4671 9 38 (by decide) (by decide)
      · right
        exact rec4675 9 38 (by decide) (by decide)
      · right
        exact rec4679 9 38 (by decide) (by decide)
      · right
        exact rec4683 9 38 (by decide) (by decide)
      · right
        exact rec4687 9 38 (by decide) (by decide)
      · right
        exact rec4691 9 38 (by decide) (by decide)
      · right
        exact rec4695 9 38 (by decide) (by decide)
      · right
        exact rec4699 9 38 (by decide) (by decide)
      · right
        exact rec4703 9 38 (by decide) (by decide)
      · right
        exact rec4707 9 38 (by decide) (by decide)
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
        exact rec16364 9 38 (by decide) (by decide)
      · right
        exact rec16369 9 38 (by decide) (by decide)
      · right
        exact rec16374 9 38 (by decide) (by decide)
      · right
        exact rec16379 9 38 (by decide) (by decide)
      · right
        exact rec16384 9 38 (by decide) (by decide)
      · right
        exact rec16389 9 38 (by decide) (by decide)
      · right
        exact rec16394 9 38 (by decide) (by decide)
      · right
        exact rec16399 9 38 (by decide) (by decide)
      · right
        exact rec16404 9 38 (by decide) (by decide)
      · right
        exact rec16409 9 38 (by decide) (by decide)
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
        exact rec4860 9 38 (by decide) (by decide)
      · right
        exact rec4863 9 38 (by decide) (by decide)
      · right
        exact rec4866 9 38 (by decide) (by decide)
      · right
        exact rec4869 9 38 (by decide) (by decide)
      · right
        exact rec4872 9 38 (by decide) (by decide)
      · right
        exact rec4875 9 38 (by decide) (by decide)
      · right
        exact rec4878 9 38 (by decide) (by decide)
      · right
        exact rec4881 9 38 (by decide) (by decide)
      · right
        exact rec4884 9 38 (by decide) (by decide)
      · right
        exact rec4887 9 38 (by decide) (by decide)
      · right
        exact rec4890 9 38 (by decide) (by decide)
      · right
        exact rec4893 9 38 (by decide) (by decide)
      · right
        exact rec4896 9 38 (by decide) (by decide)
      · right
        exact rec4899 9 38 (by decide) (by decide)
      · right
        exact rec4902 9 38 (by decide) (by decide)
      · right
        exact rec4905 9 38 (by decide) (by decide)
      · right
        exact rec4908 9 38 (by decide) (by decide)
      · right
        exact rec4911 9 38 (by decide) (by decide)
      · right
        exact rec4914 9 38 (by decide) (by decide)
      · right
        exact rec4917 9 38 (by decide) (by decide)
      · right
        exact rec4920 9 38 (by decide) (by decide)
      · right
        exact rec4923 9 38 (by decide) (by decide)
      · right
        exact rec4926 9 38 (by decide) (by decide)
      · right
        exact rec4929 9 38 (by decide) (by decide)
      · right
        exact rec4932 9 38 (by decide) (by decide)
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
        exact rec4939 9 38 (by decide) (by decide)
      · right
        exact rec4948 9 38 (by decide) (by decide)
      · right
        exact rec4958 9 38 (by decide) (by decide)
      · right
        exact rec4970 9 38 (by decide) (by decide)
      · right
        exact rec4982 9 38 (by decide) (by decide)
      · right
        exact rec4992 9 38 (by decide) (by decide)
      · right
        exact rec5001 9 38 (by decide) (by decide)
      · right
        exact rec5009 9 38 (by decide) (by decide)
      · right
        exact rec5019 9 38 (by decide) (by decide)
      · right
        exact rec5029 9 38 (by decide) (by decide)
      · right
        exact rec5039 9 38 (by decide) (by decide)
      · right
        exact rec5048 9 38 (by decide) (by decide)
      · right
        exact rec5056 9 38 (by decide) (by decide)
      · right
        exact rec5066 9 38 (by decide) (by decide)
      · right
        exact rec5076 9 38 (by decide) (by decide)
      · right
        exact rec5086 9 38 (by decide) (by decide)
      · right
        exact rec5095 9 38 (by decide) (by decide)
      · right
        exact rec5103 9 38 (by decide) (by decide)
      · right
        exact rec5113 9 38 (by decide) (by decide)
      · right
        exact rec5123 9 38 (by decide) (by decide)
      · right
        exact rec5133 9 38 (by decide) (by decide)
      · right
        exact rec5142 9 38 (by decide) (by decide)
      · right
        exact rec5150 9 38 (by decide) (by decide)
      · right
        exact rec5160 9 38 (by decide) (by decide)
      · right
        exact rec5170 9 38 (by decide) (by decide)
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
        exact rec5180 9 38 (by decide) (by decide)
      · right
        exact rec5188 9 38 (by decide) (by decide)
      · right
        exact rec5196 9 38 (by decide) (by decide)
      · right
        exact rec5204 9 38 (by decide) (by decide)
      · right
        exact rec5212 9 38 (by decide) (by decide)
      · right
        exact rec5220 9 38 (by decide) (by decide)
      · right
        exact rec5228 9 38 (by decide) (by decide)
      · right
        exact rec5236 9 38 (by decide) (by decide)
      · right
        exact rec5244 9 38 (by decide) (by decide)
      · right
        exact rec5252 9 38 (by decide) (by decide)
      · right
        exact rec5260 9 38 (by decide) (by decide)
      · right
        exact rec5268 9 38 (by decide) (by decide)
      · right
        exact rec5276 9 38 (by decide) (by decide)
      · right
        exact rec5284 9 38 (by decide) (by decide)
      · right
        exact rec5292 9 38 (by decide) (by decide)
      · right
        exact rec5300 9 38 (by decide) (by decide)
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
        exact rec5308 9 38 (by decide) (by decide)
      · right
        exact rec5318 9 38 (by decide) (by decide)
      · right
        exact rec5328 9 38 (by decide) (by decide)
      · right
        exact rec5338 9 38 (by decide) (by decide)
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
        exact rec5346 9 38 (by decide) (by decide)
      · right
        exact rec5354 9 38 (by decide) (by decide)
      · right
        exact rec5360 9 38 (by decide) (by decide)
      · right
        exact rec5367 9 38 (by decide) (by decide)
      · right
        exact rec5375 9 38 (by decide) (by decide)
      · right
        exact rec5382 9 38 (by decide) (by decide)
      · right
        exact rec5388 9 38 (by decide) (by decide)
      · right
        exact rec5395 9 38 (by decide) (by decide)
      · right
        exact rec5401 9 38 (by decide) (by decide)
      · right
        exact rec5405 9 38 (by decide) (by decide)
      · right
        exact rec5408 9 38 (by decide) (by decide)
      · right
        exact rec5412 9 38 (by decide) (by decide)
      · right
        exact rec5417 9 38 (by decide) (by decide)
      · right
        exact rec5425 9 38 (by decide) (by decide)
      · right
        exact rec5430 9 38 (by decide) (by decide)
      · right
        exact rec5436 9 38 (by decide) (by decide)
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
        exact rec5440 9 38 (by decide) (by decide)
      · right
        exact rec5443 9 38 (by decide) (by decide)
      · right
        exact rec5450 9 38 (by decide) (by decide)
      · right
        exact rec5454 9 38 (by decide) (by decide)
      · right
        exact rec5457 9 38 (by decide) (by decide)
      · right
        exact rec5460 9 38 (by decide) (by decide)
      · right
        exact rec5467 9 38 (by decide) (by decide)
      · right
        exact rec5471 9 38 (by decide) (by decide)
      · right
        exact rec5474 9 38 (by decide) (by decide)
      · right
        exact rec5477 9 38 (by decide) (by decide)
      · right
        exact rec5481 9 38 (by decide) (by decide)
      · right
        exact rec5485 9 38 (by decide) (by decide)
      · right
        exact rec5488 9 38 (by decide) (by decide)
      · right
        exact rec5491 9 38 (by decide) (by decide)
      · right
        exact rec5494 9 38 (by decide) (by decide)
      · right
        exact rec5497 9 38 (by decide) (by decide)
      · right
        exact rec5500 9 38 (by decide) (by decide)
      · right
        exact rec5503 9 38 (by decide) (by decide)
      · right
        exact rec5508 9 38 (by decide) (by decide)
      · right
        exact rec5511 9 38 (by decide) (by decide)
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
    exact rec4595 9 39 (by decide) (by decide)
  · left
    exact rec4582 9 40 (by decide) (by decide)
  · left
    exact rec4582 9 41 (by decide) (by decide)
  · left
    exact rec4596 9 42 (by decide) (by decide)
  · left
    exact rec4589 9 43 (by decide) (by decide)
  · left
    exact rec4582 9 44 (by decide) (by decide)
  · left
    exact rec4582 9 45 (by decide) (by decide)
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
        exact rec4610 9 46 (by decide) (by decide)
      · right
        exact rec4614 9 46 (by decide) (by decide)
      · right
        exact rec4618 9 46 (by decide) (by decide)
      · right
        exact rec4622 9 46 (by decide) (by decide)
      · right
        exact rec4626 9 46 (by decide) (by decide)
      · right
        exact rec4630 9 46 (by decide) (by decide)
      · right
        exact rec4634 9 46 (by decide) (by decide)
      · right
        exact rec4638 9 46 (by decide) (by decide)
      · right
        exact rec4642 9 46 (by decide) (by decide)
      · right
        exact rec4646 9 46 (by decide) (by decide)
      · right
        exact rec4650 9 46 (by decide) (by decide)
      · right
        exact rec4654 9 46 (by decide) (by decide)
      · right
        exact rec4658 9 46 (by decide) (by decide)
      · right
        exact rec4662 9 46 (by decide) (by decide)
      · right
        exact rec4666 9 46 (by decide) (by decide)
      · right
        exact rec4670 9 46 (by decide) (by decide)
      · right
        exact rec4674 9 46 (by decide) (by decide)
      · right
        exact rec4678 9 46 (by decide) (by decide)
      · right
        exact rec4682 9 46 (by decide) (by decide)
      · right
        exact rec4686 9 46 (by decide) (by decide)
      · right
        exact rec4690 9 46 (by decide) (by decide)
      · right
        exact rec4694 9 46 (by decide) (by decide)
      · right
        exact rec4698 9 46 (by decide) (by decide)
      · right
        exact rec4702 9 46 (by decide) (by decide)
      · right
        exact rec4706 9 46 (by decide) (by decide)
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
        exact rec16365 9 46 (by decide) (by decide)
      · right
        exact rec16370 9 46 (by decide) (by decide)
      · right
        exact rec16375 9 46 (by decide) (by decide)
      · right
        exact rec16380 9 46 (by decide) (by decide)
      · right
        exact rec16385 9 46 (by decide) (by decide)
      · right
        exact rec16390 9 46 (by decide) (by decide)
      · right
        exact rec16395 9 46 (by decide) (by decide)
      · right
        exact rec16400 9 46 (by decide) (by decide)
      · right
        exact rec16405 9 46 (by decide) (by decide)
      · right
        exact rec16410 9 46 (by decide) (by decide)
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
        exact rec4860 9 46 (by decide) (by decide)
      · right
        exact rec4863 9 46 (by decide) (by decide)
      · right
        exact rec4866 9 46 (by decide) (by decide)
      · right
        exact rec4869 9 46 (by decide) (by decide)
      · right
        exact rec4872 9 46 (by decide) (by decide)
      · right
        exact rec4875 9 46 (by decide) (by decide)
      · right
        exact rec4878 9 46 (by decide) (by decide)
      · right
        exact rec4881 9 46 (by decide) (by decide)
      · right
        exact rec4884 9 46 (by decide) (by decide)
      · right
        exact rec4887 9 46 (by decide) (by decide)
      · right
        exact rec4890 9 46 (by decide) (by decide)
      · right
        exact rec4893 9 46 (by decide) (by decide)
      · right
        exact rec4896 9 46 (by decide) (by decide)
      · right
        exact rec4899 9 46 (by decide) (by decide)
      · right
        exact rec4902 9 46 (by decide) (by decide)
      · right
        exact rec4905 9 46 (by decide) (by decide)
      · right
        exact rec4908 9 46 (by decide) (by decide)
      · right
        exact rec4911 9 46 (by decide) (by decide)
      · right
        exact rec4914 9 46 (by decide) (by decide)
      · right
        exact rec4917 9 46 (by decide) (by decide)
      · right
        exact rec4920 9 46 (by decide) (by decide)
      · right
        exact rec4923 9 46 (by decide) (by decide)
      · right
        exact rec4926 9 46 (by decide) (by decide)
      · right
        exact rec4929 9 46 (by decide) (by decide)
      · right
        exact rec4932 9 46 (by decide) (by decide)
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
        exact rec4939 9 46 (by decide) (by decide)
      · right
        exact rec4948 9 46 (by decide) (by decide)
      · right
        exact rec4959 9 46 (by decide) (by decide)
      · right
        exact rec4971 9 46 (by decide) (by decide)
      · right
        exact rec4983 9 46 (by decide) (by decide)
      · right
        exact rec4992 9 46 (by decide) (by decide)
      · right
        exact rec5001 9 46 (by decide) (by decide)
      · right
        exact rec5010 9 46 (by decide) (by decide)
      · right
        exact rec5020 9 46 (by decide) (by decide)
      · right
        exact rec5030 9 46 (by decide) (by decide)
      · right
        exact rec5039 9 46 (by decide) (by decide)
      · right
        exact rec5048 9 46 (by decide) (by decide)
      · right
        exact rec5057 9 46 (by decide) (by decide)
      · right
        exact rec5067 9 46 (by decide) (by decide)
      · right
        exact rec5077 9 46 (by decide) (by decide)
      · right
        exact rec5086 9 46 (by decide) (by decide)
      · right
        exact rec5095 9 46 (by decide) (by decide)
      · right
        exact rec5104 9 46 (by decide) (by decide)
      · right
        exact rec5114 9 46 (by decide) (by decide)
      · right
        exact rec5124 9 46 (by decide) (by decide)
      · right
        exact rec5133 9 46 (by decide) (by decide)
      · right
        exact rec5142 9 46 (by decide) (by decide)
      · right
        exact rec5151 9 46 (by decide) (by decide)
      · right
        exact rec5161 9 46 (by decide) (by decide)
      · right
        exact rec5171 9 46 (by decide) (by decide)
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
        exact rec5181 9 46 (by decide) (by decide)
      · right
        exact rec5189 9 46 (by decide) (by decide)
      · right
        exact rec5197 9 46 (by decide) (by decide)
      · right
        exact rec5205 9 46 (by decide) (by decide)
      · right
        exact rec5213 9 46 (by decide) (by decide)
      · right
        exact rec5221 9 46 (by decide) (by decide)
      · right
        exact rec5229 9 46 (by decide) (by decide)
      · right
        exact rec5237 9 46 (by decide) (by decide)
      · right
        exact rec5245 9 46 (by decide) (by decide)
      · right
        exact rec5253 9 46 (by decide) (by decide)
      · right
        exact rec5261 9 46 (by decide) (by decide)
      · right
        exact rec5269 9 46 (by decide) (by decide)
      · right
        exact rec5277 9 46 (by decide) (by decide)
      · right
        exact rec5285 9 46 (by decide) (by decide)
      · right
        exact rec5293 9 46 (by decide) (by decide)
      · right
        exact rec5301 9 46 (by decide) (by decide)
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
        exact rec5309 9 46 (by decide) (by decide)
      · right
        exact rec5319 9 46 (by decide) (by decide)
      · right
        exact rec5329 9 46 (by decide) (by decide)
      · right
        exact rec5339 9 46 (by decide) (by decide)
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
        exact rec5345 9 46 (by decide) (by decide)
      · right
        exact rec5353 9 46 (by decide) (by decide)
      · right
        exact rec5361 9 46 (by decide) (by decide)
      · right
        exact rec5368 9 46 (by decide) (by decide)
      · right
        exact rec5374 9 46 (by decide) (by decide)
      · right
        exact rec5381 9 46 (by decide) (by decide)
      · right
        exact rec5389 9 46 (by decide) (by decide)
      · right
        exact rec5396 9 46 (by decide) (by decide)
      · right
        exact rec5400 9 46 (by decide) (by decide)
      · right
        exact rec5404 9 46 (by decide) (by decide)
      · right
        exact rec5409 9 46 (by decide) (by decide)
      · right
        exact rec5413 9 46 (by decide) (by decide)
      · right
        exact rec5418 9 46 (by decide) (by decide)
      · right
        exact rec5424 9 46 (by decide) (by decide)
      · right
        exact rec5431 9 46 (by decide) (by decide)
      · right
        exact rec5437 9 46 (by decide) (by decide)
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
        exact rec5440 9 46 (by decide) (by decide)
      · right
        exact rec5443 9 46 (by decide) (by decide)
      · right
        exact rec5451 9 46 (by decide) (by decide)
      · right
        exact rec5454 9 46 (by decide) (by decide)
      · right
        exact rec5457 9 46 (by decide) (by decide)
      · right
        exact rec5460 9 46 (by decide) (by decide)
      · right
        exact rec5468 9 46 (by decide) (by decide)
      · right
        exact rec5471 9 46 (by decide) (by decide)
      · right
        exact rec5474 9 46 (by decide) (by decide)
      · right
        exact rec5477 9 46 (by decide) (by decide)
      · right
        exact rec5480 9 46 (by decide) (by decide)
      · right
        exact rec5485 9 46 (by decide) (by decide)
      · right
        exact rec5488 9 46 (by decide) (by decide)
      · right
        exact rec5491 9 46 (by decide) (by decide)
      · right
        exact rec5494 9 46 (by decide) (by decide)
      · right
        exact rec5497 9 46 (by decide) (by decide)
      · right
        exact rec5500 9 46 (by decide) (by decide)
      · right
        exact rec5503 9 46 (by decide) (by decide)
      · right
        exact rec5508 9 46 (by decide) (by decide)
      · right
        exact rec5511 9 46 (by decide) (by decide)
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
    exact rec4590 9 47 (by decide) (by decide)
end Section14Coverage_9_3_p32_48

#print axioms solution
