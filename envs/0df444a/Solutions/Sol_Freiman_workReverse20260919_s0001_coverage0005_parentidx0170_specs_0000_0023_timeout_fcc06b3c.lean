-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_coverage0005_parentidx0170_specs_0000_0023_timeout_fcc06b3c
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T23:39:54.526108+00:00
-- url     : https://prove2.me/submissions/56871cd2-7f88-4dff-a4b7-1102875430fe

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
namespace Section14CoverageSpec_1_5_p170_0_23
private theorem rec7440 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(0),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[908]? = some (⟨155,(0),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7443 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(1),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[911]? = some (⟨155,(1),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7446 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(2),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[914]? = some (⟨155,(2),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7449 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(3),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[917]? = some (⟨155,(3),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7452 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(4),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[920]? = some (⟨155,(4),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7455 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(5),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[923]? = some (⟨155,(5),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(6),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[926]? = some (⟨155,(6),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7461 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[929]? = some (⟨155,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7464 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(8),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[932]? = some (⟨155,(8),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7467 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(9),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[935]? = some (⟨155,(9),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7470 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(10),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[938]? = some (⟨155,(10),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7473 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(11),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[941]? = some (⟨155,(11),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7476 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(12),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[944]? = some (⟨155,(12),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7479 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(13),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[947]? = some (⟨155,(13),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7482 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(14),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[950]? = some (⟨155,(14),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7485 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(15),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[953]? = some (⟨155,(15),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7488 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(16),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[956]? = some (⟨155,(16),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7491 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(17),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[959]? = some (⟨155,(17),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7494 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(18),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[962]? = some (⟨155,(18),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7497 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(19),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[965]? = some (⟨155,(19),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7500 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(20),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[968]? = some (⟨155,(20),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7503 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(21),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[971]? = some (⟨155,(21),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(22),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[974]? = some (⟨155,(22),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7509 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(23),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[977]? = some (⟨155,(23),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7512 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(24),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[980]? = some (⟨155,(24),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7515 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(0),[1,2,5,6,13,14],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[983]? = some (⟨157,(0),[1,2,5,6,13,14],[170],10⟩) from rfl))
private theorem rec7519 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(1),[1,2,5,6,13,14],[170],393⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[987]? = some (⟨157,(1),[1,2,5,6,13,14],[170],393⟩) from rfl))
private theorem rec7524 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(2),[1,2,5,6,13,14],[170],394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[992]? = some (⟨157,(2),[1,2,5,6,13,14],[170],394⟩) from rfl))
private theorem rec7529 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(3),[1,2,5,6,13,14],[170],395⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[997]? = some (⟨157,(3),[1,2,5,6,13,14],[170],395⟩) from rfl))
private theorem rec7534 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(4),[1,2,5,6,13,14],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1002]? = some (⟨157,(4),[1,2,5,6,13,14],[170],396⟩) from rfl))
private theorem rec7539 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(5),[1,2,5,6,13,14],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1007]? = some (⟨157,(5),[1,2,5,6,13,14],[170],10⟩) from rfl))
private theorem rec7543 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(6),[1,2,5,6,13,14],[170],393⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1011]? = some (⟨157,(6),[1,2,5,6,13,14],[170],393⟩) from rfl))
private theorem rec7548 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(7),[1,2,5,6,13,14],[170],394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1016]? = some (⟨157,(7),[1,2,5,6,13,14],[170],394⟩) from rfl))
private theorem rec7553 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(8),[1,2,5,6,13,14],[170],395⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1021]? = some (⟨157,(8),[1,2,5,6,13,14],[170],395⟩) from rfl))
private theorem rec7558 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(9),[1,2,5,6,13,14],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1026]? = some (⟨157,(9),[1,2,5,6,13,14],[170],396⟩) from rfl))
private theorem rec7563 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(10),[1,2,5,6,13,14],[170],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1031]? = some (⟨157,(10),[1,2,5,6,13,14],[170],18⟩) from rfl))
private theorem rec7567 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(11),[1,2,5,6,13,14],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1035]? = some (⟨157,(11),[1,2,5,6,13,14],[170],397⟩) from rfl))
private theorem rec7572 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(12),[1,2,5,6,13,14],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1040]? = some (⟨157,(12),[1,2,5,6,13,14],[170],397⟩) from rfl))
private theorem rec7577 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(13),[1,2,5,6,13,14],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1045]? = some (⟨157,(13),[1,2,5,6,13,14],[170],397⟩) from rfl))
private theorem rec7582 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(14),[1,2,5,6,13,14],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1050]? = some (⟨157,(14),[1,2,5,6,13,14],[170],396⟩) from rfl))
private theorem rec7587 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(15),[1,2,5,6,13,14],[170],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1055]? = some (⟨157,(15),[1,2,5,6,13,14],[170],21⟩) from rfl))
private theorem rec7591 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(16),[1,2,5,6,13,14],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1059]? = some (⟨157,(16),[1,2,5,6,13,14],[170],398⟩) from rfl))
private theorem rec7596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(17),[1,2,5,6,13,14],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1064]? = some (⟨157,(17),[1,2,5,6,13,14],[170],398⟩) from rfl))
private theorem rec7601 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(18),[1,2,5,6,13,14],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1069]? = some (⟨157,(18),[1,2,5,6,13,14],[170],398⟩) from rfl))
private theorem rec7606 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(19),[1,2,5,6,13,14],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1074]? = some (⟨157,(19),[1,2,5,6,13,14],[170],398⟩) from rfl))
private theorem rec7611 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(20),[1,2,5,6,13,14],[170],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1079]? = some (⟨157,(20),[1,2,5,6,13,14],[170],24⟩) from rfl))
private theorem rec7615 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(21),[1,2,5,6,13,14],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1083]? = some (⟨157,(21),[1,2,5,6,13,14],[170],399⟩) from rfl))
private theorem rec7620 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(22),[1,2,5,6,13,14],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1088]? = some (⟨157,(22),[1,2,5,6,13,14],[170],399⟩) from rfl))
private theorem rec7625 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(23),[1,2,5,6,13,14],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1093]? = some (⟨157,(23),[1,2,5,6,13,14],[170],399⟩) from rfl))
private theorem rec7630 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(24),[1,2,5,6,13,14],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1098]? = some (⟨157,(24),[1,2,5,6,13,14],[170],399⟩) from rfl))
private theorem rec7635 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(0),[1,2,5,6,13,14],[170],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1103]? = some (⟨160,(0),[1,2,5,6,13,14],[170],638⟩) from rfl))
private theorem rec7642 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(1),[1,2,5,6,13,14],[170],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1110]? = some (⟨160,(1),[1,2,5,6,13,14],[170],639⟩) from rfl))
private theorem rec7649 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(2),[1,2,5,6,13,14],[170],640⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1117]? = some (⟨160,(2),[1,2,5,6,13,14],[170],640⟩) from rfl))
private theorem rec7656 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(3),[1,2,5,6,13,14],[170],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1124]? = some (⟨160,(3),[1,2,5,6,13,14],[170],641⟩) from rfl))
private theorem rec7663 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(4),[1,2,5,6,13,14],[170],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1131]? = some (⟨160,(4),[1,2,5,6,13,14],[170],638⟩) from rfl))
private theorem rec7670 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(5),[1,2,5,6,13,14],[170],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1138]? = some (⟨160,(5),[1,2,5,6,13,14],[170],639⟩) from rfl))
private theorem rec7677 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(6),[1,2,5,6,13,14],[170],642⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1145]? = some (⟨160,(6),[1,2,5,6,13,14],[170],642⟩) from rfl))
private theorem rec7684 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(7),[1,2,5,6,13,14],[170],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[0]? = some (⟨160,(7),[1,2,5,6,13,14],[170],641⟩) from rfl))
private theorem rec7691 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(8),[1,2,5,6,13,14],[170],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[7]? = some (⟨160,(8),[1,2,5,6,13,14],[170],638⟩) from rfl))
private theorem rec7698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(9),[1,2,5,6,13,14],[170],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[14]? = some (⟨160,(9),[1,2,5,6,13,14],[170],639⟩) from rfl))
private theorem rec7705 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(10),[1,2,5,6,13,14],[170],640⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[21]? = some (⟨160,(10),[1,2,5,6,13,14],[170],640⟩) from rfl))
private theorem rec7712 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(11),[1,2,5,6,13,14],[170],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[28]? = some (⟨160,(11),[1,2,5,6,13,14],[170],641⟩) from rfl))
private theorem rec7719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(12),[1,2,5,6,13,14],[170],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[35]? = some (⟨160,(12),[1,2,5,6,13,14],[170],638⟩) from rfl))
private theorem rec7726 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(13),[1,2,5,6,13,14],[170],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[42]? = some (⟨160,(13),[1,2,5,6,13,14],[170],639⟩) from rfl))
private theorem rec7733 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(14),[1,2,5,6,13,14],[170],643⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[49]? = some (⟨160,(14),[1,2,5,6,13,14],[170],643⟩) from rfl))
private theorem rec7740 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(15),[1,2,5,6,13,14],[170],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[56]? = some (⟨160,(15),[1,2,5,6,13,14],[170],641⟩) from rfl))
private theorem rec7747 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(0),[1,2,5,6,13,14],[170],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[63]? = some (⟨163,(0),[1,2,5,6,13,14],[170],406⟩) from rfl))
private theorem rec7755 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(1),[1,2,5,6,13,14],[170],407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[71]? = some (⟨163,(1),[1,2,5,6,13,14],[170],407⟩) from rfl))
private theorem rec7763 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(2),[1,2,5,6,13,14],[170],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[79]? = some (⟨163,(2),[1,2,5,6,13,14],[170],406⟩) from rfl))
private theorem rec7771 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(3),[1,2,5,6,13,14],[170],408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[87]? = some (⟨163,(3),[1,2,5,6,13,14],[170],408⟩) from rfl))
private theorem rec7779 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(4),[1,2,5,6,13,14],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[95]? = some (⟨163,(4),[1,2,5,6,13,14],[170],409⟩) from rfl))
private theorem rec7787 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(5),[1,2,5,6,13,14],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[103]? = some (⟨163,(5),[1,2,5,6,13,14],[170],409⟩) from rfl))
private theorem rec7795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(6),[1,2,5,6,13,14],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[111]? = some (⟨163,(6),[1,2,5,6,13,14],[170],409⟩) from rfl))
private theorem rec7803 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(7),[1,2,5,6,13,14],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[119]? = some (⟨163,(7),[1,2,5,6,13,14],[170],409⟩) from rfl))
private theorem rec7811 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(8),[1,2,5,6,13,14],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[127]? = some (⟨163,(8),[1,2,5,6,13,14],[170],410⟩) from rfl))
private theorem rec7819 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(9),[1,2,5,6,13,14],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[135]? = some (⟨163,(9),[1,2,5,6,13,14],[170],410⟩) from rfl))
private theorem rec7827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(10),[1,2,5,6,13,14],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[143]? = some (⟨163,(10),[1,2,5,6,13,14],[170],410⟩) from rfl))
private theorem rec7835 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(11),[1,2,5,6,13,14],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[151]? = some (⟨163,(11),[1,2,5,6,13,14],[170],410⟩) from rfl))
private theorem rec7843 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(12),[1,2,5,6,13,14],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[159]? = some (⟨163,(12),[1,2,5,6,13,14],[170],411⟩) from rfl))
private theorem rec7851 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(13),[1,2,5,6,13,14],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[167]? = some (⟨163,(13),[1,2,5,6,13,14],[170],411⟩) from rfl))
private theorem rec7859 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(14),[1,2,5,6,13,14],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[175]? = some (⟨163,(14),[1,2,5,6,13,14],[170],411⟩) from rfl))
private theorem rec7867 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(15),[1,2,5,6,13,14],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[183]? = some (⟨163,(15),[1,2,5,6,13,14],[170],411⟩) from rfl))
private theorem rec7875 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(0),[1,2,5,6,13,14],[170],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[191]? = some (⟨166,(0),[1,2,5,6,13,14],[170],644⟩) from rfl))
private theorem rec7882 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(1),[1,2,5,6,13,14],[170],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[198]? = some (⟨166,(1),[1,2,5,6,13,14],[170],644⟩) from rfl))
private theorem rec7889 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(2),[1,2,5,6,13,14],[170],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[205]? = some (⟨166,(2),[1,2,5,6,13,14],[170],644⟩) from rfl))
private theorem rec7896 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(3),[1,2,5,6,13,14],[170],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[212]? = some (⟨166,(3),[1,2,5,6,13,14],[170],644⟩) from rfl))
private theorem rec7903 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(4),[1,2,5,6,13,14],[170],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[219]? = some (⟨166,(4),[1,2,5,6,13,14],[170],645⟩) from rfl))
private theorem rec7910 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(5),[1,2,5,6,13,14],[170],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[226]? = some (⟨166,(5),[1,2,5,6,13,14],[170],645⟩) from rfl))
private theorem rec7917 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(6),[1,2,5,6,13,14],[170],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[233]? = some (⟨166,(6),[1,2,5,6,13,14],[170],645⟩) from rfl))
private theorem rec7924 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(7),[1,2,5,6,13,14],[170],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[240]? = some (⟨166,(7),[1,2,5,6,13,14],[170],645⟩) from rfl))
private theorem rec7931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(8),[1,2,5,6,13,14],[170],646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[247]? = some (⟨166,(8),[1,2,5,6,13,14],[170],646⟩) from rfl))
private theorem rec7938 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(9),[1,2,5,6,13,14],[170],647⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[254]? = some (⟨166,(9),[1,2,5,6,13,14],[170],647⟩) from rfl))
private theorem rec7945 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(10),[1,2,5,6,13,14],[170],646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[261]? = some (⟨166,(10),[1,2,5,6,13,14],[170],646⟩) from rfl))
private theorem rec7952 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[268]? = some (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) from rfl))
private theorem rec7959 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[275]? = some (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) from rfl))
private theorem rec7966 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[282]? = some (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) from rfl))
private theorem rec7973 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[289]? = some (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) from rfl))
private theorem rec7980 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[296]? = some (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) from rfl))
private theorem rec7987 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[303]? = some (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) from rfl))
private theorem rec7995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[311]? = some (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) from rfl))
private theorem rec8003 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[319]? = some (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) from rfl))
private theorem rec8011 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[327]? = some (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) from rfl))
private theorem rec8019 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[335]? = some (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) from rfl))
private theorem rec8027 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[343]? = some (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) from rfl))
private theorem rec8035 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[351]? = some (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) from rfl))
private theorem rec8043 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[359]? = some (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) from rfl))
private theorem rec8051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[367]? = some (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) from rfl))
private theorem rec8059 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[375]? = some (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) from rfl))
private theorem rec8067 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[383]? = some (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) from rfl))
private theorem rec8075 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[391]? = some (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) from rfl))
private theorem rec8083 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[399]? = some (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) from rfl))
private theorem rec8091 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[407]? = some (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) from rfl))
private theorem rec8099 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[415]? = some (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) from rfl))
private theorem rec8107 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[423]? = some (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) from rfl))
private theorem rec8115 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 171 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[431]? = some (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) from rfl))
private theorem rec8122 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 171 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[438]? = some (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) from rfl))
private theorem rec8129 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 171 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[445]? = some (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) from rfl))
private theorem rec8136 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 171 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[452]? = some (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) from rfl))
private theorem rec8143 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[459]? = some (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) from rfl))
private theorem rec8151 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[467]? = some (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) from rfl))
private theorem rec8159 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[475]? = some (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) from rfl))
private theorem rec8167 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[483]? = some (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) from rfl))
private theorem rec8175 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[491]? = some (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) from rfl))
private theorem rec8183 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[499]? = some (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) from rfl))
private theorem rec8191 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[507]? = some (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) from rfl))
private theorem rec8199 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[515]? = some (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) from rfl))
private theorem rec8207 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[523]? = some (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) from rfl))
private theorem rec8215 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[531]? = some (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) from rfl))
private theorem rec8223 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[539]? = some (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) from rfl))
private theorem rec8231 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[547]? = some (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) from rfl))
private theorem rec8239 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[555]? = some (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) from rfl))
private theorem rec8247 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[563]? = some (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) from rfl))
private theorem rec8255 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[571]? = some (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) from rfl))
private theorem rec8263 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[579]? = some (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) from rfl))
private theorem rec8271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[587]? = some (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) from rfl))
private theorem rec8278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[594]? = some (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) from rfl))
private theorem rec8285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(2),[1,2,5,6,13,14],[170],656⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[601]? = some (⟨175,(2),[1,2,5,6,13,14],[170],656⟩) from rfl))
private theorem rec8292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(3),[1,2,5,6,13,14],[170],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[608]? = some (⟨175,(3),[1,2,5,6,13,14],[170],657⟩) from rfl))
private theorem rec8299 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(4),[1,2,5,6,13,14],[170],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[0]? = some (⟨175,(4),[1,2,5,6,13,14],[170],654⟩) from rfl))
private theorem rec8306 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(5),[1,2,5,6,13,14],[170],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[7]? = some (⟨175,(5),[1,2,5,6,13,14],[170],655⟩) from rfl))
private theorem rec8313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(6),[1,2,5,6,13,14],[170],658⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[14]? = some (⟨175,(6),[1,2,5,6,13,14],[170],658⟩) from rfl))
private theorem rec8320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(7),[1,2,5,6,13,14],[170],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[21]? = some (⟨175,(7),[1,2,5,6,13,14],[170],657⟩) from rfl))
private theorem rec8327 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(8),[1,2,5,6,13,14],[170],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[28]? = some (⟨175,(8),[1,2,5,6,13,14],[170],654⟩) from rfl))
private theorem rec8334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(9),[1,2,5,6,13,14],[170],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[35]? = some (⟨175,(9),[1,2,5,6,13,14],[170],655⟩) from rfl))
private theorem rec8341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(10),[1,2,5,6,13,14],[170],656⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[42]? = some (⟨175,(10),[1,2,5,6,13,14],[170],656⟩) from rfl))
private theorem rec8348 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(11),[1,2,5,6,13,14],[170],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[49]? = some (⟨175,(11),[1,2,5,6,13,14],[170],657⟩) from rfl))
private theorem rec8355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(12),[1,2,5,6,13,14],[170],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[56]? = some (⟨175,(12),[1,2,5,6,13,14],[170],654⟩) from rfl))
private theorem rec8362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(13),[1,2,5,6,13,14],[170],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[63]? = some (⟨175,(13),[1,2,5,6,13,14],[170],655⟩) from rfl))
private theorem rec8369 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(14),[1,2,5,6,13,14],[170],659⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[70]? = some (⟨175,(14),[1,2,5,6,13,14],[170],659⟩) from rfl))
private theorem rec8376 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(15),[1,2,5,6,13,14],[170],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[77]? = some (⟨175,(15),[1,2,5,6,13,14],[170],657⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 170 gs.1 j := by
  have hp : ((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 0).take 23) = [(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 154)).length = 16 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 155)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec7440 1 170 (by decide) (by decide)
    · right
      exact rec7443 1 170 (by decide) (by decide)
    · right
      exact rec7446 1 170 (by decide) (by decide)
    · right
      exact rec7449 1 170 (by decide) (by decide)
    · right
      exact rec7452 1 170 (by decide) (by decide)
    · right
      exact rec7455 1 170 (by decide) (by decide)
    · right
      exact rec7458 1 170 (by decide) (by decide)
    · right
      exact rec7461 1 170 (by decide) (by decide)
    · right
      exact rec7464 1 170 (by decide) (by decide)
    · right
      exact rec7467 1 170 (by decide) (by decide)
    · right
      exact rec7470 1 170 (by decide) (by decide)
    · right
      exact rec7473 1 170 (by decide) (by decide)
    · right
      exact rec7476 1 170 (by decide) (by decide)
    · right
      exact rec7479 1 170 (by decide) (by decide)
    · right
      exact rec7482 1 170 (by decide) (by decide)
    · right
      exact rec7485 1 170 (by decide) (by decide)
    · right
      exact rec7488 1 170 (by decide) (by decide)
    · right
      exact rec7491 1 170 (by decide) (by decide)
    · right
      exact rec7494 1 170 (by decide) (by decide)
    · right
      exact rec7497 1 170 (by decide) (by decide)
    · right
      exact rec7500 1 170 (by decide) (by decide)
    · right
      exact rec7503 1 170 (by decide) (by decide)
    · right
      exact rec7506 1 170 (by decide) (by decide)
    · right
      exact rec7509 1 170 (by decide) (by decide)
    · right
      exact rec7512 1 170 (by decide) (by decide)
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 157)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec7515 1 170 (by decide) (by decide)
    · right
      exact rec7519 1 170 (by decide) (by decide)
    · right
      exact rec7524 1 170 (by decide) (by decide)
    · right
      exact rec7529 1 170 (by decide) (by decide)
    · right
      exact rec7534 1 170 (by decide) (by decide)
    · right
      exact rec7539 1 170 (by decide) (by decide)
    · right
      exact rec7543 1 170 (by decide) (by decide)
    · right
      exact rec7548 1 170 (by decide) (by decide)
    · right
      exact rec7553 1 170 (by decide) (by decide)
    · right
      exact rec7558 1 170 (by decide) (by decide)
    · right
      exact rec7563 1 170 (by decide) (by decide)
    · right
      exact rec7567 1 170 (by decide) (by decide)
    · right
      exact rec7572 1 170 (by decide) (by decide)
    · right
      exact rec7577 1 170 (by decide) (by decide)
    · right
      exact rec7582 1 170 (by decide) (by decide)
    · right
      exact rec7587 1 170 (by decide) (by decide)
    · right
      exact rec7591 1 170 (by decide) (by decide)
    · right
      exact rec7596 1 170 (by decide) (by decide)
    · right
      exact rec7601 1 170 (by decide) (by decide)
    · right
      exact rec7606 1 170 (by decide) (by decide)
    · right
      exact rec7611 1 170 (by decide) (by decide)
    · right
      exact rec7615 1 170 (by decide) (by decide)
    · right
      exact rec7620 1 170 (by decide) (by decide)
    · right
      exact rec7625 1 170 (by decide) (by decide)
    · right
      exact rec7630 1 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 158)).length = 25 := by decide +kernel
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
      exact rec7635 1 170 (by decide) (by decide)
    · right
      exact rec7642 1 170 (by decide) (by decide)
    · right
      exact rec7649 1 170 (by decide) (by decide)
    · right
      exact rec7656 1 170 (by decide) (by decide)
    · right
      exact rec7663 1 170 (by decide) (by decide)
    · right
      exact rec7670 1 170 (by decide) (by decide)
    · right
      exact rec7677 1 170 (by decide) (by decide)
    · right
      exact rec7684 1 170 (by decide) (by decide)
    · right
      exact rec7691 1 170 (by decide) (by decide)
    · right
      exact rec7698 1 170 (by decide) (by decide)
    · right
      exact rec7705 1 170 (by decide) (by decide)
    · right
      exact rec7712 1 170 (by decide) (by decide)
    · right
      exact rec7719 1 170 (by decide) (by decide)
    · right
      exact rec7726 1 170 (by decide) (by decide)
    · right
      exact rec7733 1 170 (by decide) (by decide)
    · right
      exact rec7740 1 170 (by decide) (by decide)
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
      exact rec7747 1 170 (by decide) (by decide)
    · right
      exact rec7755 1 170 (by decide) (by decide)
    · right
      exact rec7763 1 170 (by decide) (by decide)
    · right
      exact rec7771 1 170 (by decide) (by decide)
    · right
      exact rec7779 1 170 (by decide) (by decide)
    · right
      exact rec7787 1 170 (by decide) (by decide)
    · right
      exact rec7795 1 170 (by decide) (by decide)
    · right
      exact rec7803 1 170 (by decide) (by decide)
    · right
      exact rec7811 1 170 (by decide) (by decide)
    · right
      exact rec7819 1 170 (by decide) (by decide)
    · right
      exact rec7827 1 170 (by decide) (by decide)
    · right
      exact rec7835 1 170 (by decide) (by decide)
    · right
      exact rec7843 1 170 (by decide) (by decide)
    · right
      exact rec7851 1 170 (by decide) (by decide)
    · right
      exact rec7859 1 170 (by decide) (by decide)
    · right
      exact rec7867 1 170 (by decide) (by decide)
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
      exact rec7875 1 170 (by decide) (by decide)
    · right
      exact rec7882 1 170 (by decide) (by decide)
    · right
      exact rec7889 1 170 (by decide) (by decide)
    · right
      exact rec7896 1 170 (by decide) (by decide)
    · right
      exact rec7903 1 170 (by decide) (by decide)
    · right
      exact rec7910 1 170 (by decide) (by decide)
    · right
      exact rec7917 1 170 (by decide) (by decide)
    · right
      exact rec7924 1 170 (by decide) (by decide)
    · right
      exact rec7931 1 170 (by decide) (by decide)
    · right
      exact rec7938 1 170 (by decide) (by decide)
    · right
      exact rec7945 1 170 (by decide) (by decide)
    · right
      exact rec7952 1 170 (by decide) (by decide)
    · right
      exact rec7959 1 170 (by decide) (by decide)
    · right
      exact rec7966 1 170 (by decide) (by decide)
    · right
      exact rec7973 1 170 (by decide) (by decide)
    · right
      exact rec7980 1 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 167)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec7987 1 170 (by decide) (by decide)
    · right
      exact rec7995 1 170 (by decide) (by decide)
    · right
      exact rec8003 1 170 (by decide) (by decide)
    · right
      exact rec8011 1 170 (by decide) (by decide)
    · right
      exact rec8019 1 170 (by decide) (by decide)
    · right
      exact rec8027 1 170 (by decide) (by decide)
    · right
      exact rec8035 1 170 (by decide) (by decide)
    · right
      exact rec8043 1 170 (by decide) (by decide)
    · right
      exact rec8051 1 170 (by decide) (by decide)
    · right
      exact rec8059 1 170 (by decide) (by decide)
    · right
      exact rec8067 1 170 (by decide) (by decide)
    · right
      exact rec8075 1 170 (by decide) (by decide)
    · right
      exact rec8083 1 170 (by decide) (by decide)
    · right
      exact rec8091 1 170 (by decide) (by decide)
    · right
      exact rec8099 1 170 (by decide) (by decide)
    · right
      exact rec8107 1 170 (by decide) (by decide)
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
      exact rec8115 1 170 (by decide) (by decide)
    · right
      exact rec8122 1 170 (by decide) (by decide)
    · right
      exact rec8129 1 170 (by decide) (by decide)
    · right
      exact rec8136 1 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 172)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec8143 1 170 (by decide) (by decide)
    · right
      exact rec8151 1 170 (by decide) (by decide)
    · right
      exact rec8159 1 170 (by decide) (by decide)
    · right
      exact rec8167 1 170 (by decide) (by decide)
    · right
      exact rec8175 1 170 (by decide) (by decide)
    · right
      exact rec8183 1 170 (by decide) (by decide)
    · right
      exact rec8191 1 170 (by decide) (by decide)
    · right
      exact rec8199 1 170 (by decide) (by decide)
    · right
      exact rec8207 1 170 (by decide) (by decide)
    · right
      exact rec8215 1 170 (by decide) (by decide)
    · right
      exact rec8223 1 170 (by decide) (by decide)
    · right
      exact rec8231 1 170 (by decide) (by decide)
    · right
      exact rec8239 1 170 (by decide) (by decide)
    · right
      exact rec8247 1 170 (by decide) (by decide)
    · right
      exact rec8255 1 170 (by decide) (by decide)
    · right
      exact rec8263 1 170 (by decide) (by decide)
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
      exact rec8271 1 170 (by decide) (by decide)
    · right
      exact rec8278 1 170 (by decide) (by decide)
    · right
      exact rec8285 1 170 (by decide) (by decide)
    · right
      exact rec8292 1 170 (by decide) (by decide)
    · right
      exact rec8299 1 170 (by decide) (by decide)
    · right
      exact rec8306 1 170 (by decide) (by decide)
    · right
      exact rec8313 1 170 (by decide) (by decide)
    · right
      exact rec8320 1 170 (by decide) (by decide)
    · right
      exact rec8327 1 170 (by decide) (by decide)
    · right
      exact rec8334 1 170 (by decide) (by decide)
    · right
      exact rec8341 1 170 (by decide) (by decide)
    · right
      exact rec8348 1 170 (by decide) (by decide)
    · right
      exact rec8355 1 170 (by decide) (by decide)
    · right
      exact rec8362 1 170 (by decide) (by decide)
    · right
      exact rec8369 1 170 (by decide) (by decide)
    · right
      exact rec8376 1 170 (by decide) (by decide)
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
end Section14CoverageSpec_1_5_p170_0_23

#print axioms solution
