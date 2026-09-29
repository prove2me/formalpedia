-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_coverage0005_parentidx0174_specs_0046_0069_ancestor_d2c19c6b
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T04:34:29.405946+00:00
-- url     : https://prove2.me/submissions/4db55a6b-d109-4aee-827f-4918abb1a593

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
namespace Section14CoverageSpec_6_5_p174_46_69
private theorem rec9639 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(0),[5,6],[174],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[121]? = some (⟨200,(0),[5,6],[174],704⟩) from rfl))
private theorem rec9646 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(1),[5,6],[174],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[128]? = some (⟨200,(1),[5,6],[174],704⟩) from rfl))
private theorem rec9653 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(2),[5,6],[174],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[135]? = some (⟨200,(2),[5,6],[174],704⟩) from rfl))
private theorem rec9660 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(3),[5,6],[174],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[142]? = some (⟨200,(3),[5,6],[174],704⟩) from rfl))
private theorem rec9667 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(4),[5,6],[174],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[149]? = some (⟨200,(4),[5,6],[174],704⟩) from rfl))
private theorem rec9674 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(5),[5,6],[174],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[156]? = some (⟨200,(5),[5,6],[174],705⟩) from rfl))
private theorem rec9681 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(6),[5,6],[174],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[163]? = some (⟨200,(6),[5,6],[174],705⟩) from rfl))
private theorem rec9688 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(7),[5,6],[174],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[170]? = some (⟨200,(7),[5,6],[174],705⟩) from rfl))
private theorem rec9695 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(8),[5,6],[174],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[177]? = some (⟨200,(8),[5,6],[174],705⟩) from rfl))
private theorem rec9702 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(9),[5,6],[174],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[184]? = some (⟨200,(9),[5,6],[174],705⟩) from rfl))
private theorem rec9709 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(10),[5,6],[174],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[191]? = some (⟨200,(10),[5,6],[174],706⟩) from rfl))
private theorem rec9716 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(11),[5,6],[174],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[198]? = some (⟨200,(11),[5,6],[174],707⟩) from rfl))
private theorem rec9723 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(12),[5,6],[174],708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[205]? = some (⟨200,(12),[5,6],[174],708⟩) from rfl))
private theorem rec9730 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(13),[5,6],[174],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[212]? = some (⟨200,(13),[5,6],[174],707⟩) from rfl))
private theorem rec9737 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(14),[5,6],[174],709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[219]? = some (⟨200,(14),[5,6],[174],709⟩) from rfl))
private theorem rec9744 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(15),[5,6],[174],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[226]? = some (⟨200,(15),[5,6],[174],706⟩) from rfl))
private theorem rec9751 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(16),[5,6],[174],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[233]? = some (⟨200,(16),[5,6],[174],710⟩) from rfl))
private theorem rec9758 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(17),[5,6],[174],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[240]? = some (⟨200,(17),[5,6],[174],710⟩) from rfl))
private theorem rec9765 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(18),[5,6],[174],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[247]? = some (⟨200,(18),[5,6],[174],710⟩) from rfl))
private theorem rec9772 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(19),[5,6],[174],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[254]? = some (⟨200,(19),[5,6],[174],710⟩) from rfl))
private theorem rec9779 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(20),[5,6],[174],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[261]? = some (⟨200,(20),[5,6],[174],706⟩) from rfl))
private theorem rec9786 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(21),[5,6],[174],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[268]? = some (⟨200,(21),[5,6],[174],707⟩) from rfl))
private theorem rec9793 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(22),[5,6],[174],708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[275]? = some (⟨200,(22),[5,6],[174],708⟩) from rfl))
private theorem rec9800 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(23),[5,6],[174],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[282]? = some (⟨200,(23),[5,6],[174],707⟩) from rfl))
private theorem rec9807 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 200 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(24),[5,6],[174],709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[289]? = some (⟨200,(24),[5,6],[174],709⟩) from rfl))
private theorem rec9815 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(0),[5,6],[174],1015⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[297]? = some (⟨202,(0),[5,6],[174],1015⟩) from rfl))
private theorem rec9823 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(1),[5,6],[174],1016⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[305]? = some (⟨202,(1),[5,6],[174],1016⟩) from rfl))
private theorem rec9831 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(2),[5,6],[174],1015⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[313]? = some (⟨202,(2),[5,6],[174],1015⟩) from rfl))
private theorem rec9839 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(3),[5,6],[174],1017⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[321]? = some (⟨202,(3),[5,6],[174],1017⟩) from rfl))
private theorem rec9847 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(4),[5,6],[174],1018⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[329]? = some (⟨202,(4),[5,6],[174],1018⟩) from rfl))
private theorem rec9855 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(5),[5,6],[174],1015⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[337]? = some (⟨202,(5),[5,6],[174],1015⟩) from rfl))
private theorem rec9863 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(6),[5,6],[174],1016⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[345]? = some (⟨202,(6),[5,6],[174],1016⟩) from rfl))
private theorem rec9871 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(7),[5,6],[174],1015⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[353]? = some (⟨202,(7),[5,6],[174],1015⟩) from rfl))
private theorem rec9879 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(8),[5,6],[174],1017⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[361]? = some (⟨202,(8),[5,6],[174],1017⟩) from rfl))
private theorem rec9887 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(9),[5,6],[174],1018⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[369]? = some (⟨202,(9),[5,6],[174],1018⟩) from rfl))
private theorem rec9895 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(10),[5,6],[174],1019⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[377]? = some (⟨202,(10),[5,6],[174],1019⟩) from rfl))
private theorem rec9903 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(11),[5,6],[174],1019⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[385]? = some (⟨202,(11),[5,6],[174],1019⟩) from rfl))
private theorem rec9911 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(12),[5,6],[174],1019⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[393]? = some (⟨202,(12),[5,6],[174],1019⟩) from rfl))
private theorem rec9919 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(13),[5,6],[174],1019⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[401]? = some (⟨202,(13),[5,6],[174],1019⟩) from rfl))
private theorem rec9927 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(14),[5,6],[174],1018⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[409]? = some (⟨202,(14),[5,6],[174],1018⟩) from rfl))
private theorem rec9935 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(15),[5,6],[174],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[417]? = some (⟨202,(15),[5,6],[174],1020⟩) from rfl))
private theorem rec9943 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(16),[5,6],[174],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[425]? = some (⟨202,(16),[5,6],[174],1020⟩) from rfl))
private theorem rec9951 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(17),[5,6],[174],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[433]? = some (⟨202,(17),[5,6],[174],1020⟩) from rfl))
private theorem rec9959 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(18),[5,6],[174],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[441]? = some (⟨202,(18),[5,6],[174],1020⟩) from rfl))
private theorem rec9967 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(19),[5,6],[174],1020⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[449]? = some (⟨202,(19),[5,6],[174],1020⟩) from rfl))
private theorem rec9975 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(20),[5,6],[174],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[457]? = some (⟨202,(20),[5,6],[174],1021⟩) from rfl))
private theorem rec9983 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(21),[5,6],[174],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[465]? = some (⟨202,(21),[5,6],[174],1021⟩) from rfl))
private theorem rec9991 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(22),[5,6],[174],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[473]? = some (⟨202,(22),[5,6],[174],1021⟩) from rfl))
private theorem rec9999 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(23),[5,6],[174],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[481]? = some (⟨202,(23),[5,6],[174],1021⟩) from rfl))
private theorem rec10007 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 202 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(24),[5,6],[174],1021⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[489]? = some (⟨202,(24),[5,6],[174],1021⟩) from rfl))
private theorem rec10014 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(0),[5,6],[174],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[496]? = some (⟨205,(0),[5,6],[174],711⟩) from rfl))
private theorem rec10021 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(1),[5,6],[174],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[503]? = some (⟨205,(1),[5,6],[174],711⟩) from rfl))
private theorem rec10028 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(2),[5,6],[174],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[510]? = some (⟨205,(2),[5,6],[174],711⟩) from rfl))
private theorem rec10035 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(3),[5,6],[174],712⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[517]? = some (⟨205,(3),[5,6],[174],712⟩) from rfl))
private theorem rec10041 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(4),[5,6],[174],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[523]? = some (⟨205,(4),[5,6],[174],711⟩) from rfl))
private theorem rec10048 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(5),[5,6],[174],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[530]? = some (⟨205,(5),[5,6],[174],713⟩) from rfl))
private theorem rec10055 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(6),[5,6],[174],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[537]? = some (⟨205,(6),[5,6],[174],713⟩) from rfl))
private theorem rec10062 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(7),[5,6],[174],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[544]? = some (⟨205,(7),[5,6],[174],713⟩) from rfl))
private theorem rec10069 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(8),[5,6],[174],714⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[551]? = some (⟨205,(8),[5,6],[174],714⟩) from rfl))
private theorem rec10075 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(9),[5,6],[174],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[557]? = some (⟨205,(9),[5,6],[174],713⟩) from rfl))
private theorem rec10082 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(10),[5,6],[174],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[564]? = some (⟨205,(10),[5,6],[174],715⟩) from rfl))
private theorem rec10089 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(11),[5,6],[174],716⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[571]? = some (⟨205,(11),[5,6],[174],716⟩) from rfl))
private theorem rec10096 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(12),[5,6],[174],717⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[578]? = some (⟨205,(12),[5,6],[174],717⟩) from rfl))
private theorem rec10103 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(13),[5,6],[174],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[585]? = some (⟨205,(13),[5,6],[174],718⟩) from rfl))
private theorem rec10109 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(14),[5,6],[174],719⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[591]? = some (⟨205,(14),[5,6],[174],719⟩) from rfl))
private theorem rec10116 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(15),[5,6],[174],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[598]? = some (⟨205,(15),[5,6],[174],715⟩) from rfl))
private theorem rec10123 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(16),[5,6],[174],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[605]? = some (⟨205,(16),[5,6],[174],720⟩) from rfl))
private theorem rec10130 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(17),[5,6],[174],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[612]? = some (⟨205,(17),[5,6],[174],720⟩) from rfl))
private theorem rec10137 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(18),[5,6],[174],721⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[619]? = some (⟨205,(18),[5,6],[174],721⟩) from rfl))
private theorem rec10143 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(19),[5,6],[174],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[625]? = some (⟨205,(19),[5,6],[174],720⟩) from rfl))
private theorem rec10150 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(20),[5,6],[174],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[632]? = some (⟨205,(20),[5,6],[174],715⟩) from rfl))
private theorem rec10157 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(21),[5,6],[174],716⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[639]? = some (⟨205,(21),[5,6],[174],716⟩) from rfl))
private theorem rec10164 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(22),[5,6],[174],717⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[646]? = some (⟨205,(22),[5,6],[174],717⟩) from rfl))
private theorem rec10171 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(23),[5,6],[174],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[653]? = some (⟨205,(23),[5,6],[174],718⟩) from rfl))
private theorem rec10177 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 205 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(24),[5,6],[174],719⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[659]? = some (⟨205,(24),[5,6],[174],719⟩) from rfl))
private theorem rec10185 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(0),[5,6],[174],1022⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[667]? = some (⟨207,(0),[5,6],[174],1022⟩) from rfl))
private theorem rec10193 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(1),[5,6],[174],1023⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[675]? = some (⟨207,(1),[5,6],[174],1023⟩) from rfl))
private theorem rec10201 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(2),[5,6],[174],1022⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[683]? = some (⟨207,(2),[5,6],[174],1022⟩) from rfl))
private theorem rec10209 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(3),[5,6],[174],1024⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[691]? = some (⟨207,(3),[5,6],[174],1024⟩) from rfl))
private theorem rec10217 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(4),[5,6],[174],1025⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[699]? = some (⟨207,(4),[5,6],[174],1025⟩) from rfl))
private theorem rec10225 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(5),[5,6],[174],1022⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[707]? = some (⟨207,(5),[5,6],[174],1022⟩) from rfl))
private theorem rec10233 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(6),[5,6],[174],1023⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[715]? = some (⟨207,(6),[5,6],[174],1023⟩) from rfl))
private theorem rec10241 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(7),[5,6],[174],1022⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[723]? = some (⟨207,(7),[5,6],[174],1022⟩) from rfl))
private theorem rec10249 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(8),[5,6],[174],1024⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[731]? = some (⟨207,(8),[5,6],[174],1024⟩) from rfl))
private theorem rec10257 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(9),[5,6],[174],1025⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[739]? = some (⟨207,(9),[5,6],[174],1025⟩) from rfl))
private theorem rec10265 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(10),[5,6],[174],1026⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[747]? = some (⟨207,(10),[5,6],[174],1026⟩) from rfl))
private theorem rec10273 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(11),[5,6],[174],1026⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[755]? = some (⟨207,(11),[5,6],[174],1026⟩) from rfl))
private theorem rec10281 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(12),[5,6],[174],1026⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[763]? = some (⟨207,(12),[5,6],[174],1026⟩) from rfl))
private theorem rec10289 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(13),[5,6],[174],1026⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[771]? = some (⟨207,(13),[5,6],[174],1026⟩) from rfl))
private theorem rec10297 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(14),[5,6],[174],1025⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[779]? = some (⟨207,(14),[5,6],[174],1025⟩) from rfl))
private theorem rec10305 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(15),[5,6],[174],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[787]? = some (⟨207,(15),[5,6],[174],1027⟩) from rfl))
private theorem rec10313 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(16),[5,6],[174],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[795]? = some (⟨207,(16),[5,6],[174],1027⟩) from rfl))
private theorem rec10321 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(17),[5,6],[174],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[803]? = some (⟨207,(17),[5,6],[174],1027⟩) from rfl))
private theorem rec10329 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(18),[5,6],[174],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[811]? = some (⟨207,(18),[5,6],[174],1027⟩) from rfl))
private theorem rec10337 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(19),[5,6],[174],1027⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[819]? = some (⟨207,(19),[5,6],[174],1027⟩) from rfl))
private theorem rec10345 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(20),[5,6],[174],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[827]? = some (⟨207,(20),[5,6],[174],1028⟩) from rfl))
private theorem rec10353 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(21),[5,6],[174],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[835]? = some (⟨207,(21),[5,6],[174],1028⟩) from rfl))
private theorem rec10361 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(22),[5,6],[174],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[843]? = some (⟨207,(22),[5,6],[174],1028⟩) from rfl))
private theorem rec10369 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(23),[5,6],[174],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[851]? = some (⟨207,(23),[5,6],[174],1028⟩) from rfl))
private theorem rec10377 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 207 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(24),[5,6],[174],1028⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[859]? = some (⟨207,(24),[5,6],[174],1028⟩) from rfl))
private theorem rec10383 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(0),[5,6],[174],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[865]? = some (⟨210,(0),[5,6],[174],722⟩) from rfl))
private theorem rec10387 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(1),[5,6],[174],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[869]? = some (⟨210,(1),[5,6],[174],723⟩) from rfl))
private theorem rec10391 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(2),[5,6],[174],724⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[873]? = some (⟨210,(2),[5,6],[174],724⟩) from rfl))
private theorem rec10395 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(3),[5,6],[174],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[877]? = some (⟨210,(3),[5,6],[174],725⟩) from rfl))
private theorem rec10399 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(4),[5,6],[174],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[881]? = some (⟨210,(4),[5,6],[174],722⟩) from rfl))
private theorem rec10403 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(5),[5,6],[174],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[885]? = some (⟨210,(5),[5,6],[174],723⟩) from rfl))
private theorem rec10407 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(6),[5,6],[174],726⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[889]? = some (⟨210,(6),[5,6],[174],726⟩) from rfl))
private theorem rec10411 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(7),[5,6],[174],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[893]? = some (⟨210,(7),[5,6],[174],725⟩) from rfl))
private theorem rec10415 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(8),[5,6],[174],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[897]? = some (⟨210,(8),[5,6],[174],722⟩) from rfl))
private theorem rec10419 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(9),[5,6],[174],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[901]? = some (⟨210,(9),[5,6],[174],723⟩) from rfl))
private theorem rec10423 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(10),[5,6],[174],724⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[905]? = some (⟨210,(10),[5,6],[174],724⟩) from rfl))
private theorem rec10427 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(11),[5,6],[174],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[909]? = some (⟨210,(11),[5,6],[174],725⟩) from rfl))
private theorem rec10431 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(12),[5,6],[174],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[913]? = some (⟨210,(12),[5,6],[174],722⟩) from rfl))
private theorem rec10435 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(13),[5,6],[174],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[917]? = some (⟨210,(13),[5,6],[174],723⟩) from rfl))
private theorem rec10439 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(14),[5,6],[174],727⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[921]? = some (⟨210,(14),[5,6],[174],727⟩) from rfl))
private theorem rec10443 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 210 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(15),[5,6],[174],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[925]? = some (⟨210,(15),[5,6],[174],725⟩) from rfl))
private theorem rec10449 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(0),[5,6],[174],1029⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[931]? = some (⟨213,(0),[5,6],[174],1029⟩) from rfl))
private theorem rec10457 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(1),[5,6],[174],1030⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[939]? = some (⟨213,(1),[5,6],[174],1030⟩) from rfl))
private theorem rec10465 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(2),[5,6],[174],1029⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[947]? = some (⟨213,(2),[5,6],[174],1029⟩) from rfl))
private theorem rec10473 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(3),[5,6],[174],1031⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[955]? = some (⟨213,(3),[5,6],[174],1031⟩) from rfl))
private theorem rec10481 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(4),[5,6],[174],1032⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[963]? = some (⟨213,(4),[5,6],[174],1032⟩) from rfl))
private theorem rec10489 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(5),[5,6],[174],1032⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[971]? = some (⟨213,(5),[5,6],[174],1032⟩) from rfl))
private theorem rec10498 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(6),[5,6],[174],1032⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[980]? = some (⟨213,(6),[5,6],[174],1032⟩) from rfl))
private theorem rec10508 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(7),[5,6],[174],1032⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[990]? = some (⟨213,(7),[5,6],[174],1032⟩) from rfl))
private theorem rec10516 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(8),[5,6],[174],1034⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[998]? = some (⟨213,(8),[5,6],[174],1034⟩) from rfl))
private theorem rec10524 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(9),[5,6],[174],1034⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1006]? = some (⟨213,(9),[5,6],[174],1034⟩) from rfl))
private theorem rec10532 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(10),[5,6],[174],1034⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1014]? = some (⟨213,(10),[5,6],[174],1034⟩) from rfl))
private theorem rec10540 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(11),[5,6],[174],1034⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1022]? = some (⟨213,(11),[5,6],[174],1034⟩) from rfl))
private theorem rec10548 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(12),[5,6],[174],1035⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1030]? = some (⟨213,(12),[5,6],[174],1035⟩) from rfl))
private theorem rec10556 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(13),[5,6],[174],1035⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1038]? = some (⟨213,(13),[5,6],[174],1035⟩) from rfl))
private theorem rec10564 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(14),[5,6],[174],1035⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1046]? = some (⟨213,(14),[5,6],[174],1035⟩) from rfl))
private theorem rec10572 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 213 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(15),[5,6],[174],1035⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1054]? = some (⟨213,(15),[5,6],[174],1035⟩) from rfl))
private theorem rec10578 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(0),[5,6],[174],728⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1060]? = some (⟨215,(0),[5,6],[174],728⟩) from rfl))
private theorem rec10582 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(1),[5,6],[174],729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1064]? = some (⟨215,(1),[5,6],[174],729⟩) from rfl))
private theorem rec10586 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(2),[5,6],[174],730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1068]? = some (⟨215,(2),[5,6],[174],730⟩) from rfl))
private theorem rec10590 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(3),[5,6],[174],731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1072]? = some (⟨215,(3),[5,6],[174],731⟩) from rfl))
private theorem rec10594 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(4),[5,6],[174],728⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1076]? = some (⟨215,(4),[5,6],[174],728⟩) from rfl))
private theorem rec10598 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(5),[5,6],[174],729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1080]? = some (⟨215,(5),[5,6],[174],729⟩) from rfl))
private theorem rec10602 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(6),[5,6],[174],732⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1084]? = some (⟨215,(6),[5,6],[174],732⟩) from rfl))
private theorem rec10606 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(7),[5,6],[174],731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1088]? = some (⟨215,(7),[5,6],[174],731⟩) from rfl))
private theorem rec10610 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(8),[5,6],[174],728⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1092]? = some (⟨215,(8),[5,6],[174],728⟩) from rfl))
private theorem rec10614 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(9),[5,6],[174],729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1096]? = some (⟨215,(9),[5,6],[174],729⟩) from rfl))
private theorem rec10618 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(10),[5,6],[174],730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1100]? = some (⟨215,(10),[5,6],[174],730⟩) from rfl))
private theorem rec10622 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(11),[5,6],[174],731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1104]? = some (⟨215,(11),[5,6],[174],731⟩) from rfl))
private theorem rec10626 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(12),[5,6],[174],728⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1108]? = some (⟨215,(12),[5,6],[174],728⟩) from rfl))
private theorem rec10630 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(13),[5,6],[174],729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1112]? = some (⟨215,(13),[5,6],[174],729⟩) from rfl))
private theorem rec10634 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(14),[5,6],[174],733⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1116]? = some (⟨215,(14),[5,6],[174],733⟩) from rfl))
private theorem rec10638 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 215 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨215,(15),[5,6],[174],731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1120]? = some (⟨215,(15),[5,6],[174],731⟩) from rfl))
private theorem rec10644 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 218 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(0),[5,6],[174],307⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1126]? = some (⟨218,(0),[5,6],[174],307⟩) from rfl))
private theorem rec10652 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 218 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(1),[5,6],[174],308⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1134]? = some (⟨218,(1),[5,6],[174],308⟩) from rfl))
private theorem rec10660 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 218 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(2),[5,6],[174],309⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1142]? = some (⟨218,(2),[5,6],[174],309⟩) from rfl))
private theorem rec10668 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 218 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(3),[5,6],[174],310⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1150]? = some (⟨218,(3),[5,6],[174],310⟩) from rfl))
private theorem rec10674 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(0),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1156]? = some (⟨220,(0),[5,6],[174],3⟩) from rfl))
private theorem rec10679 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(1),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1161]? = some (⟨220,(1),[5,6],[174],3⟩) from rfl))
private theorem rec10683 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(2),[5,6],[174],734⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1165]? = some (⟨220,(2),[5,6],[174],734⟩) from rfl))
private theorem rec10687 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(3),[5,6],[174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1169]? = some (⟨220,(3),[5,6],[174],29⟩) from rfl))
private theorem rec10691 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(4),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1173]? = some (⟨220,(4),[5,6],[174],3⟩) from rfl))
private theorem rec10695 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(5),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1177]? = some (⟨220,(5),[5,6],[174],3⟩) from rfl))
private theorem rec10699 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(6),[5,6],[174],511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1181]? = some (⟨220,(6),[5,6],[174],511⟩) from rfl))
private theorem rec10703 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(7),[5,6],[174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1185]? = some (⟨220,(7),[5,6],[174],29⟩) from rfl))
private theorem rec10707 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(8),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1189]? = some (⟨220,(8),[5,6],[174],3⟩) from rfl))
private theorem rec10711 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(9),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1193]? = some (⟨220,(9),[5,6],[174],3⟩) from rfl))
private theorem rec10715 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(10),[5,6],[174],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1197]? = some (⟨220,(10),[5,6],[174],512⟩) from rfl))
private theorem rec10719 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(11),[5,6],[174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1201]? = some (⟨220,(11),[5,6],[174],29⟩) from rfl))
private theorem rec10723 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(12),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1205]? = some (⟨220,(12),[5,6],[174],3⟩) from rfl))
private theorem rec10727 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(13),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1209]? = some (⟨220,(13),[5,6],[174],3⟩) from rfl))
private theorem rec10731 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(14),[5,6],[174],513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[2]? = some (⟨220,(14),[5,6],[174],513⟩) from rfl))
private theorem rec10735 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(15),[5,6],[174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[6]? = some (⟨220,(15),[5,6],[174],29⟩) from rfl))
private theorem rec10739 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(16),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[10]? = some (⟨220,(16),[5,6],[174],3⟩) from rfl))
private theorem rec10743 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(17),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[14]? = some (⟨220,(17),[5,6],[174],3⟩) from rfl))
private theorem rec10747 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(18),[5,6],[174],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[18]? = some (⟨220,(18),[5,6],[174],514⟩) from rfl))
private theorem rec10751 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 220 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(19),[5,6],[174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[22]? = some (⟨220,(19),[5,6],[174],29⟩) from rfl))
private theorem rec10757 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(0),[5,6],[174],1036⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[28]? = some (⟨221,(0),[5,6],[174],1036⟩) from rfl))
private theorem rec10765 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(1),[5,6],[174],1036⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[36]? = some (⟨221,(1),[5,6],[174],1036⟩) from rfl))
private theorem rec10773 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(2),[5,6],[174],1037⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[44]? = some (⟨221,(2),[5,6],[174],1037⟩) from rfl))
private theorem rec10781 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(3),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[52]? = some (⟨221,(3),[5,6],[174],1038⟩) from rfl))
private theorem rec10789 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(4),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[60]? = some (⟨221,(4),[5,6],[174],1039⟩) from rfl))
private theorem rec10797 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(5),[5,6],[174],1036⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[68]? = some (⟨221,(5),[5,6],[174],1036⟩) from rfl))
private theorem rec10805 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(6),[5,6],[174],1036⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[76]? = some (⟨221,(6),[5,6],[174],1036⟩) from rfl))
private theorem rec10813 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(7),[5,6],[174],1037⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[84]? = some (⟨221,(7),[5,6],[174],1037⟩) from rfl))
private theorem rec10821 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(8),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[92]? = some (⟨221,(8),[5,6],[174],1038⟩) from rfl))
private theorem rec10829 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(9),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[100]? = some (⟨221,(9),[5,6],[174],1039⟩) from rfl))
private theorem rec10837 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(10),[5,6],[174],1040⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[108]? = some (⟨221,(10),[5,6],[174],1040⟩) from rfl))
private theorem rec10845 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(11),[5,6],[174],1040⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[116]? = some (⟨221,(11),[5,6],[174],1040⟩) from rfl))
private theorem rec10853 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(12),[5,6],[174],1041⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[124]? = some (⟨221,(12),[5,6],[174],1041⟩) from rfl))
private theorem rec10861 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(13),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[132]? = some (⟨221,(13),[5,6],[174],1038⟩) from rfl))
private theorem rec10869 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(14),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[140]? = some (⟨221,(14),[5,6],[174],1039⟩) from rfl))
private theorem rec10877 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(15),[5,6],[174],1042⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[148]? = some (⟨221,(15),[5,6],[174],1042⟩) from rfl))
private theorem rec10885 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(16),[5,6],[174],1042⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[156]? = some (⟨221,(16),[5,6],[174],1042⟩) from rfl))
private theorem rec10893 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(17),[5,6],[174],1042⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[164]? = some (⟨221,(17),[5,6],[174],1042⟩) from rfl))
private theorem rec10901 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(18),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[172]? = some (⟨221,(18),[5,6],[174],1038⟩) from rfl))
private theorem rec10910 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(19),[5,6],[174],1042⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[181]? = some (⟨221,(19),[5,6],[174],1042⟩) from rfl))
private theorem rec10918 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(20),[5,6],[174],1043⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[189]? = some (⟨221,(20),[5,6],[174],1043⟩) from rfl))
private theorem rec10926 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(21),[5,6],[174],1043⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[197]? = some (⟨221,(21),[5,6],[174],1043⟩) from rfl))
private theorem rec10934 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(22),[5,6],[174],1043⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[205]? = some (⟨221,(22),[5,6],[174],1043⟩) from rfl))
private theorem rec10942 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(23),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[213]? = some (⟨221,(23),[5,6],[174],1038⟩) from rfl))
private theorem rec10950 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 221 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(24),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[221]? = some (⟨221,(24),[5,6],[174],1039⟩) from rfl))
private theorem rec10960 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(0),[6],[174],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[231]? = some (⟨222,(0),[6],[174],735⟩) from rfl))
private theorem rec10967 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(1),[5,6],[174],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[238]? = some (⟨222,(1),[5,6],[174],736⟩) from rfl))
private theorem rec10974 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(2),[5,6],[174],737⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[245]? = some (⟨222,(2),[5,6],[174],737⟩) from rfl))
private theorem rec10982 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(3),[5,6],[174],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[253]? = some (⟨222,(3),[5,6],[174],736⟩) from rfl))
private theorem rec10989 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(4),[5,6],[174],525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[260]? = some (⟨222,(4),[5,6],[174],525⟩) from rfl))
private theorem rec10995 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(5),[5,6],[174],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[266]? = some (⟨222,(5),[5,6],[174],735⟩) from rfl))
private theorem rec11004 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(6),[6],[174],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[275]? = some (⟨222,(6),[6],[174],738⟩) from rfl))
private theorem rec11011 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(7),[5,6],[174],739⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[282]? = some (⟨222,(7),[5,6],[174],739⟩) from rfl))
private theorem rec11019 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(8),[5,6],[174],740⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[290]? = some (⟨222,(8),[5,6],[174],740⟩) from rfl))
private theorem rec11026 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(9),[5,6],[174],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[297]? = some (⟨222,(9),[5,6],[174],528⟩) from rfl))
private theorem rec11034 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(10),[6],[174],741⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[305]? = some (⟨222,(10),[6],[174],741⟩) from rfl))
private theorem rec11043 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(11),[6],[174],742⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[314]? = some (⟨222,(11),[6],[174],742⟩) from rfl))
private theorem rec11052 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(12),[6],[174],743⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[323]? = some (⟨222,(12),[6],[174],743⟩) from rfl))
private theorem rec11062 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(13),[6],[174],744⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[333]? = some (⟨222,(13),[6],[174],744⟩) from rfl))
private theorem rec11069 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(14),[5,6],[174],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[340]? = some (⟨222,(14),[5,6],[174],531⟩) from rfl))
private theorem rec11075 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(15),[5,6],[174],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[346]? = some (⟨222,(15),[5,6],[174],735⟩) from rfl))
private theorem rec11082 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(16),[5,6],[174],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[353]? = some (⟨222,(16),[5,6],[174],738⟩) from rfl))
private theorem rec11089 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(17),[5,6],[174],745⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[360]? = some (⟨222,(17),[5,6],[174],745⟩) from rfl))
private theorem rec11097 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(18),[5,6],[174],746⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[368]? = some (⟨222,(18),[5,6],[174],746⟩) from rfl))
private theorem rec11104 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(19),[5,6],[174],534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[375]? = some (⟨222,(19),[5,6],[174],534⟩) from rfl))
private theorem rec11110 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(20),[5,6],[174],535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[381]? = some (⟨222,(20),[5,6],[174],535⟩) from rfl))
private theorem rec11116 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(21),[5,6],[174],536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[387]? = some (⟨222,(21),[5,6],[174],536⟩) from rfl))
private theorem rec11122 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(22),[5,6],[174],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[393]? = some (⟨222,(22),[5,6],[174],537⟩) from rfl))
private theorem rec11128 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(23),[5,6],[174],538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[399]? = some (⟨222,(23),[5,6],[174],538⟩) from rfl))
private theorem rec11134 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 222 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(24),[5,6],[174],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[405]? = some (⟨222,(24),[5,6],[174],537⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 46).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 174 gs.1 j := by
  have hp : ((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 46).take 23) = [(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 200)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec9639 6 174 (by decide) (by decide)
    · right
      exact rec9646 6 174 (by decide) (by decide)
    · right
      exact rec9653 6 174 (by decide) (by decide)
    · right
      exact rec9660 6 174 (by decide) (by decide)
    · right
      exact rec9667 6 174 (by decide) (by decide)
    · right
      exact rec9674 6 174 (by decide) (by decide)
    · right
      exact rec9681 6 174 (by decide) (by decide)
    · right
      exact rec9688 6 174 (by decide) (by decide)
    · right
      exact rec9695 6 174 (by decide) (by decide)
    · right
      exact rec9702 6 174 (by decide) (by decide)
    · right
      exact rec9709 6 174 (by decide) (by decide)
    · right
      exact rec9716 6 174 (by decide) (by decide)
    · right
      exact rec9723 6 174 (by decide) (by decide)
    · right
      exact rec9730 6 174 (by decide) (by decide)
    · right
      exact rec9737 6 174 (by decide) (by decide)
    · right
      exact rec9744 6 174 (by decide) (by decide)
    · right
      exact rec9751 6 174 (by decide) (by decide)
    · right
      exact rec9758 6 174 (by decide) (by decide)
    · right
      exact rec9765 6 174 (by decide) (by decide)
    · right
      exact rec9772 6 174 (by decide) (by decide)
    · right
      exact rec9779 6 174 (by decide) (by decide)
    · right
      exact rec9786 6 174 (by decide) (by decide)
    · right
      exact rec9793 6 174 (by decide) (by decide)
    · right
      exact rec9800 6 174 (by decide) (by decide)
    · right
      exact rec9807 6 174 (by decide) (by decide)
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
      exact rec9815 6 174 (by decide) (by decide)
    · right
      exact rec9823 6 174 (by decide) (by decide)
    · right
      exact rec9831 6 174 (by decide) (by decide)
    · right
      exact rec9839 6 174 (by decide) (by decide)
    · right
      exact rec9847 6 174 (by decide) (by decide)
    · right
      exact rec9855 6 174 (by decide) (by decide)
    · right
      exact rec9863 6 174 (by decide) (by decide)
    · right
      exact rec9871 6 174 (by decide) (by decide)
    · right
      exact rec9879 6 174 (by decide) (by decide)
    · right
      exact rec9887 6 174 (by decide) (by decide)
    · right
      exact rec9895 6 174 (by decide) (by decide)
    · right
      exact rec9903 6 174 (by decide) (by decide)
    · right
      exact rec9911 6 174 (by decide) (by decide)
    · right
      exact rec9919 6 174 (by decide) (by decide)
    · right
      exact rec9927 6 174 (by decide) (by decide)
    · right
      exact rec9935 6 174 (by decide) (by decide)
    · right
      exact rec9943 6 174 (by decide) (by decide)
    · right
      exact rec9951 6 174 (by decide) (by decide)
    · right
      exact rec9959 6 174 (by decide) (by decide)
    · right
      exact rec9967 6 174 (by decide) (by decide)
    · right
      exact rec9975 6 174 (by decide) (by decide)
    · right
      exact rec9983 6 174 (by decide) (by decide)
    · right
      exact rec9991 6 174 (by decide) (by decide)
    · right
      exact rec9999 6 174 (by decide) (by decide)
    · right
      exact rec10007 6 174 (by decide) (by decide)
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
      exact rec10014 6 174 (by decide) (by decide)
    · right
      exact rec10021 6 174 (by decide) (by decide)
    · right
      exact rec10028 6 174 (by decide) (by decide)
    · right
      exact rec10035 6 174 (by decide) (by decide)
    · right
      exact rec10041 6 174 (by decide) (by decide)
    · right
      exact rec10048 6 174 (by decide) (by decide)
    · right
      exact rec10055 6 174 (by decide) (by decide)
    · right
      exact rec10062 6 174 (by decide) (by decide)
    · right
      exact rec10069 6 174 (by decide) (by decide)
    · right
      exact rec10075 6 174 (by decide) (by decide)
    · right
      exact rec10082 6 174 (by decide) (by decide)
    · right
      exact rec10089 6 174 (by decide) (by decide)
    · right
      exact rec10096 6 174 (by decide) (by decide)
    · right
      exact rec10103 6 174 (by decide) (by decide)
    · right
      exact rec10109 6 174 (by decide) (by decide)
    · right
      exact rec10116 6 174 (by decide) (by decide)
    · right
      exact rec10123 6 174 (by decide) (by decide)
    · right
      exact rec10130 6 174 (by decide) (by decide)
    · right
      exact rec10137 6 174 (by decide) (by decide)
    · right
      exact rec10143 6 174 (by decide) (by decide)
    · right
      exact rec10150 6 174 (by decide) (by decide)
    · right
      exact rec10157 6 174 (by decide) (by decide)
    · right
      exact rec10164 6 174 (by decide) (by decide)
    · right
      exact rec10171 6 174 (by decide) (by decide)
    · right
      exact rec10177 6 174 (by decide) (by decide)
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
      exact rec10185 6 174 (by decide) (by decide)
    · right
      exact rec10193 6 174 (by decide) (by decide)
    · right
      exact rec10201 6 174 (by decide) (by decide)
    · right
      exact rec10209 6 174 (by decide) (by decide)
    · right
      exact rec10217 6 174 (by decide) (by decide)
    · right
      exact rec10225 6 174 (by decide) (by decide)
    · right
      exact rec10233 6 174 (by decide) (by decide)
    · right
      exact rec10241 6 174 (by decide) (by decide)
    · right
      exact rec10249 6 174 (by decide) (by decide)
    · right
      exact rec10257 6 174 (by decide) (by decide)
    · right
      exact rec10265 6 174 (by decide) (by decide)
    · right
      exact rec10273 6 174 (by decide) (by decide)
    · right
      exact rec10281 6 174 (by decide) (by decide)
    · right
      exact rec10289 6 174 (by decide) (by decide)
    · right
      exact rec10297 6 174 (by decide) (by decide)
    · right
      exact rec10305 6 174 (by decide) (by decide)
    · right
      exact rec10313 6 174 (by decide) (by decide)
    · right
      exact rec10321 6 174 (by decide) (by decide)
    · right
      exact rec10329 6 174 (by decide) (by decide)
    · right
      exact rec10337 6 174 (by decide) (by decide)
    · right
      exact rec10345 6 174 (by decide) (by decide)
    · right
      exact rec10353 6 174 (by decide) (by decide)
    · right
      exact rec10361 6 174 (by decide) (by decide)
    · right
      exact rec10369 6 174 (by decide) (by decide)
    · right
      exact rec10377 6 174 (by decide) (by decide)
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
      exact rec10383 6 174 (by decide) (by decide)
    · right
      exact rec10387 6 174 (by decide) (by decide)
    · right
      exact rec10391 6 174 (by decide) (by decide)
    · right
      exact rec10395 6 174 (by decide) (by decide)
    · right
      exact rec10399 6 174 (by decide) (by decide)
    · right
      exact rec10403 6 174 (by decide) (by decide)
    · right
      exact rec10407 6 174 (by decide) (by decide)
    · right
      exact rec10411 6 174 (by decide) (by decide)
    · right
      exact rec10415 6 174 (by decide) (by decide)
    · right
      exact rec10419 6 174 (by decide) (by decide)
    · right
      exact rec10423 6 174 (by decide) (by decide)
    · right
      exact rec10427 6 174 (by decide) (by decide)
    · right
      exact rec10431 6 174 (by decide) (by decide)
    · right
      exact rec10435 6 174 (by decide) (by decide)
    · right
      exact rec10439 6 174 (by decide) (by decide)
    · right
      exact rec10443 6 174 (by decide) (by decide)
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
      exact rec10449 6 174 (by decide) (by decide)
    · right
      exact rec10457 6 174 (by decide) (by decide)
    · right
      exact rec10465 6 174 (by decide) (by decide)
    · right
      exact rec10473 6 174 (by decide) (by decide)
    · right
      exact rec10481 6 174 (by decide) (by decide)
    · right
      exact rec10489 6 174 (by decide) (by decide)
    · right
      exact rec10498 6 174 (by decide) (by decide)
    · right
      exact rec10508 6 174 (by decide) (by decide)
    · right
      exact rec10516 6 174 (by decide) (by decide)
    · right
      exact rec10524 6 174 (by decide) (by decide)
    · right
      exact rec10532 6 174 (by decide) (by decide)
    · right
      exact rec10540 6 174 (by decide) (by decide)
    · right
      exact rec10548 6 174 (by decide) (by decide)
    · right
      exact rec10556 6 174 (by decide) (by decide)
    · right
      exact rec10564 6 174 (by decide) (by decide)
    · right
      exact rec10572 6 174 (by decide) (by decide)
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
      exact rec10578 6 174 (by decide) (by decide)
    · right
      exact rec10582 6 174 (by decide) (by decide)
    · right
      exact rec10586 6 174 (by decide) (by decide)
    · right
      exact rec10590 6 174 (by decide) (by decide)
    · right
      exact rec10594 6 174 (by decide) (by decide)
    · right
      exact rec10598 6 174 (by decide) (by decide)
    · right
      exact rec10602 6 174 (by decide) (by decide)
    · right
      exact rec10606 6 174 (by decide) (by decide)
    · right
      exact rec10610 6 174 (by decide) (by decide)
    · right
      exact rec10614 6 174 (by decide) (by decide)
    · right
      exact rec10618 6 174 (by decide) (by decide)
    · right
      exact rec10622 6 174 (by decide) (by decide)
    · right
      exact rec10626 6 174 (by decide) (by decide)
    · right
      exact rec10630 6 174 (by decide) (by decide)
    · right
      exact rec10634 6 174 (by decide) (by decide)
    · right
      exact rec10638 6 174 (by decide) (by decide)
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
      exact rec10644 6 174 (by decide) (by decide)
    · right
      exact rec10652 6 174 (by decide) (by decide)
    · right
      exact rec10660 6 174 (by decide) (by decide)
    · right
      exact rec10668 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 219)).length = 20 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 220)).length = 20 := by decide +kernel
    have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec10674 6 174 (by decide) (by decide)
    · right
      exact rec10679 6 174 (by decide) (by decide)
    · right
      exact rec10683 6 174 (by decide) (by decide)
    · right
      exact rec10687 6 174 (by decide) (by decide)
    · right
      exact rec10691 6 174 (by decide) (by decide)
    · right
      exact rec10695 6 174 (by decide) (by decide)
    · right
      exact rec10699 6 174 (by decide) (by decide)
    · right
      exact rec10703 6 174 (by decide) (by decide)
    · right
      exact rec10707 6 174 (by decide) (by decide)
    · right
      exact rec10711 6 174 (by decide) (by decide)
    · right
      exact rec10715 6 174 (by decide) (by decide)
    · right
      exact rec10719 6 174 (by decide) (by decide)
    · right
      exact rec10723 6 174 (by decide) (by decide)
    · right
      exact rec10727 6 174 (by decide) (by decide)
    · right
      exact rec10731 6 174 (by decide) (by decide)
    · right
      exact rec10735 6 174 (by decide) (by decide)
    · right
      exact rec10739 6 174 (by decide) (by decide)
    · right
      exact rec10743 6 174 (by decide) (by decide)
    · right
      exact rec10747 6 174 (by decide) (by decide)
    · right
      exact rec10751 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 221)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec10757 6 174 (by decide) (by decide)
    · right
      exact rec10765 6 174 (by decide) (by decide)
    · right
      exact rec10773 6 174 (by decide) (by decide)
    · right
      exact rec10781 6 174 (by decide) (by decide)
    · right
      exact rec10789 6 174 (by decide) (by decide)
    · right
      exact rec10797 6 174 (by decide) (by decide)
    · right
      exact rec10805 6 174 (by decide) (by decide)
    · right
      exact rec10813 6 174 (by decide) (by decide)
    · right
      exact rec10821 6 174 (by decide) (by decide)
    · right
      exact rec10829 6 174 (by decide) (by decide)
    · right
      exact rec10837 6 174 (by decide) (by decide)
    · right
      exact rec10845 6 174 (by decide) (by decide)
    · right
      exact rec10853 6 174 (by decide) (by decide)
    · right
      exact rec10861 6 174 (by decide) (by decide)
    · right
      exact rec10869 6 174 (by decide) (by decide)
    · right
      exact rec10877 6 174 (by decide) (by decide)
    · right
      exact rec10885 6 174 (by decide) (by decide)
    · right
      exact rec10893 6 174 (by decide) (by decide)
    · right
      exact rec10901 6 174 (by decide) (by decide)
    · right
      exact rec10910 6 174 (by decide) (by decide)
    · right
      exact rec10918 6 174 (by decide) (by decide)
    · right
      exact rec10926 6 174 (by decide) (by decide)
    · right
      exact rec10934 6 174 (by decide) (by decide)
    · right
      exact rec10942 6 174 (by decide) (by decide)
    · right
      exact rec10950 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 222)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec10960 6 174 (by decide) (by decide)
    · right
      exact rec10967 6 174 (by decide) (by decide)
    · right
      exact rec10974 6 174 (by decide) (by decide)
    · right
      exact rec10982 6 174 (by decide) (by decide)
    · right
      exact rec10989 6 174 (by decide) (by decide)
    · right
      exact rec10995 6 174 (by decide) (by decide)
    · right
      exact rec11004 6 174 (by decide) (by decide)
    · right
      exact rec11011 6 174 (by decide) (by decide)
    · right
      exact rec11019 6 174 (by decide) (by decide)
    · right
      exact rec11026 6 174 (by decide) (by decide)
    · right
      exact rec11034 6 174 (by decide) (by decide)
    · right
      exact rec11043 6 174 (by decide) (by decide)
    · right
      exact rec11052 6 174 (by decide) (by decide)
    · right
      exact rec11062 6 174 (by decide) (by decide)
    · right
      exact rec11069 6 174 (by decide) (by decide)
    · right
      exact rec11075 6 174 (by decide) (by decide)
    · right
      exact rec11082 6 174 (by decide) (by decide)
    · right
      exact rec11089 6 174 (by decide) (by decide)
    · right
      exact rec11097 6 174 (by decide) (by decide)
    · right
      exact rec11104 6 174 (by decide) (by decide)
    · right
      exact rec11110 6 174 (by decide) (by decide)
    · right
      exact rec11116 6 174 (by decide) (by decide)
    · right
      exact rec11122 6 174 (by decide) (by decide)
    · right
      exact rec11128 6 174 (by decide) (by decide)
    · right
      exact rec11134 6 174 (by decide) (by decide)
end Section14CoverageSpec_6_5_p174_46_69

#print axioms solution
