-- Prove2me | solution 1 for Freiman.section14_s0013_coverage0005_parentidx0170_specs_0056_0064
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-21T09:12:55.418298+00:00
-- url     : https://prove2.me/submissions/e77813fd-c6b9-471a-b43d-5d32d4ffccb7

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
namespace Section14CoverageSpec_13_5_p170_56_64
private theorem rec_210_0 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(0),[1,2,5,6,13,14],[170],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[863]? = some (⟨210,(0),[1,2,5,6,13,14],[170],722⟩) from rfl))
private theorem rec_210_1 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(1),[1,2,5,6,13,14],[170],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[867]? = some (⟨210,(1),[1,2,5,6,13,14],[170],723⟩) from rfl))
private theorem rec_210_2 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(2),[1,2,5,6,13,14],[170],724⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[871]? = some (⟨210,(2),[1,2,5,6,13,14],[170],724⟩) from rfl))
private theorem rec_210_3 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(3),[1,2,5,6,13,14],[170],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[875]? = some (⟨210,(3),[1,2,5,6,13,14],[170],725⟩) from rfl))
private theorem rec_210_4 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(4),[1,2,5,6,13,14],[170],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[879]? = some (⟨210,(4),[1,2,5,6,13,14],[170],722⟩) from rfl))
private theorem rec_210_5 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(5),[1,2,5,6,13,14],[170],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[883]? = some (⟨210,(5),[1,2,5,6,13,14],[170],723⟩) from rfl))
private theorem rec_210_6 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(6),[1,2,5,6,13,14],[170],726⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[887]? = some (⟨210,(6),[1,2,5,6,13,14],[170],726⟩) from rfl))
private theorem rec_210_7 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(7),[1,2,5,6,13,14],[170],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[891]? = some (⟨210,(7),[1,2,5,6,13,14],[170],725⟩) from rfl))
private theorem rec_210_8 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(8),[1,2,5,6,13,14],[170],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[895]? = some (⟨210,(8),[1,2,5,6,13,14],[170],722⟩) from rfl))
private theorem rec_210_9 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(9),[1,2,5,6,13,14],[170],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[899]? = some (⟨210,(9),[1,2,5,6,13,14],[170],723⟩) from rfl))
private theorem rec_210_10 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(10),[1,2,5,6,13,14],[170],724⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[903]? = some (⟨210,(10),[1,2,5,6,13,14],[170],724⟩) from rfl))
private theorem rec_210_11 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(11),[1,2,5,6,13,14],[170],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[907]? = some (⟨210,(11),[1,2,5,6,13,14],[170],725⟩) from rfl))
private theorem rec_210_12 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(12),[1,2,5,6,13,14],[170],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[911]? = some (⟨210,(12),[1,2,5,6,13,14],[170],722⟩) from rfl))
private theorem rec_210_13 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(13),[1,2,5,6,13,14],[170],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[915]? = some (⟨210,(13),[1,2,5,6,13,14],[170],723⟩) from rfl))
private theorem rec_210_14 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(14),[1,2,5,6,13,14],[170],727⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[919]? = some (⟨210,(14),[1,2,5,6,13,14],[170],727⟩) from rfl))
private theorem rec_210_15 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(15),[1,2,5,6,13,14],[170],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[923]? = some (⟨210,(15),[1,2,5,6,13,14],[170],725⟩) from rfl))
private theorem rec_213_0 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(0),[1,2,5,6,13,14],[170],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[927]? = some (⟨213,(0),[1,2,5,6,13,14],[170],494⟩) from rfl))
private theorem rec_213_1 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(1),[1,2,5,6,13,14],[170],495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[935]? = some (⟨213,(1),[1,2,5,6,13,14],[170],495⟩) from rfl))
private theorem rec_213_2 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(2),[1,2,5,6,13,14],[170],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[943]? = some (⟨213,(2),[1,2,5,6,13,14],[170],494⟩) from rfl))
private theorem rec_213_3 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(3),[1,2,5,6,13,14],[170],496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[951]? = some (⟨213,(3),[1,2,5,6,13,14],[170],496⟩) from rfl))
private theorem rec_213_4 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(4),[1,2,5,6,13,14],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[959]? = some (⟨213,(4),[1,2,5,6,13,14],[170],497⟩) from rfl))
private theorem rec_213_5 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(5),[1,2,5,6,13,14],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[967]? = some (⟨213,(5),[1,2,5,6,13,14],[170],497⟩) from rfl))
private theorem rec_213_6 (si parent : ℕ) (hs : si ∈ ([1,5,6,13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(6),[1,5,6,13],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[975]? = some (⟨213,(6),[1,5,6,13],[170],497⟩) from rfl))
private theorem rec_213_7 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(7),[1,2,5,6,13,14],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[986]? = some (⟨213,(7),[1,2,5,6,13,14],[170],497⟩) from rfl))
private theorem rec_213_8 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(8),[1,2,5,6,13,14],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[994]? = some (⟨213,(8),[1,2,5,6,13,14],[170],498⟩) from rfl))
private theorem rec_213_9 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(9),[1,2,5,6,13,14],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1002]? = some (⟨213,(9),[1,2,5,6,13,14],[170],498⟩) from rfl))
private theorem rec_213_10 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(10),[1,2,5,6,13,14],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1010]? = some (⟨213,(10),[1,2,5,6,13,14],[170],498⟩) from rfl))
private theorem rec_213_11 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(11),[1,2,5,6,13,14],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1018]? = some (⟨213,(11),[1,2,5,6,13,14],[170],498⟩) from rfl))
private theorem rec_213_12 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(12),[1,2,5,6,13,14],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1026]? = some (⟨213,(12),[1,2,5,6,13,14],[170],499⟩) from rfl))
private theorem rec_213_13 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(13),[1,2,5,6,13,14],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1034]? = some (⟨213,(13),[1,2,5,6,13,14],[170],499⟩) from rfl))
private theorem rec_213_14 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(14),[1,2,5,6,13,14],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1042]? = some (⟨213,(14),[1,2,5,6,13,14],[170],499⟩) from rfl))
private theorem rec_213_15 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(15),[1,2,5,6,13,14],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1050]? = some (⟨213,(15),[1,2,5,6,13,14],[170],499⟩) from rfl))
private theorem rec_220_0 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(0),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1154]? = some (⟨220,(0),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_1 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(1),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1159]? = some (⟨220,(1),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_2 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(2),[1,2,5,6,13,14],[170],734⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1163]? = some (⟨220,(2),[1,2,5,6,13,14],[170],734⟩) from rfl))
private theorem rec_220_3 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(3),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1167]? = some (⟨220,(3),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec_220_4 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(4),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1171]? = some (⟨220,(4),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_5 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(5),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1175]? = some (⟨220,(5),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_6 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(6),[1,2,5,6,13,14],[170],511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1179]? = some (⟨220,(6),[1,2,5,6,13,14],[170],511⟩) from rfl))
private theorem rec_220_7 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(7),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1183]? = some (⟨220,(7),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec_220_8 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(8),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1187]? = some (⟨220,(8),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_9 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(9),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1191]? = some (⟨220,(9),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_10 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(10),[1,2,5,6,13,14],[170],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1195]? = some (⟨220,(10),[1,2,5,6,13,14],[170],512⟩) from rfl))
private theorem rec_220_11 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(11),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1199]? = some (⟨220,(11),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec_220_12 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(12),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1203]? = some (⟨220,(12),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_13 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(13),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1207]? = some (⟨220,(13),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_14 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(14),[1,2,5,6,13,14],[170],513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[0]? = some (⟨220,(14),[1,2,5,6,13,14],[170],513⟩) from rfl))
private theorem rec_220_15 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(15),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[4]? = some (⟨220,(15),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec_220_16 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(16),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[8]? = some (⟨220,(16),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_17 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(17),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[12]? = some (⟨220,(17),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec_220_18 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(18),[1,2,5,6,13,14],[170],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[16]? = some (⟨220,(18),[1,2,5,6,13,14],[170],514⟩) from rfl))
private theorem rec_220_19 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(19),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[20]? = some (⟨220,(19),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec_221_0 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(0),[1,2,5,6,13,14],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[24]? = some (⟨221,(0),[1,2,5,6,13,14],[170],515⟩) from rfl))
private theorem rec_221_1 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(1),[1,2,5,6,13,14],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[32]? = some (⟨221,(1),[1,2,5,6,13,14],[170],515⟩) from rfl))
private theorem rec_221_2 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(2),[1,2,5,6,13,14],[170],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[40]? = some (⟨221,(2),[1,2,5,6,13,14],[170],516⟩) from rfl))
private theorem rec_221_3 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(3),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[48]? = some (⟨221,(3),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec_221_4 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(4),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[56]? = some (⟨221,(4),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec_221_5 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(5),[1,2,5,6,13,14],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[64]? = some (⟨221,(5),[1,2,5,6,13,14],[170],515⟩) from rfl))
private theorem rec_221_6 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(6),[1,2,5,6,13,14],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[72]? = some (⟨221,(6),[1,2,5,6,13,14],[170],515⟩) from rfl))
private theorem rec_221_7 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(7),[1,2,5,6,13,14],[170],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[80]? = some (⟨221,(7),[1,2,5,6,13,14],[170],516⟩) from rfl))
private theorem rec_221_8 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(8),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[88]? = some (⟨221,(8),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec_221_9 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(9),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[96]? = some (⟨221,(9),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec_221_10 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(10),[1,2,5,6,13,14],[170],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[104]? = some (⟨221,(10),[1,2,5,6,13,14],[170],519⟩) from rfl))
private theorem rec_221_11 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(11),[1,2,5,6,13,14],[170],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[112]? = some (⟨221,(11),[1,2,5,6,13,14],[170],519⟩) from rfl))
private theorem rec_221_12 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(12),[1,2,5,6,13,14],[170],520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[120]? = some (⟨221,(12),[1,2,5,6,13,14],[170],520⟩) from rfl))
private theorem rec_221_13 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(13),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[128]? = some (⟨221,(13),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec_221_14 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(14),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[136]? = some (⟨221,(14),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec_221_15 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(15),[1,2,5,6,13,14],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[144]? = some (⟨221,(15),[1,2,5,6,13,14],[170],521⟩) from rfl))
private theorem rec_221_16 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(16),[1,2,5,6,13,14],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[152]? = some (⟨221,(16),[1,2,5,6,13,14],[170],521⟩) from rfl))
private theorem rec_221_17 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(17),[1,2,5,6,13,14],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[160]? = some (⟨221,(17),[1,2,5,6,13,14],[170],521⟩) from rfl))
private theorem rec_221_18 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(18),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[168]? = some (⟨221,(18),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec_221_19 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(19),[1,2,5,6,13,14],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[177]? = some (⟨221,(19),[1,2,5,6,13,14],[170],521⟩) from rfl))
private theorem rec_221_20 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(20),[1,2,5,6,13,14],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[185]? = some (⟨221,(20),[1,2,5,6,13,14],[170],522⟩) from rfl))
private theorem rec_221_21 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(21),[1,2,5,6,13,14],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[193]? = some (⟨221,(21),[1,2,5,6,13,14],[170],522⟩) from rfl))
private theorem rec_221_22 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(22),[1,2,5,6,13,14],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[201]? = some (⟨221,(22),[1,2,5,6,13,14],[170],522⟩) from rfl))
private theorem rec_221_23 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(23),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[209]? = some (⟨221,(23),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec_221_24 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(24),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[217]? = some (⟨221,(24),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec_222_0 (si parent : ℕ) (hs : si ∈ ([1,2,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(0),[1,2,6,13,14],[170],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[226]? = some (⟨222,(0),[1,2,6,13,14],[170],735⟩) from rfl))
private theorem rec_222_1 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(1),[1,2,5,6,13,14],[170],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[235]? = some (⟨222,(1),[1,2,5,6,13,14],[170],736⟩) from rfl))
private theorem rec_222_2 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(2),[1,2,5,6,13,14],[170],737⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[242]? = some (⟨222,(2),[1,2,5,6,13,14],[170],737⟩) from rfl))
private theorem rec_222_3 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(3),[1,2,5,6,13,14],[170],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[250]? = some (⟨222,(3),[1,2,5,6,13,14],[170],736⟩) from rfl))
private theorem rec_222_4 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(4),[1,2,5,6,13,14],[170],525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[257]? = some (⟨222,(4),[1,2,5,6,13,14],[170],525⟩) from rfl))
private theorem rec_222_5 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(5),[1,2,5,6,13,14],[170],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[263]? = some (⟨222,(5),[1,2,5,6,13,14],[170],735⟩) from rfl))
private theorem rec_222_6 (si parent : ℕ) (hs : si ∈ ([1,2,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(6),[1,2,6,13,14],[170],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[270]? = some (⟨222,(6),[1,2,6,13,14],[170],738⟩) from rfl))
private theorem rec_222_7 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(7),[1,2,5,6,13,14],[170],739⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[279]? = some (⟨222,(7),[1,2,5,6,13,14],[170],739⟩) from rfl))
private theorem rec_222_8 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(8),[1,2,5,6,13,14],[170],740⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[287]? = some (⟨222,(8),[1,2,5,6,13,14],[170],740⟩) from rfl))
private theorem rec_222_9 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(9),[1,2,5,6,13,14],[170],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[294]? = some (⟨222,(9),[1,2,5,6,13,14],[170],528⟩) from rfl))
private theorem rec_222_10 (si parent : ℕ) (hs : si ∈ ([1,2,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(10),[1,2,6,13,14],[170],741⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[300]? = some (⟨222,(10),[1,2,6,13,14],[170],741⟩) from rfl))
private theorem rec_222_11 (si parent : ℕ) (hs : si ∈ ([1,2,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(11),[1,2,6,13,14],[170],742⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[309]? = some (⟨222,(11),[1,2,6,13,14],[170],742⟩) from rfl))
private theorem rec_222_12 (si parent : ℕ) (hs : si ∈ ([1,2,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(12),[1,2,6,13,14],[170],743⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[318]? = some (⟨222,(12),[1,2,6,13,14],[170],743⟩) from rfl))
private theorem rec_222_13 (si parent : ℕ) (hs : si ∈ ([1,2,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(13),[1,2,6,13,14],[170],744⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[328]? = some (⟨222,(13),[1,2,6,13,14],[170],744⟩) from rfl))
private theorem rec_222_14 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(14),[1,2,5,6,13,14],[170],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[337]? = some (⟨222,(14),[1,2,5,6,13,14],[170],531⟩) from rfl))
private theorem rec_222_15 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(15),[1,2,5,6,13,14],[170],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[343]? = some (⟨222,(15),[1,2,5,6,13,14],[170],735⟩) from rfl))
private theorem rec_222_16 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(16),[1,2,5,6,13,14],[170],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[350]? = some (⟨222,(16),[1,2,5,6,13,14],[170],738⟩) from rfl))
private theorem rec_222_17 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(17),[1,2,5,6,13,14],[170],745⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[357]? = some (⟨222,(17),[1,2,5,6,13,14],[170],745⟩) from rfl))
private theorem rec_222_18 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(18),[1,2,5,6,13,14],[170],746⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[365]? = some (⟨222,(18),[1,2,5,6,13,14],[170],746⟩) from rfl))
private theorem rec_222_19 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(19),[1,2,5,6,13,14],[170],534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[372]? = some (⟨222,(19),[1,2,5,6,13,14],[170],534⟩) from rfl))
private theorem rec_222_20 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(20),[1,2,5,6,13,14],[170],535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[378]? = some (⟨222,(20),[1,2,5,6,13,14],[170],535⟩) from rfl))
private theorem rec_222_21 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(21),[1,2,5,6,13,14],[170],536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[384]? = some (⟨222,(21),[1,2,5,6,13,14],[170],536⟩) from rfl))
private theorem rec_222_22 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(22),[1,2,5,6,13,14],[170],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[390]? = some (⟨222,(22),[1,2,5,6,13,14],[170],537⟩) from rfl))
private theorem rec_222_23 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(23),[1,2,5,6,13,14],[170],538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[396]? = some (⟨222,(23),[1,2,5,6,13,14],[170],538⟩) from rfl))
private theorem rec_222_24 (si parent : ℕ) (hs : si ∈ ([1,2,5,6,13,14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(24),[1,2,5,6,13,14],[170],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[402]? = some (⟨222,(24),[1,2,5,6,13,14],[170],537⟩) from rfl))
theorem _root_.Freiman.section14_s0013_coverage0005_parentidx0170_specs_0056_0064 : ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 56).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 170 gs.1 j := by
  have hp : ((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(640,⟨([],[]),false,([2],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(640,⟨([],[]),false,([2],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 56).take 8) = [(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 210)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec_210_0 13 170 (by decide) (by decide)
    · right
      exact rec_210_1 13 170 (by decide) (by decide)
    · right
      exact rec_210_2 13 170 (by decide) (by decide)
    · right
      exact rec_210_3 13 170 (by decide) (by decide)
    · right
      exact rec_210_4 13 170 (by decide) (by decide)
    · right
      exact rec_210_5 13 170 (by decide) (by decide)
    · right
      exact rec_210_6 13 170 (by decide) (by decide)
    · right
      exact rec_210_7 13 170 (by decide) (by decide)
    · right
      exact rec_210_8 13 170 (by decide) (by decide)
    · right
      exact rec_210_9 13 170 (by decide) (by decide)
    · right
      exact rec_210_10 13 170 (by decide) (by decide)
    · right
      exact rec_210_11 13 170 (by decide) (by decide)
    · right
      exact rec_210_12 13 170 (by decide) (by decide)
    · right
      exact rec_210_13 13 170 (by decide) (by decide)
    · right
      exact rec_210_14 13 170 (by decide) (by decide)
    · right
      exact rec_210_15 13 170 (by decide) (by decide)
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
      exact rec_213_0 13 170 (by decide) (by decide)
    · right
      exact rec_213_1 13 170 (by decide) (by decide)
    · right
      exact rec_213_2 13 170 (by decide) (by decide)
    · right
      exact rec_213_3 13 170 (by decide) (by decide)
    · right
      exact rec_213_4 13 170 (by decide) (by decide)
    · right
      exact rec_213_5 13 170 (by decide) (by decide)
    · right
      exact rec_213_6 13 170 (by decide) (by decide)
    · right
      exact rec_213_7 13 170 (by decide) (by decide)
    · right
      exact rec_213_8 13 170 (by decide) (by decide)
    · right
      exact rec_213_9 13 170 (by decide) (by decide)
    · right
      exact rec_213_10 13 170 (by decide) (by decide)
    · right
      exact rec_213_11 13 170 (by decide) (by decide)
    · right
      exact rec_213_12 13 170 (by decide) (by decide)
    · right
      exact rec_213_13 13 170 (by decide) (by decide)
    · right
      exact rec_213_14 13 170 (by decide) (by decide)
    · right
      exact rec_213_15 13 170 (by decide) (by decide)
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
      exact rec_220_0 13 170 (by decide) (by decide)
    · right
      exact rec_220_1 13 170 (by decide) (by decide)
    · right
      exact rec_220_2 13 170 (by decide) (by decide)
    · right
      exact rec_220_3 13 170 (by decide) (by decide)
    · right
      exact rec_220_4 13 170 (by decide) (by decide)
    · right
      exact rec_220_5 13 170 (by decide) (by decide)
    · right
      exact rec_220_6 13 170 (by decide) (by decide)
    · right
      exact rec_220_7 13 170 (by decide) (by decide)
    · right
      exact rec_220_8 13 170 (by decide) (by decide)
    · right
      exact rec_220_9 13 170 (by decide) (by decide)
    · right
      exact rec_220_10 13 170 (by decide) (by decide)
    · right
      exact rec_220_11 13 170 (by decide) (by decide)
    · right
      exact rec_220_12 13 170 (by decide) (by decide)
    · right
      exact rec_220_13 13 170 (by decide) (by decide)
    · right
      exact rec_220_14 13 170 (by decide) (by decide)
    · right
      exact rec_220_15 13 170 (by decide) (by decide)
    · right
      exact rec_220_16 13 170 (by decide) (by decide)
    · right
      exact rec_220_17 13 170 (by decide) (by decide)
    · right
      exact rec_220_18 13 170 (by decide) (by decide)
    · right
      exact rec_220_19 13 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 221)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec_221_0 13 170 (by decide) (by decide)
    · right
      exact rec_221_1 13 170 (by decide) (by decide)
    · right
      exact rec_221_2 13 170 (by decide) (by decide)
    · right
      exact rec_221_3 13 170 (by decide) (by decide)
    · right
      exact rec_221_4 13 170 (by decide) (by decide)
    · right
      exact rec_221_5 13 170 (by decide) (by decide)
    · right
      exact rec_221_6 13 170 (by decide) (by decide)
    · right
      exact rec_221_7 13 170 (by decide) (by decide)
    · right
      exact rec_221_8 13 170 (by decide) (by decide)
    · right
      exact rec_221_9 13 170 (by decide) (by decide)
    · right
      exact rec_221_10 13 170 (by decide) (by decide)
    · right
      exact rec_221_11 13 170 (by decide) (by decide)
    · right
      exact rec_221_12 13 170 (by decide) (by decide)
    · right
      exact rec_221_13 13 170 (by decide) (by decide)
    · right
      exact rec_221_14 13 170 (by decide) (by decide)
    · right
      exact rec_221_15 13 170 (by decide) (by decide)
    · right
      exact rec_221_16 13 170 (by decide) (by decide)
    · right
      exact rec_221_17 13 170 (by decide) (by decide)
    · right
      exact rec_221_18 13 170 (by decide) (by decide)
    · right
      exact rec_221_19 13 170 (by decide) (by decide)
    · right
      exact rec_221_20 13 170 (by decide) (by decide)
    · right
      exact rec_221_21 13 170 (by decide) (by decide)
    · right
      exact rec_221_22 13 170 (by decide) (by decide)
    · right
      exact rec_221_23 13 170 (by decide) (by decide)
    · right
      exact rec_221_24 13 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 222)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec_222_0 13 170 (by decide) (by decide)
    · right
      exact rec_222_1 13 170 (by decide) (by decide)
    · right
      exact rec_222_2 13 170 (by decide) (by decide)
    · right
      exact rec_222_3 13 170 (by decide) (by decide)
    · right
      exact rec_222_4 13 170 (by decide) (by decide)
    · right
      exact rec_222_5 13 170 (by decide) (by decide)
    · right
      exact rec_222_6 13 170 (by decide) (by decide)
    · right
      exact rec_222_7 13 170 (by decide) (by decide)
    · right
      exact rec_222_8 13 170 (by decide) (by decide)
    · right
      exact rec_222_9 13 170 (by decide) (by decide)
    · right
      exact rec_222_10 13 170 (by decide) (by decide)
    · right
      exact rec_222_11 13 170 (by decide) (by decide)
    · right
      exact rec_222_12 13 170 (by decide) (by decide)
    · right
      exact rec_222_13 13 170 (by decide) (by decide)
    · right
      exact rec_222_14 13 170 (by decide) (by decide)
    · right
      exact rec_222_15 13 170 (by decide) (by decide)
    · right
      exact rec_222_16 13 170 (by decide) (by decide)
    · right
      exact rec_222_17 13 170 (by decide) (by decide)
    · right
      exact rec_222_18 13 170 (by decide) (by decide)
    · right
      exact rec_222_19 13 170 (by decide) (by decide)
    · right
      exact rec_222_20 13 170 (by decide) (by decide)
    · right
      exact rec_222_21 13 170 (by decide) (by decide)
    · right
      exact rec_222_22 13 170 (by decide) (by decide)
    · right
      exact rec_222_23 13 170 (by decide) (by decide)
    · right
      exact rec_222_24 13 170 (by decide) (by decide)
end Section14CoverageSpec_13_5_p170_56_64

theorem solution : ∀ gs ∈ (((section14State section14Catalog 13).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 56).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 170 gs.1 j :=
  Freiman.section14_s0013_coverage0005_parentidx0170_specs_0056_0064

#print axioms Freiman.section14_s0013_coverage0005_parentidx0170_specs_0056_0064
#print axioms solution
