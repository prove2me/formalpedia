-- Prove2me | solution 1 for Freiman.section14_s0003_coverage0005_parentidx0010_specs_0064_0072
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:32:30.146021+00:00
-- url     : https://prove2.me/submissions/f8349c05-7e41-46d3-9f9f-82cb116d4526

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
namespace Section14CoverageSpec_3_5_p10_64_72
private theorem rec10642 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 218 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(0),[3,7],[10],506⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1124]? = some (⟨218,(0),[3,7],[10],506⟩) from rfl))
private theorem rec10650 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 218 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(1),[3,7],[10],507⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1132]? = some (⟨218,(1),[3,7],[10],507⟩) from rfl))
private theorem rec10658 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 218 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(2),[3,7],[10],508⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1140]? = some (⟨218,(2),[3,7],[10],508⟩) from rfl))
private theorem rec10666 (si parent : ℕ) (hs : si ∈ ([3, 7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 218 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨218,(3),[3,7],[10],509⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1148]? = some (⟨218,(3),[3,7],[10],509⟩) from rfl))
private theorem rec10755 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(0),[3,7,15],[10],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[26]? = some (⟨221,(0),[3,7,15],[10],515⟩) from rfl))
private theorem rec10763 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(1),[3,7,15],[10],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[34]? = some (⟨221,(1),[3,7,15],[10],515⟩) from rfl))
private theorem rec10771 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(2),[3,7,15],[10],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[42]? = some (⟨221,(2),[3,7,15],[10],516⟩) from rfl))
private theorem rec10779 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(3),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[50]? = some (⟨221,(3),[3,7,15],[10],517⟩) from rfl))
private theorem rec10787 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(4),[3,7,15],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[58]? = some (⟨221,(4),[3,7,15],[10],518⟩) from rfl))
private theorem rec10795 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(5),[3,7,15],[10],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[66]? = some (⟨221,(5),[3,7,15],[10],515⟩) from rfl))
private theorem rec10803 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(6),[3,7,15],[10],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[74]? = some (⟨221,(6),[3,7,15],[10],515⟩) from rfl))
private theorem rec10811 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(7),[3,7,15],[10],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[82]? = some (⟨221,(7),[3,7,15],[10],516⟩) from rfl))
private theorem rec10819 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(8),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[90]? = some (⟨221,(8),[3,7,15],[10],517⟩) from rfl))
private theorem rec10827 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(9),[3,7,15],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[98]? = some (⟨221,(9),[3,7,15],[10],518⟩) from rfl))
private theorem rec10835 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(10),[3,7,15],[10],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[106]? = some (⟨221,(10),[3,7,15],[10],519⟩) from rfl))
private theorem rec10843 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(11),[3,7,15],[10],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[114]? = some (⟨221,(11),[3,7,15],[10],519⟩) from rfl))
private theorem rec10851 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(12),[3,7,15],[10],520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[122]? = some (⟨221,(12),[3,7,15],[10],520⟩) from rfl))
private theorem rec10859 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(13),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[130]? = some (⟨221,(13),[3,7,15],[10],517⟩) from rfl))
private theorem rec10867 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(14),[3,7,15],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[138]? = some (⟨221,(14),[3,7,15],[10],518⟩) from rfl))
private theorem rec10875 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(15),[3,7,15],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[146]? = some (⟨221,(15),[3,7,15],[10],521⟩) from rfl))
private theorem rec10883 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(16),[3,7,15],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[154]? = some (⟨221,(16),[3,7,15],[10],521⟩) from rfl))
private theorem rec10891 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(17),[3,7,15],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[162]? = some (⟨221,(17),[3,7,15],[10],521⟩) from rfl))
private theorem rec10899 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(18),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[170]? = some (⟨221,(18),[3,7,15],[10],517⟩) from rfl))
private theorem rec10908 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(19),[3,7,15],[10],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[179]? = some (⟨221,(19),[3,7,15],[10],521⟩) from rfl))
private theorem rec10916 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(20),[3,7,15],[10],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[187]? = some (⟨221,(20),[3,7,15],[10],522⟩) from rfl))
private theorem rec10924 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(21),[3,7,15],[10],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[195]? = some (⟨221,(21),[3,7,15],[10],522⟩) from rfl))
private theorem rec10932 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(22),[3,7,15],[10],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[203]? = some (⟨221,(22),[3,7,15],[10],522⟩) from rfl))
private theorem rec10940 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(23),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[211]? = some (⟨221,(23),[3,7,15],[10],517⟩) from rfl))
private theorem rec10948 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 221 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(24),[3,7,15],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[219]? = some (⟨221,(24),[3,7,15],[10],518⟩) from rfl))
private theorem rec10957 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(0),[3,15],[10],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[228]? = some (⟨222,(0),[3,15],[10],735⟩) from rfl))
private theorem rec10965 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(1),[3,4,8,12,15,16],[10],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[236]? = some (⟨222,(1),[3,4,8,12,15,16],[10],736⟩) from rfl))
private theorem rec10972 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(2),[3,4,7,15,16],[10],737⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[243]? = some (⟨222,(2),[3,4,7,15,16],[10],737⟩) from rfl))
private theorem rec10980 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(3),[3,4,8,12,15,16],[10],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[251]? = some (⟨222,(3),[3,4,8,12,15,16],[10],736⟩) from rfl))
private theorem rec10987 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(4),[3,4,7,8,12,15,16],[10],525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[258]? = some (⟨222,(4),[3,4,7,8,12,15,16],[10],525⟩) from rfl))
private theorem rec10993 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(5),[3,4,8,12,15,16],[10],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[264]? = some (⟨222,(5),[3,4,8,12,15,16],[10],735⟩) from rfl))
private theorem rec11001 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(6),[3,15],[10],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[272]? = some (⟨222,(6),[3,15],[10],738⟩) from rfl))
private theorem rec11009 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(7),[3,4,7,15,16],[10],739⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[280]? = some (⟨222,(7),[3,4,7,15,16],[10],739⟩) from rfl))
private theorem rec11017 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(8),[3,4,8,12,15,16],[10],740⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[288]? = some (⟨222,(8),[3,4,8,12,15,16],[10],740⟩) from rfl))
private theorem rec11024 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(9),[3,4,7,8,12,15,16],[10],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[295]? = some (⟨222,(9),[3,4,7,8,12,15,16],[10],528⟩) from rfl))
private theorem rec11031 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(10),[3,7,15],[10],741⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[302]? = some (⟨222,(10),[3,7,15],[10],741⟩) from rfl))
private theorem rec11040 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(11),[3,7,15],[10],742⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[311]? = some (⟨222,(11),[3,7,15],[10],742⟩) from rfl))
private theorem rec11049 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(12),[3,7,15],[10],743⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[320]? = some (⟨222,(12),[3,7,15],[10],743⟩) from rfl))
private theorem rec11059 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(13),[3,7,15],[10],744⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[330]? = some (⟨222,(13),[3,7,15],[10],744⟩) from rfl))
private theorem rec11067 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(14),[3,4,7,8,12,15,16],[10],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[338]? = some (⟨222,(14),[3,4,7,8,12,15,16],[10],531⟩) from rfl))
private theorem rec11073 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(15),[3,4,8,12,15,16],[10],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[344]? = some (⟨222,(15),[3,4,8,12,15,16],[10],735⟩) from rfl))
private theorem rec11080 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(16),[3,4,8,12,15,16],[10],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[351]? = some (⟨222,(16),[3,4,8,12,15,16],[10],738⟩) from rfl))
private theorem rec11087 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(17),[3,4,7,15,16],[10],745⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[358]? = some (⟨222,(17),[3,4,7,15,16],[10],745⟩) from rfl))
private theorem rec11095 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(18),[3,4,8,12,15,16],[10],746⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[366]? = some (⟨222,(18),[3,4,8,12,15,16],[10],746⟩) from rfl))
private theorem rec11102 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(19),[3,4,7,8,12,15,16],[10],534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[373]? = some (⟨222,(19),[3,4,7,8,12,15,16],[10],534⟩) from rfl))
private theorem rec11108 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(20),[3,4,7,8,12,15,16],[10],535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[379]? = some (⟨222,(20),[3,4,7,8,12,15,16],[10],535⟩) from rfl))
private theorem rec11114 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(21),[3,4,7,8,12,15,16],[10],536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[385]? = some (⟨222,(21),[3,4,7,8,12,15,16],[10],536⟩) from rfl))
private theorem rec11120 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(22),[3,4,7,8,12,15,16],[10],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[391]? = some (⟨222,(22),[3,4,7,8,12,15,16],[10],537⟩) from rfl))
private theorem rec11126 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(23),[3,4,7,8,12,15,16],[10],538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[397]? = some (⟨222,(23),[3,4,7,8,12,15,16],[10],538⟩) from rfl))
private theorem rec11132 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 222 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(24),[3,4,7,15,16],[10],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[403]? = some (⟨222,(24),[3,4,7,15,16],[10],537⟩) from rfl))
private theorem rec11139 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(0),[3,4,7,8,12,15,16],[10],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[410]? = some (⟨224,(0),[3,4,7,8,12,15,16],[10],539⟩) from rfl))
private theorem rec11145 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(1),[3,4,7,8,12,15,16],[10],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[416]? = some (⟨224,(1),[3,4,7,8,12,15,16],[10],539⟩) from rfl))
private theorem rec11151 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(2),[3,4,7,8,12,15,16],[10],540⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[422]? = some (⟨224,(2),[3,4,7,8,12,15,16],[10],540⟩) from rfl))
private theorem rec11157 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(3),[3,4,7,8,12,15,16],[10],541⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[428]? = some (⟨224,(3),[3,4,7,8,12,15,16],[10],541⟩) from rfl))
private theorem rec11163 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(4),[3,4,7,8,12,15,16],[10],542⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[434]? = some (⟨224,(4),[3,4,7,8,12,15,16],[10],542⟩) from rfl))
private theorem rec11170 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(5),[3,7,15],[10],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[441]? = some (⟨224,(5),[3,7,15],[10],543⟩) from rfl))
private theorem rec11178 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(6),[3,7,15],[10],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[449]? = some (⟨224,(6),[3,7,15],[10],543⟩) from rfl))
private theorem rec11186 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(7),[3,7,15],[10],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[457]? = some (⟨224,(7),[3,7,15],[10],544⟩) from rfl))
private theorem rec11194 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(8),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[465]? = some (⟨224,(8),[3,7,15],[10],517⟩) from rfl))
private theorem rec11202 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(9),[3,7,15],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[473]? = some (⟨224,(9),[3,7,15],[10],518⟩) from rfl))
private theorem rec11210 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(10),[3,7,15],[10],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[481]? = some (⟨224,(10),[3,7,15],[10],545⟩) from rfl))
private theorem rec11218 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(11),[3,7,15],[10],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[489]? = some (⟨224,(11),[3,7,15],[10],545⟩) from rfl))
private theorem rec11226 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(12),[3,7,15],[10],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[497]? = some (⟨224,(12),[3,7,15],[10],544⟩) from rfl))
private theorem rec11234 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(13),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[505]? = some (⟨224,(13),[3,7,15],[10],517⟩) from rfl))
private theorem rec11242 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(14),[3,7,15],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[513]? = some (⟨224,(14),[3,7,15],[10],518⟩) from rfl))
private theorem rec11250 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(15),[3,7,15],[10],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[521]? = some (⟨224,(15),[3,7,15],[10],546⟩) from rfl))
private theorem rec11258 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(16),[3,7,15],[10],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[529]? = some (⟨224,(16),[3,7,15],[10],546⟩) from rfl))
private theorem rec11266 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(17),[3,7,15],[10],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[537]? = some (⟨224,(17),[3,7,15],[10],544⟩) from rfl))
private theorem rec11274 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(18),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[545]? = some (⟨224,(18),[3,7,15],[10],517⟩) from rfl))
private theorem rec11282 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(19),[3,7,15],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[553]? = some (⟨224,(19),[3,7,15],[10],518⟩) from rfl))
private theorem rec11290 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(20),[3,7,15],[10],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[561]? = some (⟨224,(20),[3,7,15],[10],547⟩) from rfl))
private theorem rec11298 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(21),[3,7,15],[10],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[569]? = some (⟨224,(21),[3,7,15],[10],547⟩) from rfl))
private theorem rec11306 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(22),[3,7,15],[10],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[577]? = some (⟨224,(22),[3,7,15],[10],547⟩) from rfl))
private theorem rec11314 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(23),[3,7,15],[10],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[585]? = some (⟨224,(23),[3,7,15],[10],517⟩) from rfl))
private theorem rec11322 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 224 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(24),[3,7,15],[10],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[593]? = some (⟨224,(24),[3,7,15],[10],518⟩) from rfl))
private theorem rec11329 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[600]? = some (⟨225,(0),[3,4,7,8,12,15,16],[10],747⟩) from rfl))
private theorem rec11335 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[606]? = some (⟨225,(1),[3,4,7,8,12,15,16],[10],748⟩) from rfl))
private theorem rec11342 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[613]? = some (⟨225,(2),[3,4,7,8,12,15,16],[10],749⟩) from rfl))
private theorem rec11349 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[620]? = some (⟨225,(3),[3,4,7,8,12,15,16],[10],750⟩) from rfl))
private theorem rec11356 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[627]? = some (⟨225,(4),[3,4,7,8,12,15,16],[10],749⟩) from rfl))
private theorem rec11362 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[633]? = some (⟨225,(5),[3,4,7,8,12,15,16],[10],751⟩) from rfl))
private theorem rec11368 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[639]? = some (⟨225,(6),[3,4,7,8,12,15,16],[10],752⟩) from rfl))
private theorem rec11375 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(7),[3,7,15],[10],753⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[646]? = some (⟨225,(7),[3,7,15],[10],753⟩) from rfl))
private theorem rec11383 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[654]? = some (⟨225,(8),[3,4,7,8,12,15,16],[10],754⟩) from rfl))
private theorem rec11390 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(9),[3,7,15],[10],753⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[661]? = some (⟨225,(9),[3,7,15],[10],753⟩) from rfl))
private theorem rec11397 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[668]? = some (⟨225,(10),[3,4,7,8,12,15,16],[10],755⟩) from rfl))
private theorem rec11403 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[674]? = some (⟨225,(11),[3,4,7,8,12,15,16],[10],756⟩) from rfl))
private theorem rec11410 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(12),[3,7,15],[10],757⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[681]? = some (⟨225,(12),[3,7,15],[10],757⟩) from rfl))
private theorem rec11418 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[689]? = some (⟨225,(13),[3,4,7,8,12,15,16],[10],758⟩) from rfl))
private theorem rec11425 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(14),[3,7,15],[10],757⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[696]? = some (⟨225,(14),[3,7,15],[10],757⟩) from rfl))
private theorem rec11432 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[703]? = some (⟨225,(15),[3,4,7,8,12,15,16],[10],759⟩) from rfl))
private theorem rec11438 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[709]? = some (⟨225,(16),[3,4,7,8,12,15,16],[10],760⟩) from rfl))
private theorem rec11445 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(17),[3,7,15],[10],761⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[716]? = some (⟨225,(17),[3,7,15],[10],761⟩) from rfl))
private theorem rec11453 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[724]? = some (⟨225,(18),[3,4,7,8,12,15,16],[10],762⟩) from rfl))
private theorem rec11460 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(19),[3,7,15],[10],761⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[731]? = some (⟨225,(19),[3,7,15],[10],761⟩) from rfl))
private theorem rec11467 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[738]? = some (⟨225,(20),[3,4,7,8,12,15,16],[10],763⟩) from rfl))
private theorem rec11473 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[744]? = some (⟨225,(21),[3,4,7,8,12,15,16],[10],764⟩) from rfl))
private theorem rec11480 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(22),[3,7,15],[10],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[751]? = some (⟨225,(22),[3,7,15],[10],547⟩) from rfl))
private theorem rec11488 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[759]? = some (⟨225,(23),[3,4,7,8,12,15,16],[10],765⟩) from rfl))
private theorem rec11495 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 225 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(24),[3,7,15],[10],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[766]? = some (⟨225,(24),[3,7,15],[10],547⟩) from rfl))
private theorem rec15131 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 408 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨408,(0),[3,15],[10],957⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[210]? = some (⟨408,(0),[3,15],[10],957⟩) from rfl))
private theorem rec15135 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 408 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨408,(1),[3,7,15],[10],958⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[214]? = some (⟨408,(1),[3,7,15],[10],958⟩) from rfl))
private theorem rec15138 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 408 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨408,(2),[3,7,15],[10],959⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[217]? = some (⟨408,(2),[3,7,15],[10],959⟩) from rfl))
private theorem rec15141 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 408 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨408,(3),[3,7,15],[10],960⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[220]? = some (⟨408,(3),[3,7,15],[10],960⟩) from rfl))
private theorem rec15144 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 408 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨408,(4),[3,7,15],[10],961⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[223]? = some (⟨408,(4),[3,7,15],[10],961⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 10 gs.1 j := by
  have hp : ((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 64).take 8) = [(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 218)).length = 4 := by decide +kernel
    have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec10642 3 10 (by decide) (by decide)
    · right
      exact rec10650 3 10 (by decide) (by decide)
    · right
      exact rec10658 3 10 (by decide) (by decide)
    · right
      exact rec10666 3 10 (by decide) (by decide)
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 408)).length = 5 := by decide +kernel
    have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec15131 3 10 (by decide) (by decide)
    · right
      exact rec15135 3 10 (by decide) (by decide)
    · right
      exact rec15138 3 10 (by decide) (by decide)
    · right
      exact rec15141 3 10 (by decide) (by decide)
    · right
      exact rec15144 3 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 221)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec10755 3 10 (by decide) (by decide)
    · right
      exact rec10763 3 10 (by decide) (by decide)
    · right
      exact rec10771 3 10 (by decide) (by decide)
    · right
      exact rec10779 3 10 (by decide) (by decide)
    · right
      exact rec10787 3 10 (by decide) (by decide)
    · right
      exact rec10795 3 10 (by decide) (by decide)
    · right
      exact rec10803 3 10 (by decide) (by decide)
    · right
      exact rec10811 3 10 (by decide) (by decide)
    · right
      exact rec10819 3 10 (by decide) (by decide)
    · right
      exact rec10827 3 10 (by decide) (by decide)
    · right
      exact rec10835 3 10 (by decide) (by decide)
    · right
      exact rec10843 3 10 (by decide) (by decide)
    · right
      exact rec10851 3 10 (by decide) (by decide)
    · right
      exact rec10859 3 10 (by decide) (by decide)
    · right
      exact rec10867 3 10 (by decide) (by decide)
    · right
      exact rec10875 3 10 (by decide) (by decide)
    · right
      exact rec10883 3 10 (by decide) (by decide)
    · right
      exact rec10891 3 10 (by decide) (by decide)
    · right
      exact rec10899 3 10 (by decide) (by decide)
    · right
      exact rec10908 3 10 (by decide) (by decide)
    · right
      exact rec10916 3 10 (by decide) (by decide)
    · right
      exact rec10924 3 10 (by decide) (by decide)
    · right
      exact rec10932 3 10 (by decide) (by decide)
    · right
      exact rec10940 3 10 (by decide) (by decide)
    · right
      exact rec10948 3 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 222)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec10957 3 10 (by decide) (by decide)
    · right
      exact rec10965 3 10 (by decide) (by decide)
    · right
      exact rec10972 3 10 (by decide) (by decide)
    · right
      exact rec10980 3 10 (by decide) (by decide)
    · right
      exact rec10987 3 10 (by decide) (by decide)
    · right
      exact rec10993 3 10 (by decide) (by decide)
    · right
      exact rec11001 3 10 (by decide) (by decide)
    · right
      exact rec11009 3 10 (by decide) (by decide)
    · right
      exact rec11017 3 10 (by decide) (by decide)
    · right
      exact rec11024 3 10 (by decide) (by decide)
    · right
      exact rec11031 3 10 (by decide) (by decide)
    · right
      exact rec11040 3 10 (by decide) (by decide)
    · right
      exact rec11049 3 10 (by decide) (by decide)
    · right
      exact rec11059 3 10 (by decide) (by decide)
    · right
      exact rec11067 3 10 (by decide) (by decide)
    · right
      exact rec11073 3 10 (by decide) (by decide)
    · right
      exact rec11080 3 10 (by decide) (by decide)
    · right
      exact rec11087 3 10 (by decide) (by decide)
    · right
      exact rec11095 3 10 (by decide) (by decide)
    · right
      exact rec11102 3 10 (by decide) (by decide)
    · right
      exact rec11108 3 10 (by decide) (by decide)
    · right
      exact rec11114 3 10 (by decide) (by decide)
    · right
      exact rec11120 3 10 (by decide) (by decide)
    · right
      exact rec11126 3 10 (by decide) (by decide)
    · right
      exact rec11132 3 10 (by decide) (by decide)
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
      exact rec11139 3 10 (by decide) (by decide)
    · right
      exact rec11145 3 10 (by decide) (by decide)
    · right
      exact rec11151 3 10 (by decide) (by decide)
    · right
      exact rec11157 3 10 (by decide) (by decide)
    · right
      exact rec11163 3 10 (by decide) (by decide)
    · right
      exact rec11170 3 10 (by decide) (by decide)
    · right
      exact rec11178 3 10 (by decide) (by decide)
    · right
      exact rec11186 3 10 (by decide) (by decide)
    · right
      exact rec11194 3 10 (by decide) (by decide)
    · right
      exact rec11202 3 10 (by decide) (by decide)
    · right
      exact rec11210 3 10 (by decide) (by decide)
    · right
      exact rec11218 3 10 (by decide) (by decide)
    · right
      exact rec11226 3 10 (by decide) (by decide)
    · right
      exact rec11234 3 10 (by decide) (by decide)
    · right
      exact rec11242 3 10 (by decide) (by decide)
    · right
      exact rec11250 3 10 (by decide) (by decide)
    · right
      exact rec11258 3 10 (by decide) (by decide)
    · right
      exact rec11266 3 10 (by decide) (by decide)
    · right
      exact rec11274 3 10 (by decide) (by decide)
    · right
      exact rec11282 3 10 (by decide) (by decide)
    · right
      exact rec11290 3 10 (by decide) (by decide)
    · right
      exact rec11298 3 10 (by decide) (by decide)
    · right
      exact rec11306 3 10 (by decide) (by decide)
    · right
      exact rec11314 3 10 (by decide) (by decide)
    · right
      exact rec11322 3 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 225)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11329 3 10 (by decide) (by decide)
    · right
      exact rec11335 3 10 (by decide) (by decide)
    · right
      exact rec11342 3 10 (by decide) (by decide)
    · right
      exact rec11349 3 10 (by decide) (by decide)
    · right
      exact rec11356 3 10 (by decide) (by decide)
    · right
      exact rec11362 3 10 (by decide) (by decide)
    · right
      exact rec11368 3 10 (by decide) (by decide)
    · right
      exact rec11375 3 10 (by decide) (by decide)
    · right
      exact rec11383 3 10 (by decide) (by decide)
    · right
      exact rec11390 3 10 (by decide) (by decide)
    · right
      exact rec11397 3 10 (by decide) (by decide)
    · right
      exact rec11403 3 10 (by decide) (by decide)
    · right
      exact rec11410 3 10 (by decide) (by decide)
    · right
      exact rec11418 3 10 (by decide) (by decide)
    · right
      exact rec11425 3 10 (by decide) (by decide)
    · right
      exact rec11432 3 10 (by decide) (by decide)
    · right
      exact rec11438 3 10 (by decide) (by decide)
    · right
      exact rec11445 3 10 (by decide) (by decide)
    · right
      exact rec11453 3 10 (by decide) (by decide)
    · right
      exact rec11460 3 10 (by decide) (by decide)
    · right
      exact rec11467 3 10 (by decide) (by decide)
    · right
      exact rec11473 3 10 (by decide) (by decide)
    · right
      exact rec11480 3 10 (by decide) (by decide)
    · right
      exact rec11488 3 10 (by decide) (by decide)
    · right
      exact rec11495 3 10 (by decide) (by decide)
end Section14CoverageSpec_3_5_p10_64_72

#print axioms solution
