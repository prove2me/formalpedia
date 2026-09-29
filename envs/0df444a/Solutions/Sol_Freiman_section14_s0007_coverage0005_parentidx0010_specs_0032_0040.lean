-- Prove2me | solution 1 for Freiman.section14_s0007_coverage0005_parentidx0010_specs_0032_0040
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:14:58.792717+00:00
-- url     : https://prove2.me/submissions/e7c917f5-151f-4de8-a52a-483bc414f951

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
namespace Section14CoverageSpec_7_5_p10_32_40
private theorem rec8865 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(0),[3,7,15],[10],684⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[566]? = some (⟨188,(0),[3,7,15],[10],684⟩) from rfl))
private theorem rec8873 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(1),[3,7,15],[10],685⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[574]? = some (⟨188,(1),[3,7,15],[10],685⟩) from rfl))
private theorem rec8881 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(2),[3,7,15],[10],684⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[582]? = some (⟨188,(2),[3,7,15],[10],684⟩) from rfl))
private theorem rec8889 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(3),[3,7,15],[10],686⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[590]? = some (⟨188,(3),[3,7,15],[10],686⟩) from rfl))
private theorem rec8897 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(4),[3,7,15],[10],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[598]? = some (⟨188,(4),[3,7,15],[10],687⟩) from rfl))
private theorem rec8905 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(5),[3,7,15],[10],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[606]? = some (⟨188,(5),[3,7,15],[10],687⟩) from rfl))
private theorem rec8913 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(6),[3,7,15],[10],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[614]? = some (⟨188,(6),[3,7,15],[10],687⟩) from rfl))
private theorem rec8921 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(7),[3,7,15],[10],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[622]? = some (⟨188,(7),[3,7,15],[10],687⟩) from rfl))
private theorem rec8929 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(8),[3,7,15],[10],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[630]? = some (⟨188,(8),[3,7,15],[10],688⟩) from rfl))
private theorem rec8937 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(9),[3,7,15],[10],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[638]? = some (⟨188,(9),[3,7,15],[10],688⟩) from rfl))
private theorem rec8945 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(10),[3,7,15],[10],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[646]? = some (⟨188,(10),[3,7,15],[10],688⟩) from rfl))
private theorem rec8953 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(11),[3,7,15],[10],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[654]? = some (⟨188,(11),[3,7,15],[10],688⟩) from rfl))
private theorem rec8961 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(12),[3,7,15],[10],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[662]? = some (⟨188,(12),[3,7,15],[10],689⟩) from rfl))
private theorem rec8969 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(13),[3,7,15],[10],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[670]? = some (⟨188,(13),[3,7,15],[10],689⟩) from rfl))
private theorem rec8977 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(14),[3,7,15],[10],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[678]? = some (⟨188,(14),[3,7,15],[10],689⟩) from rfl))
private theorem rec8985 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 188 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(15),[3,7,15],[10],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[686]? = some (⟨188,(15),[3,7,15],[10],689⟩) from rfl))
private theorem rec8995 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(0),[7],[10],1581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[696]? = some (⟨190,(0),[7],[10],1581⟩) from rfl))
private theorem rec9002 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(1),[7],[10],1581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[703]? = some (⟨190,(1),[7],[10],1581⟩) from rfl))
private theorem rec9009 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(2),[7],[10],1581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[710]? = some (⟨190,(2),[7],[10],1581⟩) from rfl))
private theorem rec9016 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(3),[7],[10],1581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[717]? = some (⟨190,(3),[7],[10],1581⟩) from rfl))
private theorem rec9023 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(4),[7],[10],1581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[724]? = some (⟨190,(4),[7],[10],1581⟩) from rfl))
private theorem rec9030 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(5),[7],[10],1582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[731]? = some (⟨190,(5),[7],[10],1582⟩) from rfl))
private theorem rec9037 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(6),[7],[10],1582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[738]? = some (⟨190,(6),[7],[10],1582⟩) from rfl))
private theorem rec9044 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(7),[7],[10],1582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[745]? = some (⟨190,(7),[7],[10],1582⟩) from rfl))
private theorem rec9051 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(8),[7],[10],1582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[752]? = some (⟨190,(8),[7],[10],1582⟩) from rfl))
private theorem rec9058 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(9),[7],[10],1582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[759]? = some (⟨190,(9),[7],[10],1582⟩) from rfl))
private theorem rec9065 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(10),[7],[10],1583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[766]? = some (⟨190,(10),[7],[10],1583⟩) from rfl))
private theorem rec9072 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(11),[7],[10],1584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[773]? = some (⟨190,(11),[7],[10],1584⟩) from rfl))
private theorem rec9079 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(12),[7],[10],1585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[780]? = some (⟨190,(12),[7],[10],1585⟩) from rfl))
private theorem rec9086 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(13),[7],[10],1584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[787]? = some (⟨190,(13),[7],[10],1584⟩) from rfl))
private theorem rec9093 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(14),[7],[10],1586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[794]? = some (⟨190,(14),[7],[10],1586⟩) from rfl))
private theorem rec9100 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(15),[7],[10],1583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[801]? = some (⟨190,(15),[7],[10],1583⟩) from rfl))
private theorem rec9107 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(16),[7],[10],1587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[808]? = some (⟨190,(16),[7],[10],1587⟩) from rfl))
private theorem rec9114 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(17),[7],[10],1587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[815]? = some (⟨190,(17),[7],[10],1587⟩) from rfl))
private theorem rec9121 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(18),[7],[10],1587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[822]? = some (⟨190,(18),[7],[10],1587⟩) from rfl))
private theorem rec9128 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(19),[7],[10],1587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[829]? = some (⟨190,(19),[7],[10],1587⟩) from rfl))
private theorem rec9135 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(20),[7],[10],1583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[836]? = some (⟨190,(20),[7],[10],1583⟩) from rfl))
private theorem rec9142 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(21),[7],[10],1584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[843]? = some (⟨190,(21),[7],[10],1584⟩) from rfl))
private theorem rec9149 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(22),[7],[10],1585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[850]? = some (⟨190,(22),[7],[10],1585⟩) from rfl))
private theorem rec9156 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(23),[7],[10],1584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[857]? = some (⟨190,(23),[7],[10],1584⟩) from rfl))
private theorem rec9163 (si parent : ℕ) (hs : si ∈ ([7] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 190 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(24),[7],[10],1586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[864]? = some (⟨190,(24),[7],[10],1586⟩) from rfl))
private theorem rec9168 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(0),[3,7,15],[10],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[869]? = some (⟨192,(0),[3,7,15],[10],441⟩) from rfl))
private theorem rec9176 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(1),[3,7,15],[10],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[877]? = some (⟨192,(1),[3,7,15],[10],442⟩) from rfl))
private theorem rec9184 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(2),[3,7,15],[10],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[885]? = some (⟨192,(2),[3,7,15],[10],441⟩) from rfl))
private theorem rec9192 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(3),[3,7,15],[10],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[893]? = some (⟨192,(3),[3,7,15],[10],443⟩) from rfl))
private theorem rec9200 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(4),[3,7,15],[10],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[901]? = some (⟨192,(4),[3,7,15],[10],444⟩) from rfl))
private theorem rec9208 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(5),[3,7,15],[10],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[909]? = some (⟨192,(5),[3,7,15],[10],441⟩) from rfl))
private theorem rec9216 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(6),[3,7,15],[10],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[917]? = some (⟨192,(6),[3,7,15],[10],442⟩) from rfl))
private theorem rec9224 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(7),[3,7,15],[10],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[925]? = some (⟨192,(7),[3,7,15],[10],441⟩) from rfl))
private theorem rec9232 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(8),[3,7,15],[10],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[933]? = some (⟨192,(8),[3,7,15],[10],443⟩) from rfl))
private theorem rec9240 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(9),[3,7,15],[10],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[941]? = some (⟨192,(9),[3,7,15],[10],444⟩) from rfl))
private theorem rec9248 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(10),[3,7,15],[10],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[949]? = some (⟨192,(10),[3,7,15],[10],445⟩) from rfl))
private theorem rec9256 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(11),[3,7,15],[10],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[957]? = some (⟨192,(11),[3,7,15],[10],445⟩) from rfl))
private theorem rec9264 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(12),[3,7,15],[10],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[965]? = some (⟨192,(12),[3,7,15],[10],445⟩) from rfl))
private theorem rec9272 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(13),[3,7,15],[10],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[973]? = some (⟨192,(13),[3,7,15],[10],445⟩) from rfl))
private theorem rec9280 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(14),[3,7,15],[10],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[981]? = some (⟨192,(14),[3,7,15],[10],444⟩) from rfl))
private theorem rec9288 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(15),[3,7,15],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[989]? = some (⟨192,(15),[3,7,15],[10],446⟩) from rfl))
private theorem rec9296 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(16),[3,7,15],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[997]? = some (⟨192,(16),[3,7,15],[10],446⟩) from rfl))
private theorem rec9304 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(17),[3,7,15],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1005]? = some (⟨192,(17),[3,7,15],[10],446⟩) from rfl))
private theorem rec9312 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(18),[3,7,15],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1013]? = some (⟨192,(18),[3,7,15],[10],446⟩) from rfl))
private theorem rec9320 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(19),[3,7,15],[10],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1021]? = some (⟨192,(19),[3,7,15],[10],446⟩) from rfl))
private theorem rec9328 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(20),[3,7,15],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1029]? = some (⟨192,(20),[3,7,15],[10],447⟩) from rfl))
private theorem rec9336 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(21),[3,7,15],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1037]? = some (⟨192,(21),[3,7,15],[10],447⟩) from rfl))
private theorem rec9344 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(22),[3,7,15],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1045]? = some (⟨192,(22),[3,7,15],[10],447⟩) from rfl))
private theorem rec9352 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(23),[3,7,15],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1053]? = some (⟨192,(23),[3,7,15],[10],447⟩) from rfl))
private theorem rec9360 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 192 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(24),[3,7,15],[10],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1061]? = some (⟨192,(24),[3,7,15],[10],447⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 32).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 7 10 gs.1 j := by
  have hp : ((section14State section14Catalog 7).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 32).take 8) = [(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      exact rec8865 7 10 (by decide) (by decide)
    · right
      exact rec8873 7 10 (by decide) (by decide)
    · right
      exact rec8881 7 10 (by decide) (by decide)
    · right
      exact rec8889 7 10 (by decide) (by decide)
    · right
      exact rec8897 7 10 (by decide) (by decide)
    · right
      exact rec8905 7 10 (by decide) (by decide)
    · right
      exact rec8913 7 10 (by decide) (by decide)
    · right
      exact rec8921 7 10 (by decide) (by decide)
    · right
      exact rec8929 7 10 (by decide) (by decide)
    · right
      exact rec8937 7 10 (by decide) (by decide)
    · right
      exact rec8945 7 10 (by decide) (by decide)
    · right
      exact rec8953 7 10 (by decide) (by decide)
    · right
      exact rec8961 7 10 (by decide) (by decide)
    · right
      exact rec8969 7 10 (by decide) (by decide)
    · right
      exact rec8977 7 10 (by decide) (by decide)
    · right
      exact rec8985 7 10 (by decide) (by decide)
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
      exact rec8995 7 10 (by decide) (by decide)
    · right
      exact rec9002 7 10 (by decide) (by decide)
    · right
      exact rec9009 7 10 (by decide) (by decide)
    · right
      exact rec9016 7 10 (by decide) (by decide)
    · right
      exact rec9023 7 10 (by decide) (by decide)
    · right
      exact rec9030 7 10 (by decide) (by decide)
    · right
      exact rec9037 7 10 (by decide) (by decide)
    · right
      exact rec9044 7 10 (by decide) (by decide)
    · right
      exact rec9051 7 10 (by decide) (by decide)
    · right
      exact rec9058 7 10 (by decide) (by decide)
    · right
      exact rec9065 7 10 (by decide) (by decide)
    · right
      exact rec9072 7 10 (by decide) (by decide)
    · right
      exact rec9079 7 10 (by decide) (by decide)
    · right
      exact rec9086 7 10 (by decide) (by decide)
    · right
      exact rec9093 7 10 (by decide) (by decide)
    · right
      exact rec9100 7 10 (by decide) (by decide)
    · right
      exact rec9107 7 10 (by decide) (by decide)
    · right
      exact rec9114 7 10 (by decide) (by decide)
    · right
      exact rec9121 7 10 (by decide) (by decide)
    · right
      exact rec9128 7 10 (by decide) (by decide)
    · right
      exact rec9135 7 10 (by decide) (by decide)
    · right
      exact rec9142 7 10 (by decide) (by decide)
    · right
      exact rec9149 7 10 (by decide) (by decide)
    · right
      exact rec9156 7 10 (by decide) (by decide)
    · right
      exact rec9163 7 10 (by decide) (by decide)
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
      exact rec9168 7 10 (by decide) (by decide)
    · right
      exact rec9176 7 10 (by decide) (by decide)
    · right
      exact rec9184 7 10 (by decide) (by decide)
    · right
      exact rec9192 7 10 (by decide) (by decide)
    · right
      exact rec9200 7 10 (by decide) (by decide)
    · right
      exact rec9208 7 10 (by decide) (by decide)
    · right
      exact rec9216 7 10 (by decide) (by decide)
    · right
      exact rec9224 7 10 (by decide) (by decide)
    · right
      exact rec9232 7 10 (by decide) (by decide)
    · right
      exact rec9240 7 10 (by decide) (by decide)
    · right
      exact rec9248 7 10 (by decide) (by decide)
    · right
      exact rec9256 7 10 (by decide) (by decide)
    · right
      exact rec9264 7 10 (by decide) (by decide)
    · right
      exact rec9272 7 10 (by decide) (by decide)
    · right
      exact rec9280 7 10 (by decide) (by decide)
    · right
      exact rec9288 7 10 (by decide) (by decide)
    · right
      exact rec9296 7 10 (by decide) (by decide)
    · right
      exact rec9304 7 10 (by decide) (by decide)
    · right
      exact rec9312 7 10 (by decide) (by decide)
    · right
      exact rec9320 7 10 (by decide) (by decide)
    · right
      exact rec9328 7 10 (by decide) (by decide)
    · right
      exact rec9336 7 10 (by decide) (by decide)
    · right
      exact rec9344 7 10 (by decide) (by decide)
    · right
      exact rec9352 7 10 (by decide) (by decide)
    · right
      exact rec9360 7 10 (by decide) (by decide)
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
end Section14CoverageSpec_7_5_p10_32_40

#print axioms solution
