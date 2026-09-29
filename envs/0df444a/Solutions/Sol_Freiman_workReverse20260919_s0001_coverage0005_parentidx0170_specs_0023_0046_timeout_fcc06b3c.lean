-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_coverage0005_parentidx0170_specs_0023_0046_timeout_fcc06b3c
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T23:41:20.856304+00:00
-- url     : https://prove2.me/submissions/fc4fd18c-e260-4327-8fcf-19e7b7acdcad

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
namespace Section14CoverageSpec_1_5_p170_23_46
private theorem rec8383 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(0),[1,2,5,6,13,14],[170],660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[84]? = some (⟨178,(0),[1,2,5,6,13,14],[170],660⟩) from rfl))
private theorem rec8391 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(1),[1,2,5,6,13,14],[170],661⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[92]? = some (⟨178,(1),[1,2,5,6,13,14],[170],661⟩) from rfl))
private theorem rec8399 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(2),[1,2,5,6,13,14],[170],660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[100]? = some (⟨178,(2),[1,2,5,6,13,14],[170],660⟩) from rfl))
private theorem rec8407 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(3),[1,2,5,6,13,14],[170],662⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[108]? = some (⟨178,(3),[1,2,5,6,13,14],[170],662⟩) from rfl))
private theorem rec8415 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(4),[1,2,5,6,13,14],[170],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[116]? = some (⟨178,(4),[1,2,5,6,13,14],[170],663⟩) from rfl))
private theorem rec8423 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(5),[1,2,5,6,13,14],[170],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[124]? = some (⟨178,(5),[1,2,5,6,13,14],[170],663⟩) from rfl))
private theorem rec8431 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(6),[1,2,5,6,13,14],[170],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[132]? = some (⟨178,(6),[1,2,5,6,13,14],[170],663⟩) from rfl))
private theorem rec8439 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(7),[1,2,5,6,13,14],[170],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[140]? = some (⟨178,(7),[1,2,5,6,13,14],[170],663⟩) from rfl))
private theorem rec8447 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(8),[1,2,5,6,13,14],[170],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[148]? = some (⟨178,(8),[1,2,5,6,13,14],[170],664⟩) from rfl))
private theorem rec8455 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(9),[1,2,5,6,13,14],[170],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[156]? = some (⟨178,(9),[1,2,5,6,13,14],[170],664⟩) from rfl))
private theorem rec8463 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(10),[1,2,5,6,13,14],[170],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[164]? = some (⟨178,(10),[1,2,5,6,13,14],[170],664⟩) from rfl))
private theorem rec8471 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(11),[1,2,5,6,13,14],[170],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[172]? = some (⟨178,(11),[1,2,5,6,13,14],[170],664⟩) from rfl))
private theorem rec8479 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(12),[1,2,5,6,13,14],[170],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[180]? = some (⟨178,(12),[1,2,5,6,13,14],[170],665⟩) from rfl))
private theorem rec8487 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(13),[1,2,5,6,13,14],[170],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[188]? = some (⟨178,(13),[1,2,5,6,13,14],[170],665⟩) from rfl))
private theorem rec8495 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(14),[1,2,5,6,13,14],[170],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[196]? = some (⟨178,(14),[1,2,5,6,13,14],[170],665⟩) from rfl))
private theorem rec8503 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(15),[1,2,5,6,13,14],[170],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[204]? = some (⟨178,(15),[1,2,5,6,13,14],[170],665⟩) from rfl))
private theorem rec8511 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(0),[1,2,5,6,13,14],[170],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[212]? = some (⟨180,(0),[1,2,5,6,13,14],[170],666⟩) from rfl))
private theorem rec8518 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(1),[1,2,5,6,13,14],[170],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[219]? = some (⟨180,(1),[1,2,5,6,13,14],[170],667⟩) from rfl))
private theorem rec8525 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(2),[1,2,5,6,13,14],[170],668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[226]? = some (⟨180,(2),[1,2,5,6,13,14],[170],668⟩) from rfl))
private theorem rec8532 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(3),[1,2,5,6,13,14],[170],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[233]? = some (⟨180,(3),[1,2,5,6,13,14],[170],669⟩) from rfl))
private theorem rec8539 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(4),[1,2,5,6,13,14],[170],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[240]? = some (⟨180,(4),[1,2,5,6,13,14],[170],666⟩) from rfl))
private theorem rec8546 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(5),[1,2,5,6,13,14],[170],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[247]? = some (⟨180,(5),[1,2,5,6,13,14],[170],667⟩) from rfl))
private theorem rec8553 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(6),[1,2,5,6,13,14],[170],670⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[254]? = some (⟨180,(6),[1,2,5,6,13,14],[170],670⟩) from rfl))
private theorem rec8560 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(7),[1,2,5,6,13,14],[170],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[261]? = some (⟨180,(7),[1,2,5,6,13,14],[170],669⟩) from rfl))
private theorem rec8567 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(8),[1,2,5,6,13,14],[170],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[268]? = some (⟨180,(8),[1,2,5,6,13,14],[170],666⟩) from rfl))
private theorem rec8574 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(9),[1,2,5,6,13,14],[170],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[275]? = some (⟨180,(9),[1,2,5,6,13,14],[170],667⟩) from rfl))
private theorem rec8581 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(10),[1,2,5,6,13,14],[170],668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[282]? = some (⟨180,(10),[1,2,5,6,13,14],[170],668⟩) from rfl))
private theorem rec8588 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(11),[1,2,5,6,13,14],[170],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[289]? = some (⟨180,(11),[1,2,5,6,13,14],[170],669⟩) from rfl))
private theorem rec8595 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(12),[1,2,5,6,13,14],[170],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[296]? = some (⟨180,(12),[1,2,5,6,13,14],[170],666⟩) from rfl))
private theorem rec8602 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(13),[1,2,5,6,13,14],[170],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[303]? = some (⟨180,(13),[1,2,5,6,13,14],[170],667⟩) from rfl))
private theorem rec8609 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(14),[1,2,5,6,13,14],[170],671⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[310]? = some (⟨180,(14),[1,2,5,6,13,14],[170],671⟩) from rfl))
private theorem rec8616 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(15),[1,2,5,6,13,14],[170],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[317]? = some (⟨180,(15),[1,2,5,6,13,14],[170],669⟩) from rfl))
private theorem rec8623 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(0),[1,2,5,6,13,14],[170],672⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[324]? = some (⟨183,(0),[1,2,5,6,13,14],[170],672⟩) from rfl))
private theorem rec8631 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(1),[1,2,5,6,13,14],[170],673⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[332]? = some (⟨183,(1),[1,2,5,6,13,14],[170],673⟩) from rfl))
private theorem rec8639 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(2),[1,2,5,6,13,14],[170],672⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[340]? = some (⟨183,(2),[1,2,5,6,13,14],[170],672⟩) from rfl))
private theorem rec8647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(3),[1,2,5,6,13,14],[170],674⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[348]? = some (⟨183,(3),[1,2,5,6,13,14],[170],674⟩) from rfl))
private theorem rec8655 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(4),[1,2,5,6,13,14],[170],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[356]? = some (⟨183,(4),[1,2,5,6,13,14],[170],675⟩) from rfl))
private theorem rec8663 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(5),[1,2,5,6,13,14],[170],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[364]? = some (⟨183,(5),[1,2,5,6,13,14],[170],675⟩) from rfl))
private theorem rec8671 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(6),[1,2,5,6,13,14],[170],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[372]? = some (⟨183,(6),[1,2,5,6,13,14],[170],675⟩) from rfl))
private theorem rec8679 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(7),[1,2,5,6,13,14],[170],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[380]? = some (⟨183,(7),[1,2,5,6,13,14],[170],675⟩) from rfl))
private theorem rec8687 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(8),[1,2,5,6,13,14],[170],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[388]? = some (⟨183,(8),[1,2,5,6,13,14],[170],676⟩) from rfl))
private theorem rec8695 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(9),[1,2,5,6,13,14],[170],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[396]? = some (⟨183,(9),[1,2,5,6,13,14],[170],676⟩) from rfl))
private theorem rec8703 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(10),[1,2,5,6,13,14],[170],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[404]? = some (⟨183,(10),[1,2,5,6,13,14],[170],676⟩) from rfl))
private theorem rec8711 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(11),[1,2,5,6,13,14],[170],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[412]? = some (⟨183,(11),[1,2,5,6,13,14],[170],676⟩) from rfl))
private theorem rec8719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(12),[1,2,5,6,13,14],[170],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[420]? = some (⟨183,(12),[1,2,5,6,13,14],[170],677⟩) from rfl))
private theorem rec8727 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(13),[1,2,5,6,13,14],[170],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[428]? = some (⟨183,(13),[1,2,5,6,13,14],[170],677⟩) from rfl))
private theorem rec8735 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(14),[1,2,5,6,13,14],[170],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[436]? = some (⟨183,(14),[1,2,5,6,13,14],[170],677⟩) from rfl))
private theorem rec8743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(15),[1,2,5,6,13,14],[170],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[444]? = some (⟨183,(15),[1,2,5,6,13,14],[170],677⟩) from rfl))
private theorem rec8751 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(0),[1,2,5,6,13,14],[170],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[452]? = some (⟨185,(0),[1,2,5,6,13,14],[170],678⟩) from rfl))
private theorem rec8758 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(1),[1,2,5,6,13,14],[170],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[459]? = some (⟨185,(1),[1,2,5,6,13,14],[170],679⟩) from rfl))
private theorem rec8765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(2),[1,2,5,6,13,14],[170],680⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[466]? = some (⟨185,(2),[1,2,5,6,13,14],[170],680⟩) from rfl))
private theorem rec8772 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(3),[1,2,5,6,13,14],[170],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[473]? = some (⟨185,(3),[1,2,5,6,13,14],[170],681⟩) from rfl))
private theorem rec8779 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(4),[1,2,5,6,13,14],[170],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[480]? = some (⟨185,(4),[1,2,5,6,13,14],[170],678⟩) from rfl))
private theorem rec8786 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(5),[1,2,5,6,13,14],[170],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[487]? = some (⟨185,(5),[1,2,5,6,13,14],[170],679⟩) from rfl))
private theorem rec8793 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(6),[1,2,5,6,13,14],[170],682⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[494]? = some (⟨185,(6),[1,2,5,6,13,14],[170],682⟩) from rfl))
private theorem rec8800 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(7),[1,2,5,6,13,14],[170],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[501]? = some (⟨185,(7),[1,2,5,6,13,14],[170],681⟩) from rfl))
private theorem rec8807 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(8),[1,2,5,6,13,14],[170],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[508]? = some (⟨185,(8),[1,2,5,6,13,14],[170],678⟩) from rfl))
private theorem rec8814 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(9),[1,2,5,6,13,14],[170],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[515]? = some (⟨185,(9),[1,2,5,6,13,14],[170],679⟩) from rfl))
private theorem rec8821 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(10),[1,2,5,6,13,14],[170],680⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[522]? = some (⟨185,(10),[1,2,5,6,13,14],[170],680⟩) from rfl))
private theorem rec8828 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(11),[1,2,5,6,13,14],[170],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[529]? = some (⟨185,(11),[1,2,5,6,13,14],[170],681⟩) from rfl))
private theorem rec8835 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(12),[1,2,5,6,13,14],[170],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[536]? = some (⟨185,(12),[1,2,5,6,13,14],[170],678⟩) from rfl))
private theorem rec8842 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(13),[1,2,5,6,13,14],[170],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[543]? = some (⟨185,(13),[1,2,5,6,13,14],[170],679⟩) from rfl))
private theorem rec8849 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(14),[1,2,5,6,13,14],[170],683⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[550]? = some (⟨185,(14),[1,2,5,6,13,14],[170],683⟩) from rfl))
private theorem rec8856 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(15),[1,2,5,6,13,14],[170],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[557]? = some (⟨185,(15),[1,2,5,6,13,14],[170],681⟩) from rfl))
private theorem rec8863 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(0),[1,2,5,6,13,14],[170],684⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[564]? = some (⟨188,(0),[1,2,5,6,13,14],[170],684⟩) from rfl))
private theorem rec8871 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(1),[1,2,5,6,13,14],[170],685⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[572]? = some (⟨188,(1),[1,2,5,6,13,14],[170],685⟩) from rfl))
private theorem rec8879 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(2),[1,2,5,6,13,14],[170],684⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[580]? = some (⟨188,(2),[1,2,5,6,13,14],[170],684⟩) from rfl))
private theorem rec8887 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(3),[1,2,5,6,13,14],[170],686⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[588]? = some (⟨188,(3),[1,2,5,6,13,14],[170],686⟩) from rfl))
private theorem rec8895 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(4),[1,2,5,6,13,14],[170],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[596]? = some (⟨188,(4),[1,2,5,6,13,14],[170],687⟩) from rfl))
private theorem rec8903 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(5),[1,2,5,6,13,14],[170],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[604]? = some (⟨188,(5),[1,2,5,6,13,14],[170],687⟩) from rfl))
private theorem rec8911 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(6),[1,2,5,6,13,14],[170],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[612]? = some (⟨188,(6),[1,2,5,6,13,14],[170],687⟩) from rfl))
private theorem rec8919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(7),[1,2,5,6,13,14],[170],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[620]? = some (⟨188,(7),[1,2,5,6,13,14],[170],687⟩) from rfl))
private theorem rec8927 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(8),[1,2,5,6,13,14],[170],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[628]? = some (⟨188,(8),[1,2,5,6,13,14],[170],688⟩) from rfl))
private theorem rec8935 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(9),[1,2,5,6,13,14],[170],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[636]? = some (⟨188,(9),[1,2,5,6,13,14],[170],688⟩) from rfl))
private theorem rec8943 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(10),[1,2,5,6,13,14],[170],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[644]? = some (⟨188,(10),[1,2,5,6,13,14],[170],688⟩) from rfl))
private theorem rec8951 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(11),[1,2,5,6,13,14],[170],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[652]? = some (⟨188,(11),[1,2,5,6,13,14],[170],688⟩) from rfl))
private theorem rec8959 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(12),[1,2,5,6,13,14],[170],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[660]? = some (⟨188,(12),[1,2,5,6,13,14],[170],689⟩) from rfl))
private theorem rec8967 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(13),[1,2,5,6,13,14],[170],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[668]? = some (⟨188,(13),[1,2,5,6,13,14],[170],689⟩) from rfl))
private theorem rec8975 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(14),[1,2,5,6,13,14],[170],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[676]? = some (⟨188,(14),[1,2,5,6,13,14],[170],689⟩) from rfl))
private theorem rec8983 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(15),[1,2,5,6,13,14],[170],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[684]? = some (⟨188,(15),[1,2,5,6,13,14],[170],689⟩) from rfl))
private theorem rec8991 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(0),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[692]? = some (⟨190,(0),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec8998 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(1),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[699]? = some (⟨190,(1),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec9005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(2),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[706]? = some (⟨190,(2),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec9012 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(3),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[713]? = some (⟨190,(3),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec9019 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(4),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[720]? = some (⟨190,(4),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec9026 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(5),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[727]? = some (⟨190,(5),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9033 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(6),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[734]? = some (⟨190,(6),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9040 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(7),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[741]? = some (⟨190,(7),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9047 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(8),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[748]? = some (⟨190,(8),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9054 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(9),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[755]? = some (⟨190,(9),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9061 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(10),[1,2,5,6,13,14],[170],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[762]? = some (⟨190,(10),[1,2,5,6,13,14],[170],692⟩) from rfl))
private theorem rec9068 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(11),[1,2,5,6,13,14],[170],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[769]? = some (⟨190,(11),[1,2,5,6,13,14],[170],693⟩) from rfl))
private theorem rec9075 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(12),[1,2,5,6,13,14],[170],694⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[776]? = some (⟨190,(12),[1,2,5,6,13,14],[170],694⟩) from rfl))
private theorem rec9082 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(13),[1,2,5,6,13,14],[170],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[783]? = some (⟨190,(13),[1,2,5,6,13,14],[170],693⟩) from rfl))
private theorem rec9089 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(14),[1,2,5,6,13,14],[170],695⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[790]? = some (⟨190,(14),[1,2,5,6,13,14],[170],695⟩) from rfl))
private theorem rec9096 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(15),[1,2,5,6,13,14],[170],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[797]? = some (⟨190,(15),[1,2,5,6,13,14],[170],692⟩) from rfl))
private theorem rec9103 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(16),[1,2,5,6,13,14],[170],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[804]? = some (⟨190,(16),[1,2,5,6,13,14],[170],696⟩) from rfl))
private theorem rec9110 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(17),[1,2,5,6,13,14],[170],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[811]? = some (⟨190,(17),[1,2,5,6,13,14],[170],696⟩) from rfl))
private theorem rec9117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(18),[1,2,5,6,13,14],[170],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[818]? = some (⟨190,(18),[1,2,5,6,13,14],[170],696⟩) from rfl))
private theorem rec9124 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(19),[1,2,5,6,13,14],[170],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[825]? = some (⟨190,(19),[1,2,5,6,13,14],[170],696⟩) from rfl))
private theorem rec9131 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(20),[1,2,5,6,13,14],[170],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[832]? = some (⟨190,(20),[1,2,5,6,13,14],[170],692⟩) from rfl))
private theorem rec9138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(21),[1,2,5,6,13,14],[170],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[839]? = some (⟨190,(21),[1,2,5,6,13,14],[170],693⟩) from rfl))
private theorem rec9145 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(22),[1,2,5,6,13,14],[170],694⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[846]? = some (⟨190,(22),[1,2,5,6,13,14],[170],694⟩) from rfl))
private theorem rec9152 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(23),[1,2,5,6,13,14],[170],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[853]? = some (⟨190,(23),[1,2,5,6,13,14],[170],693⟩) from rfl))
private theorem rec9159 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(24),[1,2,5,6,13,14],[170],695⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[860]? = some (⟨190,(24),[1,2,5,6,13,14],[170],695⟩) from rfl))
private theorem rec9166 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(0),[1,2,5,6,13,14],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[867]? = some (⟨192,(0),[1,2,5,6,13,14],[170],441⟩) from rfl))
private theorem rec9174 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(1),[1,2,5,6,13,14],[170],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[875]? = some (⟨192,(1),[1,2,5,6,13,14],[170],442⟩) from rfl))
private theorem rec9182 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(2),[1,2,5,6,13,14],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[883]? = some (⟨192,(2),[1,2,5,6,13,14],[170],441⟩) from rfl))
private theorem rec9190 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(3),[1,2,5,6,13,14],[170],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[891]? = some (⟨192,(3),[1,2,5,6,13,14],[170],443⟩) from rfl))
private theorem rec9198 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(4),[1,2,5,6,13,14],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[899]? = some (⟨192,(4),[1,2,5,6,13,14],[170],444⟩) from rfl))
private theorem rec9206 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(5),[1,2,5,6,13,14],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[907]? = some (⟨192,(5),[1,2,5,6,13,14],[170],441⟩) from rfl))
private theorem rec9214 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(6),[1,2,5,6,13,14],[170],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[915]? = some (⟨192,(6),[1,2,5,6,13,14],[170],442⟩) from rfl))
private theorem rec9222 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(7),[1,2,5,6,13,14],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[923]? = some (⟨192,(7),[1,2,5,6,13,14],[170],441⟩) from rfl))
private theorem rec9230 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(8),[1,2,5,6,13,14],[170],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[931]? = some (⟨192,(8),[1,2,5,6,13,14],[170],443⟩) from rfl))
private theorem rec9238 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(9),[1,2,5,6,13,14],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[939]? = some (⟨192,(9),[1,2,5,6,13,14],[170],444⟩) from rfl))
private theorem rec9246 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(10),[1,2,5,6,13,14],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[947]? = some (⟨192,(10),[1,2,5,6,13,14],[170],445⟩) from rfl))
private theorem rec9254 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(11),[1,2,5,6,13,14],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[955]? = some (⟨192,(11),[1,2,5,6,13,14],[170],445⟩) from rfl))
private theorem rec9262 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(12),[1,2,5,6,13,14],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[963]? = some (⟨192,(12),[1,2,5,6,13,14],[170],445⟩) from rfl))
private theorem rec9270 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(13),[1,2,5,6,13,14],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[971]? = some (⟨192,(13),[1,2,5,6,13,14],[170],445⟩) from rfl))
private theorem rec9278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(14),[1,2,5,6,13,14],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[979]? = some (⟨192,(14),[1,2,5,6,13,14],[170],444⟩) from rfl))
private theorem rec9286 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(15),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[987]? = some (⟨192,(15),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9294 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(16),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[995]? = some (⟨192,(16),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9302 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(17),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1003]? = some (⟨192,(17),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9310 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(18),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1011]? = some (⟨192,(18),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9318 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(19),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1019]? = some (⟨192,(19),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(20),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1027]? = some (⟨192,(20),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(21),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1035]? = some (⟨192,(21),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9342 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(22),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1043]? = some (⟨192,(22),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9350 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(23),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1051]? = some (⟨192,(23),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9358 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(24),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1059]? = some (⟨192,(24),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9366 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(0),[1,2,5,6,13,14],[170],697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1067]? = some (⟨195,(0),[1,2,5,6,13,14],[170],697⟩) from rfl))
private theorem rec9373 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(1),[1,2,5,6,13,14],[170],697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1074]? = some (⟨195,(1),[1,2,5,6,13,14],[170],697⟩) from rfl))
private theorem rec9380 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(2),[1,2,5,6,13,14],[170],698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1081]? = some (⟨195,(2),[1,2,5,6,13,14],[170],698⟩) from rfl))
private theorem rec9387 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(3),[1,2,5,6,13,14],[170],698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1088]? = some (⟨195,(3),[1,2,5,6,13,14],[170],698⟩) from rfl))
private theorem rec9394 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(4),[1,2,5,6,13,14],[170],699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1095]? = some (⟨195,(4),[1,2,5,6,13,14],[170],699⟩) from rfl))
private theorem rec9401 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(5),[1,2,5,6,13,14],[170],700⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1102]? = some (⟨195,(5),[1,2,5,6,13,14],[170],700⟩) from rfl))
private theorem rec9408 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(6),[1,2,5,6,13,14],[170],699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1109]? = some (⟨195,(6),[1,2,5,6,13,14],[170],699⟩) from rfl))
private theorem rec9415 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(7),[1,2,5,6,13,14],[170],701⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1116]? = some (⟨195,(7),[1,2,5,6,13,14],[170],701⟩) from rfl))
private theorem rec9422 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(8),[1,2,5,6,13,14],[170],702⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1123]? = some (⟨195,(8),[1,2,5,6,13,14],[170],702⟩) from rfl))
private theorem rec9429 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(9),[1,2,5,6,13,14],[170],703⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1130]? = some (⟨195,(9),[1,2,5,6,13,14],[170],703⟩) from rfl))
private theorem rec9436 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(0),[1,2,5,6,13,14],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1137]? = some (⟨197,(0),[1,2,5,6,13,14],[170],453⟩) from rfl))
private theorem rec9444 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(1),[1,2,5,6,13,14],[170],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1145]? = some (⟨197,(1),[1,2,5,6,13,14],[170],454⟩) from rfl))
private theorem rec9452 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(2),[1,2,5,6,13,14],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1153]? = some (⟨197,(2),[1,2,5,6,13,14],[170],453⟩) from rfl))
private theorem rec9460 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(3),[1,2,5,6,13,14],[170],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1161]? = some (⟨197,(3),[1,2,5,6,13,14],[170],455⟩) from rfl))
private theorem rec9468 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(4),[1,2,5,6,13,14],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1169]? = some (⟨197,(4),[1,2,5,6,13,14],[170],456⟩) from rfl))
private theorem rec9476 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(5),[1,2,5,6,13,14],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1177]? = some (⟨197,(5),[1,2,5,6,13,14],[170],453⟩) from rfl))
private theorem rec9484 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(6),[1,2,5,6,13,14],[170],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1185]? = some (⟨197,(6),[1,2,5,6,13,14],[170],454⟩) from rfl))
private theorem rec9492 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(7),[1,2,5,6,13,14],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1193]? = some (⟨197,(7),[1,2,5,6,13,14],[170],453⟩) from rfl))
private theorem rec9500 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(8),[1,2,5,6,13,14],[170],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1201]? = some (⟨197,(8),[1,2,5,6,13,14],[170],455⟩) from rfl))
private theorem rec9508 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(9),[1,2,5,6,13,14],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1209]? = some (⟨197,(9),[1,2,5,6,13,14],[170],456⟩) from rfl))
private theorem rec9516 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(10),[1,2,5,6,13,14],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1217]? = some (⟨197,(10),[1,2,5,6,13,14],[170],457⟩) from rfl))
private theorem rec9524 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(11),[1,2,5,6,13,14],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[6]? = some (⟨197,(11),[1,2,5,6,13,14],[170],457⟩) from rfl))
private theorem rec9532 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(12),[1,2,5,6,13,14],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[14]? = some (⟨197,(12),[1,2,5,6,13,14],[170],457⟩) from rfl))
private theorem rec9540 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(13),[1,2,5,6,13,14],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[22]? = some (⟨197,(13),[1,2,5,6,13,14],[170],457⟩) from rfl))
private theorem rec9548 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(14),[1,2,5,6,13,14],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[30]? = some (⟨197,(14),[1,2,5,6,13,14],[170],456⟩) from rfl))
private theorem rec9556 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(15),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[38]? = some (⟨197,(15),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9564 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(16),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[46]? = some (⟨197,(16),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9572 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(17),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[54]? = some (⟨197,(17),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9580 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(18),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[62]? = some (⟨197,(18),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9588 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(19),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[70]? = some (⟨197,(19),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(20),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[78]? = some (⟨197,(20),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9604 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(21),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[86]? = some (⟨197,(21),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9612 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(22),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[94]? = some (⟨197,(22),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9620 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(23),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[102]? = some (⟨197,(23),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9628 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(24),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[110]? = some (⟨197,(24),[1,2,5,6,13,14],[170],459⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 23).take 23, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 1 170 gs.1 j := by
  have hp : ((section14State section14Catalog 1).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 23).take 23) = [(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      exact rec8383 1 170 (by decide) (by decide)
    · right
      exact rec8391 1 170 (by decide) (by decide)
    · right
      exact rec8399 1 170 (by decide) (by decide)
    · right
      exact rec8407 1 170 (by decide) (by decide)
    · right
      exact rec8415 1 170 (by decide) (by decide)
    · right
      exact rec8423 1 170 (by decide) (by decide)
    · right
      exact rec8431 1 170 (by decide) (by decide)
    · right
      exact rec8439 1 170 (by decide) (by decide)
    · right
      exact rec8447 1 170 (by decide) (by decide)
    · right
      exact rec8455 1 170 (by decide) (by decide)
    · right
      exact rec8463 1 170 (by decide) (by decide)
    · right
      exact rec8471 1 170 (by decide) (by decide)
    · right
      exact rec8479 1 170 (by decide) (by decide)
    · right
      exact rec8487 1 170 (by decide) (by decide)
    · right
      exact rec8495 1 170 (by decide) (by decide)
    · right
      exact rec8503 1 170 (by decide) (by decide)
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
      exact rec8511 1 170 (by decide) (by decide)
    · right
      exact rec8518 1 170 (by decide) (by decide)
    · right
      exact rec8525 1 170 (by decide) (by decide)
    · right
      exact rec8532 1 170 (by decide) (by decide)
    · right
      exact rec8539 1 170 (by decide) (by decide)
    · right
      exact rec8546 1 170 (by decide) (by decide)
    · right
      exact rec8553 1 170 (by decide) (by decide)
    · right
      exact rec8560 1 170 (by decide) (by decide)
    · right
      exact rec8567 1 170 (by decide) (by decide)
    · right
      exact rec8574 1 170 (by decide) (by decide)
    · right
      exact rec8581 1 170 (by decide) (by decide)
    · right
      exact rec8588 1 170 (by decide) (by decide)
    · right
      exact rec8595 1 170 (by decide) (by decide)
    · right
      exact rec8602 1 170 (by decide) (by decide)
    · right
      exact rec8609 1 170 (by decide) (by decide)
    · right
      exact rec8616 1 170 (by decide) (by decide)
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
      exact rec8623 1 170 (by decide) (by decide)
    · right
      exact rec8631 1 170 (by decide) (by decide)
    · right
      exact rec8639 1 170 (by decide) (by decide)
    · right
      exact rec8647 1 170 (by decide) (by decide)
    · right
      exact rec8655 1 170 (by decide) (by decide)
    · right
      exact rec8663 1 170 (by decide) (by decide)
    · right
      exact rec8671 1 170 (by decide) (by decide)
    · right
      exact rec8679 1 170 (by decide) (by decide)
    · right
      exact rec8687 1 170 (by decide) (by decide)
    · right
      exact rec8695 1 170 (by decide) (by decide)
    · right
      exact rec8703 1 170 (by decide) (by decide)
    · right
      exact rec8711 1 170 (by decide) (by decide)
    · right
      exact rec8719 1 170 (by decide) (by decide)
    · right
      exact rec8727 1 170 (by decide) (by decide)
    · right
      exact rec8735 1 170 (by decide) (by decide)
    · right
      exact rec8743 1 170 (by decide) (by decide)
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
      exact rec8751 1 170 (by decide) (by decide)
    · right
      exact rec8758 1 170 (by decide) (by decide)
    · right
      exact rec8765 1 170 (by decide) (by decide)
    · right
      exact rec8772 1 170 (by decide) (by decide)
    · right
      exact rec8779 1 170 (by decide) (by decide)
    · right
      exact rec8786 1 170 (by decide) (by decide)
    · right
      exact rec8793 1 170 (by decide) (by decide)
    · right
      exact rec8800 1 170 (by decide) (by decide)
    · right
      exact rec8807 1 170 (by decide) (by decide)
    · right
      exact rec8814 1 170 (by decide) (by decide)
    · right
      exact rec8821 1 170 (by decide) (by decide)
    · right
      exact rec8828 1 170 (by decide) (by decide)
    · right
      exact rec8835 1 170 (by decide) (by decide)
    · right
      exact rec8842 1 170 (by decide) (by decide)
    · right
      exact rec8849 1 170 (by decide) (by decide)
    · right
      exact rec8856 1 170 (by decide) (by decide)
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
      exact rec8863 1 170 (by decide) (by decide)
    · right
      exact rec8871 1 170 (by decide) (by decide)
    · right
      exact rec8879 1 170 (by decide) (by decide)
    · right
      exact rec8887 1 170 (by decide) (by decide)
    · right
      exact rec8895 1 170 (by decide) (by decide)
    · right
      exact rec8903 1 170 (by decide) (by decide)
    · right
      exact rec8911 1 170 (by decide) (by decide)
    · right
      exact rec8919 1 170 (by decide) (by decide)
    · right
      exact rec8927 1 170 (by decide) (by decide)
    · right
      exact rec8935 1 170 (by decide) (by decide)
    · right
      exact rec8943 1 170 (by decide) (by decide)
    · right
      exact rec8951 1 170 (by decide) (by decide)
    · right
      exact rec8959 1 170 (by decide) (by decide)
    · right
      exact rec8967 1 170 (by decide) (by decide)
    · right
      exact rec8975 1 170 (by decide) (by decide)
    · right
      exact rec8983 1 170 (by decide) (by decide)
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
      exact rec8991 1 170 (by decide) (by decide)
    · right
      exact rec8998 1 170 (by decide) (by decide)
    · right
      exact rec9005 1 170 (by decide) (by decide)
    · right
      exact rec9012 1 170 (by decide) (by decide)
    · right
      exact rec9019 1 170 (by decide) (by decide)
    · right
      exact rec9026 1 170 (by decide) (by decide)
    · right
      exact rec9033 1 170 (by decide) (by decide)
    · right
      exact rec9040 1 170 (by decide) (by decide)
    · right
      exact rec9047 1 170 (by decide) (by decide)
    · right
      exact rec9054 1 170 (by decide) (by decide)
    · right
      exact rec9061 1 170 (by decide) (by decide)
    · right
      exact rec9068 1 170 (by decide) (by decide)
    · right
      exact rec9075 1 170 (by decide) (by decide)
    · right
      exact rec9082 1 170 (by decide) (by decide)
    · right
      exact rec9089 1 170 (by decide) (by decide)
    · right
      exact rec9096 1 170 (by decide) (by decide)
    · right
      exact rec9103 1 170 (by decide) (by decide)
    · right
      exact rec9110 1 170 (by decide) (by decide)
    · right
      exact rec9117 1 170 (by decide) (by decide)
    · right
      exact rec9124 1 170 (by decide) (by decide)
    · right
      exact rec9131 1 170 (by decide) (by decide)
    · right
      exact rec9138 1 170 (by decide) (by decide)
    · right
      exact rec9145 1 170 (by decide) (by decide)
    · right
      exact rec9152 1 170 (by decide) (by decide)
    · right
      exact rec9159 1 170 (by decide) (by decide)
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
      exact rec9166 1 170 (by decide) (by decide)
    · right
      exact rec9174 1 170 (by decide) (by decide)
    · right
      exact rec9182 1 170 (by decide) (by decide)
    · right
      exact rec9190 1 170 (by decide) (by decide)
    · right
      exact rec9198 1 170 (by decide) (by decide)
    · right
      exact rec9206 1 170 (by decide) (by decide)
    · right
      exact rec9214 1 170 (by decide) (by decide)
    · right
      exact rec9222 1 170 (by decide) (by decide)
    · right
      exact rec9230 1 170 (by decide) (by decide)
    · right
      exact rec9238 1 170 (by decide) (by decide)
    · right
      exact rec9246 1 170 (by decide) (by decide)
    · right
      exact rec9254 1 170 (by decide) (by decide)
    · right
      exact rec9262 1 170 (by decide) (by decide)
    · right
      exact rec9270 1 170 (by decide) (by decide)
    · right
      exact rec9278 1 170 (by decide) (by decide)
    · right
      exact rec9286 1 170 (by decide) (by decide)
    · right
      exact rec9294 1 170 (by decide) (by decide)
    · right
      exact rec9302 1 170 (by decide) (by decide)
    · right
      exact rec9310 1 170 (by decide) (by decide)
    · right
      exact rec9318 1 170 (by decide) (by decide)
    · right
      exact rec9326 1 170 (by decide) (by decide)
    · right
      exact rec9334 1 170 (by decide) (by decide)
    · right
      exact rec9342 1 170 (by decide) (by decide)
    · right
      exact rec9350 1 170 (by decide) (by decide)
    · right
      exact rec9358 1 170 (by decide) (by decide)
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
      exact rec9366 1 170 (by decide) (by decide)
    · right
      exact rec9373 1 170 (by decide) (by decide)
    · right
      exact rec9380 1 170 (by decide) (by decide)
    · right
      exact rec9387 1 170 (by decide) (by decide)
    · right
      exact rec9394 1 170 (by decide) (by decide)
    · right
      exact rec9401 1 170 (by decide) (by decide)
    · right
      exact rec9408 1 170 (by decide) (by decide)
    · right
      exact rec9415 1 170 (by decide) (by decide)
    · right
      exact rec9422 1 170 (by decide) (by decide)
    · right
      exact rec9429 1 170 (by decide) (by decide)
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
      exact rec9436 1 170 (by decide) (by decide)
    · right
      exact rec9444 1 170 (by decide) (by decide)
    · right
      exact rec9452 1 170 (by decide) (by decide)
    · right
      exact rec9460 1 170 (by decide) (by decide)
    · right
      exact rec9468 1 170 (by decide) (by decide)
    · right
      exact rec9476 1 170 (by decide) (by decide)
    · right
      exact rec9484 1 170 (by decide) (by decide)
    · right
      exact rec9492 1 170 (by decide) (by decide)
    · right
      exact rec9500 1 170 (by decide) (by decide)
    · right
      exact rec9508 1 170 (by decide) (by decide)
    · right
      exact rec9516 1 170 (by decide) (by decide)
    · right
      exact rec9524 1 170 (by decide) (by decide)
    · right
      exact rec9532 1 170 (by decide) (by decide)
    · right
      exact rec9540 1 170 (by decide) (by decide)
    · right
      exact rec9548 1 170 (by decide) (by decide)
    · right
      exact rec9556 1 170 (by decide) (by decide)
    · right
      exact rec9564 1 170 (by decide) (by decide)
    · right
      exact rec9572 1 170 (by decide) (by decide)
    · right
      exact rec9580 1 170 (by decide) (by decide)
    · right
      exact rec9588 1 170 (by decide) (by decide)
    · right
      exact rec9596 1 170 (by decide) (by decide)
    · right
      exact rec9604 1 170 (by decide) (by decide)
    · right
      exact rec9612 1 170 (by decide) (by decide)
    · right
      exact rec9620 1 170 (by decide) (by decide)
    · right
      exact rec9628 1 170 (by decide) (by decide)
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
end Section14CoverageSpec_1_5_p170_23_46

#print axioms solution
