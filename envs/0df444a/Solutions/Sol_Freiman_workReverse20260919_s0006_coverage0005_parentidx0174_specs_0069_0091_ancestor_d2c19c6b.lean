-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_coverage0005_parentidx0174_specs_0069_0091_ancestor_d2c19c6b
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T04:39:48.571985+00:00
-- url     : https://prove2.me/submissions/527dae97-d99c-44f8-ad41-263c8d9170fb

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
namespace Section14CoverageSpec_6_5_p174_69_91
private theorem rec11141 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(0),[5,6],[174],1044⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[412]? = some (⟨224,(0),[5,6],[174],1044⟩) from rfl))
private theorem rec11147 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(1),[5,6],[174],1044⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[418]? = some (⟨224,(1),[5,6],[174],1044⟩) from rfl))
private theorem rec11153 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(2),[5,6],[174],1045⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[424]? = some (⟨224,(2),[5,6],[174],1045⟩) from rfl))
private theorem rec11159 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(3),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[430]? = some (⟨224,(3),[5,6],[174],1038⟩) from rfl))
private theorem rec11165 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(4),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[436]? = some (⟨224,(4),[5,6],[174],1039⟩) from rfl))
private theorem rec11172 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(5),[5,6],[174],1046⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[443]? = some (⟨224,(5),[5,6],[174],1046⟩) from rfl))
private theorem rec11180 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(6),[5,6],[174],1046⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[451]? = some (⟨224,(6),[5,6],[174],1046⟩) from rfl))
private theorem rec11188 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(7),[5,6],[174],1045⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[459]? = some (⟨224,(7),[5,6],[174],1045⟩) from rfl))
private theorem rec11196 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(8),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[467]? = some (⟨224,(8),[5,6],[174],1038⟩) from rfl))
private theorem rec11204 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(9),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[475]? = some (⟨224,(9),[5,6],[174],1039⟩) from rfl))
private theorem rec11212 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(10),[5,6],[174],1044⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[483]? = some (⟨224,(10),[5,6],[174],1044⟩) from rfl))
private theorem rec11220 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(11),[5,6],[174],1044⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[491]? = some (⟨224,(11),[5,6],[174],1044⟩) from rfl))
private theorem rec11228 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(12),[5,6],[174],1045⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[499]? = some (⟨224,(12),[5,6],[174],1045⟩) from rfl))
private theorem rec11236 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(13),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[507]? = some (⟨224,(13),[5,6],[174],1038⟩) from rfl))
private theorem rec11244 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(14),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[515]? = some (⟨224,(14),[5,6],[174],1039⟩) from rfl))
private theorem rec11252 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(15),[5,6],[174],1047⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[523]? = some (⟨224,(15),[5,6],[174],1047⟩) from rfl))
private theorem rec11260 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(16),[5,6],[174],1047⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[531]? = some (⟨224,(16),[5,6],[174],1047⟩) from rfl))
private theorem rec11268 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(17),[5,6],[174],1045⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[539]? = some (⟨224,(17),[5,6],[174],1045⟩) from rfl))
private theorem rec11276 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(18),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[547]? = some (⟨224,(18),[5,6],[174],1038⟩) from rfl))
private theorem rec11284 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(19),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[555]? = some (⟨224,(19),[5,6],[174],1039⟩) from rfl))
private theorem rec11292 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(20),[5,6],[174],1048⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[563]? = some (⟨224,(20),[5,6],[174],1048⟩) from rfl))
private theorem rec11300 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(21),[5,6],[174],1048⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[571]? = some (⟨224,(21),[5,6],[174],1048⟩) from rfl))
private theorem rec11308 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(22),[5,6],[174],1048⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[579]? = some (⟨224,(22),[5,6],[174],1048⟩) from rfl))
private theorem rec11316 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(23),[5,6],[174],1038⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[587]? = some (⟨224,(23),[5,6],[174],1038⟩) from rfl))
private theorem rec11324 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 224 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(24),[5,6],[174],1039⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[595]? = some (⟨224,(24),[5,6],[174],1039⟩) from rfl))
private theorem rec11331 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(0),[5,6],[174],747⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[602]? = some (⟨225,(0),[5,6],[174],747⟩) from rfl))
private theorem rec11337 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(1),[5,6],[174],748⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[608]? = some (⟨225,(1),[5,6],[174],748⟩) from rfl))
private theorem rec11343 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(2),[5,6],[174],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[614]? = some (⟨225,(2),[5,6],[174],749⟩) from rfl))
private theorem rec11350 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(3),[5,6],[174],750⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[621]? = some (⟨225,(3),[5,6],[174],750⟩) from rfl))
private theorem rec11357 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(4),[5,6],[174],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[628]? = some (⟨225,(4),[5,6],[174],749⟩) from rfl))
private theorem rec11364 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(5),[5,6],[174],751⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[635]? = some (⟨225,(5),[5,6],[174],751⟩) from rfl))
private theorem rec11370 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(6),[5,6],[174],752⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[641]? = some (⟨225,(6),[5,6],[174],752⟩) from rfl))
private theorem rec11377 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(7),[5,6],[174],1051⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[648]? = some (⟨225,(7),[5,6],[174],1051⟩) from rfl))
private theorem rec11384 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(8),[5,6],[174],754⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[655]? = some (⟨225,(8),[5,6],[174],754⟩) from rfl))
private theorem rec11392 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(9),[5,6],[174],1051⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[663]? = some (⟨225,(9),[5,6],[174],1051⟩) from rfl))
private theorem rec11399 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(10),[5,6],[174],755⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[670]? = some (⟨225,(10),[5,6],[174],755⟩) from rfl))
private theorem rec11405 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(11),[5,6],[174],756⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[676]? = some (⟨225,(11),[5,6],[174],756⟩) from rfl))
private theorem rec11412 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(12),[5,6],[174],1053⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[683]? = some (⟨225,(12),[5,6],[174],1053⟩) from rfl))
private theorem rec11419 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(13),[5,6],[174],758⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[690]? = some (⟨225,(13),[5,6],[174],758⟩) from rfl))
private theorem rec11427 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(14),[5,6],[174],1053⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[698]? = some (⟨225,(14),[5,6],[174],1053⟩) from rfl))
private theorem rec11434 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(15),[5,6],[174],759⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[705]? = some (⟨225,(15),[5,6],[174],759⟩) from rfl))
private theorem rec11440 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(16),[5,6],[174],760⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[711]? = some (⟨225,(16),[5,6],[174],760⟩) from rfl))
private theorem rec11447 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(17),[5,6],[174],1054⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[718]? = some (⟨225,(17),[5,6],[174],1054⟩) from rfl))
private theorem rec11454 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(18),[5,6],[174],762⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[725]? = some (⟨225,(18),[5,6],[174],762⟩) from rfl))
private theorem rec11462 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(19),[5,6],[174],1054⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[733]? = some (⟨225,(19),[5,6],[174],1054⟩) from rfl))
private theorem rec11469 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(20),[5,6],[174],763⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[740]? = some (⟨225,(20),[5,6],[174],763⟩) from rfl))
private theorem rec11475 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(21),[5,6],[174],764⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[746]? = some (⟨225,(21),[5,6],[174],764⟩) from rfl))
private theorem rec11482 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(22),[5,6],[174],1048⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[753]? = some (⟨225,(22),[5,6],[174],1048⟩) from rfl))
private theorem rec11489 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(23),[5,6],[174],765⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[760]? = some (⟨225,(23),[5,6],[174],765⟩) from rfl))
private theorem rec11497 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 225 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(24),[5,6],[174],1048⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[768]? = some (⟨225,(24),[5,6],[174],1048⟩) from rfl))
private theorem rec11504 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(0),[5,6],[174],766⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[775]? = some (⟨226,(0),[5,6],[174],766⟩) from rfl))
private theorem rec11511 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(1),[5,6],[174],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[782]? = some (⟨226,(1),[5,6],[174],767⟩) from rfl))
private theorem rec11517 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(2),[5,6],[174],768⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[788]? = some (⟨226,(2),[5,6],[174],768⟩) from rfl))
private theorem rec11523 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(3),[5,6],[174],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[794]? = some (⟨226,(3),[5,6],[174],767⟩) from rfl))
private theorem rec11529 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(4),[5,6],[174],769⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[800]? = some (⟨226,(4),[5,6],[174],769⟩) from rfl))
private theorem rec11535 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(5),[5,6],[174],770⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[806]? = some (⟨226,(5),[5,6],[174],770⟩) from rfl))
private theorem rec11541 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(6),[5,6],[174],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[812]? = some (⟨226,(6),[5,6],[174],771⟩) from rfl))
private theorem rec11547 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(7),[5,6],[174],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[818]? = some (⟨226,(7),[5,6],[174],771⟩) from rfl))
private theorem rec11553 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(8),[5,6],[174],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[824]? = some (⟨226,(8),[5,6],[174],772⟩) from rfl))
private theorem rec11559 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 226 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(9),[5,6],[174],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[830]? = some (⟨226,(9),[5,6],[174],772⟩) from rfl))
private theorem rec11565 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(0),[5,6],[174],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[836]? = some (⟨227,(0),[5,6],[174],773⟩) from rfl))
private theorem rec11571 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(1),[5,6],[174],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[842]? = some (⟨227,(1),[5,6],[174],774⟩) from rfl))
private theorem rec11578 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(2),[5,6],[174],1056⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[849]? = some (⟨227,(2),[5,6],[174],1056⟩) from rfl))
private theorem rec11585 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(3),[5,6],[174],1057⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[856]? = some (⟨227,(3),[5,6],[174],1057⟩) from rfl))
private theorem rec11592 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(4),[5,6],[174],1056⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[863]? = some (⟨227,(4),[5,6],[174],1056⟩) from rfl))
private theorem rec11599 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(5),[5,6],[174],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[870]? = some (⟨227,(5),[5,6],[174],773⟩) from rfl))
private theorem rec11605 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(6),[5,6],[174],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[876]? = some (⟨227,(6),[5,6],[174],774⟩) from rfl))
private theorem rec11612 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(7),[5,6],[174],1056⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[883]? = some (⟨227,(7),[5,6],[174],1056⟩) from rfl))
private theorem rec11619 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(8),[5,6],[174],1057⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[890]? = some (⟨227,(8),[5,6],[174],1057⟩) from rfl))
private theorem rec11626 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(9),[5,6],[174],1056⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[897]? = some (⟨227,(9),[5,6],[174],1056⟩) from rfl))
private theorem rec11633 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(10),[5,6],[174],777⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[904]? = some (⟨227,(10),[5,6],[174],777⟩) from rfl))
private theorem rec11639 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(11),[5,6],[174],778⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[910]? = some (⟨227,(11),[5,6],[174],778⟩) from rfl))
private theorem rec11646 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(12),[5,6],[174],1058⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[917]? = some (⟨227,(12),[5,6],[174],1058⟩) from rfl))
private theorem rec11653 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(13),[5,6],[174],1059⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[924]? = some (⟨227,(13),[5,6],[174],1059⟩) from rfl))
private theorem rec11660 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(14),[5,6],[174],1058⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[931]? = some (⟨227,(14),[5,6],[174],1058⟩) from rfl))
private theorem rec11667 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(15),[5,6],[174],781⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[938]? = some (⟨227,(15),[5,6],[174],781⟩) from rfl))
private theorem rec11673 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(16),[5,6],[174],782⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[944]? = some (⟨227,(16),[5,6],[174],782⟩) from rfl))
private theorem rec11680 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(17),[5,6],[174],1060⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[951]? = some (⟨227,(17),[5,6],[174],1060⟩) from rfl))
private theorem rec11687 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(18),[5,6],[174],1060⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[958]? = some (⟨227,(18),[5,6],[174],1060⟩) from rfl))
private theorem rec11694 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(19),[5,6],[174],1060⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[965]? = some (⟨227,(19),[5,6],[174],1060⟩) from rfl))
private theorem rec11701 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(20),[5,6],[174],785⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[972]? = some (⟨227,(20),[5,6],[174],785⟩) from rfl))
private theorem rec11707 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(21),[5,6],[174],786⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[978]? = some (⟨227,(21),[5,6],[174],786⟩) from rfl))
private theorem rec11714 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(22),[5,6],[174],1061⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[985]? = some (⟨227,(22),[5,6],[174],1061⟩) from rfl))
private theorem rec11721 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(23),[5,6],[174],1062⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[992]? = some (⟨227,(23),[5,6],[174],1062⟩) from rfl))
private theorem rec11728 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 227 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(24),[5,6],[174],1061⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[999]? = some (⟨227,(24),[5,6],[174],1061⟩) from rfl))
private theorem rec11735 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(0),[5,6],[174],789⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1006]? = some (⟨228,(0),[5,6],[174],789⟩) from rfl))
private theorem rec11742 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(1),[5,6],[174],790⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1013]? = some (⟨228,(1),[5,6],[174],790⟩) from rfl))
private theorem rec11751 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(2),[5,6],[174],791⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1022]? = some (⟨228,(2),[5,6],[174],791⟩) from rfl))
private theorem rec11759 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(3),[5,6],[174],792⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1030]? = some (⟨228,(3),[5,6],[174],792⟩) from rfl))
private theorem rec11766 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(4),[5,6],[174],793⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1037]? = some (⟨228,(4),[5,6],[174],793⟩) from rfl))
private theorem rec11772 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(5),[5,6],[174],794⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1043]? = some (⟨228,(5),[5,6],[174],794⟩) from rfl))
private theorem rec11778 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(6),[5,6],[174],795⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1049]? = some (⟨228,(6),[5,6],[174],795⟩) from rfl))
private theorem rec11784 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(7),[5,6],[174],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1055]? = some (⟨228,(7),[5,6],[174],796⟩) from rfl))
private theorem rec11790 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(8),[5,6],[174],797⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1061]? = some (⟨228,(8),[5,6],[174],797⟩) from rfl))
private theorem rec11796 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(9),[5,6],[174],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1067]? = some (⟨228,(9),[5,6],[174],796⟩) from rfl))
private theorem rec11803 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(10),[5,6],[174],798⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1074]? = some (⟨228,(10),[5,6],[174],798⟩) from rfl))
private theorem rec11809 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(11),[5,6],[174],799⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1080]? = some (⟨228,(11),[5,6],[174],799⟩) from rfl))
private theorem rec11815 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(12),[5,6],[174],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1086]? = some (⟨228,(12),[5,6],[174],800⟩) from rfl))
private theorem rec11821 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(13),[5,6],[174],801⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1092]? = some (⟨228,(13),[5,6],[174],801⟩) from rfl))
private theorem rec11827 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(14),[5,6],[174],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1098]? = some (⟨228,(14),[5,6],[174],800⟩) from rfl))
private theorem rec11833 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(15),[5,6],[174],802⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1104]? = some (⟨228,(15),[5,6],[174],802⟩) from rfl))
private theorem rec11839 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(16),[5,6],[174],803⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1110]? = some (⟨228,(16),[5,6],[174],803⟩) from rfl))
private theorem rec11845 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(17),[5,6],[174],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1116]? = some (⟨228,(17),[5,6],[174],804⟩) from rfl))
private theorem rec11851 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(18),[5,6],[174],805⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1122]? = some (⟨228,(18),[5,6],[174],805⟩) from rfl))
private theorem rec11857 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(19),[5,6],[174],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1128]? = some (⟨228,(19),[5,6],[174],804⟩) from rfl))
private theorem rec11863 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(20),[5,6],[174],806⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1134]? = some (⟨228,(20),[5,6],[174],806⟩) from rfl))
private theorem rec11869 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(21),[5,6],[174],807⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1140]? = some (⟨228,(21),[5,6],[174],807⟩) from rfl))
private theorem rec11875 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(22),[5,6],[174],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1146]? = some (⟨228,(22),[5,6],[174],808⟩) from rfl))
private theorem rec11881 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(23),[5,6],[174],809⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1152]? = some (⟨228,(23),[5,6],[174],809⟩) from rfl))
private theorem rec11887 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 228 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(24),[5,6],[174],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1158]? = some (⟨228,(24),[5,6],[174],808⟩) from rfl))
private theorem rec11893 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(0),[5,6],[174],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1164]? = some (⟨230,(0),[5,6],[174],810⟩) from rfl))
private theorem rec11899 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(1),[5,6],[174],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1170]? = some (⟨230,(1),[5,6],[174],811⟩) from rfl))
private theorem rec11906 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(2),[5,6],[174],812⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1177]? = some (⟨230,(2),[5,6],[174],812⟩) from rfl))
private theorem rec11912 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(3),[5,6],[174],813⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1183]? = some (⟨230,(3),[5,6],[174],813⟩) from rfl))
private theorem rec11918 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(4),[5,6],[174],814⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1189]? = some (⟨230,(4),[5,6],[174],814⟩) from rfl))
private theorem rec11924 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(5),[5,6],[174],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1195]? = some (⟨230,(5),[5,6],[174],810⟩) from rfl))
private theorem rec11930 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(6),[5,6],[174],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[1]? = some (⟨230,(6),[5,6],[174],811⟩) from rfl))
private theorem rec11939 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(7),[5,6],[174],1063⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[10]? = some (⟨230,(7),[5,6],[174],1063⟩) from rfl))
private theorem rec11945 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(8),[5,6],[174],816⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[16]? = some (⟨230,(8),[5,6],[174],816⟩) from rfl))
private theorem rec11954 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(9),[5,6],[174],1065⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[25]? = some (⟨230,(9),[5,6],[174],1065⟩) from rfl))
private theorem rec11961 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(10),[5,6],[174],818⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[32]? = some (⟨230,(10),[5,6],[174],818⟩) from rfl))
private theorem rec11967 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(11),[5,6],[174],819⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[38]? = some (⟨230,(11),[5,6],[174],819⟩) from rfl))
private theorem rec11975 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(12),[5,6],[174],1066⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[46]? = some (⟨230,(12),[5,6],[174],1066⟩) from rfl))
private theorem rec11981 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(13),[5,6],[174],1066⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[52]? = some (⟨230,(13),[5,6],[174],1066⟩) from rfl))
private theorem rec11989 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(14),[5,6],[174],1065⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[60]? = some (⟨230,(14),[5,6],[174],1065⟩) from rfl))
private theorem rec11996 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(15),[5,6],[174],822⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[67]? = some (⟨230,(15),[5,6],[174],822⟩) from rfl))
private theorem rec12002 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(16),[5,6],[174],823⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[73]? = some (⟨230,(16),[5,6],[174],823⟩) from rfl))
private theorem rec12009 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(17),[5,6],[174],1067⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[80]? = some (⟨230,(17),[5,6],[174],1067⟩) from rfl))
private theorem rec12016 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(18),[5,6],[174],1067⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[87]? = some (⟨230,(18),[5,6],[174],1067⟩) from rfl))
private theorem rec12023 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(19),[5,6],[174],1067⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[94]? = some (⟨230,(19),[5,6],[174],1067⟩) from rfl))
private theorem rec12030 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(20),[5,6],[174],826⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[101]? = some (⟨230,(20),[5,6],[174],826⟩) from rfl))
private theorem rec12036 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(21),[5,6],[174],827⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[107]? = some (⟨230,(21),[5,6],[174],827⟩) from rfl))
private theorem rec12043 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(22),[5,6],[174],1068⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[114]? = some (⟨230,(22),[5,6],[174],1068⟩) from rfl))
private theorem rec12050 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(23),[5,6],[174],1068⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[121]? = some (⟨230,(23),[5,6],[174],1068⟩) from rfl))
private theorem rec12057 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 230 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(24),[5,6],[174],1068⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[128]? = some (⟨230,(24),[5,6],[174],1068⟩) from rfl))
private theorem rec12064 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(0),[5,6],[174],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[135]? = some (⟨231,(0),[5,6],[174],830⟩) from rfl))
private theorem rec12071 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(1),[5,6],[174],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[142]? = some (⟨231,(1),[5,6],[174],831⟩) from rfl))
private theorem rec12079 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(2),[5,6],[174],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[150]? = some (⟨231,(2),[5,6],[174],832⟩) from rfl))
private theorem rec12085 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(3),[5,6],[174],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[156]? = some (⟨231,(3),[5,6],[174],833⟩) from rfl))
private theorem rec12091 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(4),[5,6],[174],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[162]? = some (⟨231,(4),[5,6],[174],830⟩) from rfl))
private theorem rec12098 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(5),[5,6],[174],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[169]? = some (⟨231,(5),[5,6],[174],831⟩) from rfl))
private theorem rec12106 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(6),[5,6],[174],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[177]? = some (⟨231,(6),[5,6],[174],832⟩) from rfl))
private theorem rec12112 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(7),[5,6],[174],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[183]? = some (⟨231,(7),[5,6],[174],833⟩) from rfl))
private theorem rec12118 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(8),[5,6],[174],834⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[189]? = some (⟨231,(8),[5,6],[174],834⟩) from rfl))
private theorem rec12124 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(9),[5,6],[174],835⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[195]? = some (⟨231,(9),[5,6],[174],835⟩) from rfl))
private theorem rec12130 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(10),[5,6],[174],836⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[201]? = some (⟨231,(10),[5,6],[174],836⟩) from rfl))
private theorem rec12136 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(11),[5,6],[174],837⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[207]? = some (⟨231,(11),[5,6],[174],837⟩) from rfl))
private theorem rec12142 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(12),[5,6],[174],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[213]? = some (⟨231,(12),[5,6],[174],838⟩) from rfl))
private theorem rec12148 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(13),[5,6],[174],839⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[219]? = some (⟨231,(13),[5,6],[174],839⟩) from rfl))
private theorem rec12154 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(14),[5,6],[174],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[225]? = some (⟨231,(14),[5,6],[174],838⟩) from rfl))
private theorem rec12160 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(15),[5,6],[174],840⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[231]? = some (⟨231,(15),[5,6],[174],840⟩) from rfl))
private theorem rec12166 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(16),[5,6],[174],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[237]? = some (⟨231,(16),[5,6],[174],841⟩) from rfl))
private theorem rec12172 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(17),[5,6],[174],842⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[243]? = some (⟨231,(17),[5,6],[174],842⟩) from rfl))
private theorem rec12178 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(18),[5,6],[174],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[249]? = some (⟨231,(18),[5,6],[174],841⟩) from rfl))
private theorem rec12184 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 231 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(19),[5,6],[174],843⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[255]? = some (⟨231,(19),[5,6],[174],843⟩) from rfl))
private theorem rec12190 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(0),[5,6],[174],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[261]? = some (⟨232,(0),[5,6],[174],844⟩) from rfl))
private theorem rec12196 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(1),[5,6],[174],845⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[267]? = some (⟨232,(1),[5,6],[174],845⟩) from rfl))
private theorem rec12202 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(2),[5,6],[174],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[273]? = some (⟨232,(2),[5,6],[174],846⟩) from rfl))
private theorem rec12209 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(3),[5,6],[174],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[280]? = some (⟨232,(3),[5,6],[174],847⟩) from rfl))
private theorem rec12217 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(4),[5,6],[174],1069⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[288]? = some (⟨232,(4),[5,6],[174],1069⟩) from rfl))
private theorem rec12223 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(5),[5,6],[174],849⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[294]? = some (⟨232,(5),[5,6],[174],849⟩) from rfl))
private theorem rec12229 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(6),[5,6],[174],850⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[300]? = some (⟨232,(6),[5,6],[174],850⟩) from rfl))
private theorem rec12235 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(7),[5,6],[174],851⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[306]? = some (⟨232,(7),[5,6],[174],851⟩) from rfl))
private theorem rec12242 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(8),[5,6],[174],852⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[313]? = some (⟨232,(8),[5,6],[174],852⟩) from rfl))
private theorem rec12249 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(9),[5,6],[174],1070⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[320]? = some (⟨232,(9),[5,6],[174],1070⟩) from rfl))
private theorem rec12256 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(10),[5,6],[174],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[327]? = some (⟨232,(10),[5,6],[174],844⟩) from rfl))
private theorem rec12262 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(11),[5,6],[174],854⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[333]? = some (⟨232,(11),[5,6],[174],854⟩) from rfl))
private theorem rec12268 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(12),[5,6],[174],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[339]? = some (⟨232,(12),[5,6],[174],846⟩) from rfl))
private theorem rec12275 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(13),[5,6],[174],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[346]? = some (⟨232,(13),[5,6],[174],847⟩) from rfl))
private theorem rec12282 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(14),[5,6],[174],1069⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[353]? = some (⟨232,(14),[5,6],[174],1069⟩) from rfl))
private theorem rec12289 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(15),[5,6],[174],856⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[360]? = some (⟨232,(15),[5,6],[174],856⟩) from rfl))
private theorem rec12295 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(16),[5,6],[174],857⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[366]? = some (⟨232,(16),[5,6],[174],857⟩) from rfl))
private theorem rec12301 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(17),[5,6],[174],858⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[372]? = some (⟨232,(17),[5,6],[174],858⟩) from rfl))
private theorem rec12308 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(18),[5,6],[174],859⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[379]? = some (⟨232,(18),[5,6],[174],859⟩) from rfl))
private theorem rec12315 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 232 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(19),[5,6],[174],1071⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[386]? = some (⟨232,(19),[5,6],[174],1071⟩) from rfl))
private theorem rec12322 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(0),[5,6],[174],1072⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[393]? = some (⟨234,(0),[5,6],[174],1072⟩) from rfl))
private theorem rec12329 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(1),[5,6],[174],1073⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[400]? = some (⟨234,(1),[5,6],[174],1073⟩) from rfl))
private theorem rec12337 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(2),[5,6],[174],1072⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[408]? = some (⟨234,(2),[5,6],[174],1072⟩) from rfl))
private theorem rec12345 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(3),[5,6],[174],1074⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[416]? = some (⟨234,(3),[5,6],[174],1074⟩) from rfl))
private theorem rec12352 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(4),[5,6],[174],1075⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[423]? = some (⟨234,(4),[5,6],[174],1075⟩) from rfl))
private theorem rec12359 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(5),[5,6],[174],1075⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[430]? = some (⟨234,(5),[5,6],[174],1075⟩) from rfl))
private theorem rec12367 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(6),[5,6],[174],1075⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[438]? = some (⟨234,(6),[5,6],[174],1075⟩) from rfl))
private theorem rec12375 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(7),[5,6],[174],1075⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[446]? = some (⟨234,(7),[5,6],[174],1075⟩) from rfl))
private theorem rec12382 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(8),[5,6],[174],1076⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[453]? = some (⟨234,(8),[5,6],[174],1076⟩) from rfl))
private theorem rec12389 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(9),[5,6],[174],1076⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[460]? = some (⟨234,(9),[5,6],[174],1076⟩) from rfl))
private theorem rec12397 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(10),[5,6],[174],1076⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[468]? = some (⟨234,(10),[5,6],[174],1076⟩) from rfl))
private theorem rec12405 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(11),[5,6],[174],1076⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[476]? = some (⟨234,(11),[5,6],[174],1076⟩) from rfl))
private theorem rec12412 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(12),[5,6],[174],1077⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[483]? = some (⟨234,(12),[5,6],[174],1077⟩) from rfl))
private theorem rec12419 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(13),[5,6],[174],1077⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[490]? = some (⟨234,(13),[5,6],[174],1077⟩) from rfl))
private theorem rec12427 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(14),[5,6],[174],1077⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[498]? = some (⟨234,(14),[5,6],[174],1077⟩) from rfl))
private theorem rec12435 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 234 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(15),[5,6],[174],1077⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[506]? = some (⟨234,(15),[5,6],[174],1077⟩) from rfl))
private theorem rec12442 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(0),[5,6],[174],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[513]? = some (⟨235,(0),[5,6],[174],578⟩) from rfl))
private theorem rec12448 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(1),[5,6],[174],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[0]? = some (⟨235,(1),[5,6],[174],579⟩) from rfl))
private theorem rec12455 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(2),[5,6],[174],1078⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[7]? = some (⟨235,(2),[5,6],[174],1078⟩) from rfl))
private theorem rec12462 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(3),[5,6],[174],1079⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[14]? = some (⟨235,(3),[5,6],[174],1079⟩) from rfl))
private theorem rec12468 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(4),[5,6],[174],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[20]? = some (⟨235,(4),[5,6],[174],582⟩) from rfl))
private theorem rec12474 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(5),[5,6],[174],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[26]? = some (⟨235,(5),[5,6],[174],583⟩) from rfl))
private theorem rec12481 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(6),[5,6],[174],1080⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[33]? = some (⟨235,(6),[5,6],[174],1080⟩) from rfl))
private theorem rec12488 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(7),[5,6],[174],1081⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[40]? = some (⟨235,(7),[5,6],[174],1081⟩) from rfl))
private theorem rec12494 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(8),[5,6],[174],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[46]? = some (⟨235,(8),[5,6],[174],578⟩) from rfl))
private theorem rec12500 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(9),[5,6],[174],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[52]? = some (⟨235,(9),[5,6],[174],579⟩) from rfl))
private theorem rec12507 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(10),[5,6],[174],1078⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[59]? = some (⟨235,(10),[5,6],[174],1078⟩) from rfl))
private theorem rec12514 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(11),[5,6],[174],1079⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[66]? = some (⟨235,(11),[5,6],[174],1079⟩) from rfl))
private theorem rec12520 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(12),[5,6],[174],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[72]? = some (⟨235,(12),[5,6],[174],586⟩) from rfl))
private theorem rec12526 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(13),[5,6],[174],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[78]? = some (⟨235,(13),[5,6],[174],587⟩) from rfl))
private theorem rec12533 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(14),[5,6],[174],1082⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[85]? = some (⟨235,(14),[5,6],[174],1082⟩) from rfl))
private theorem rec12540 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 235 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(15),[5,6],[174],1083⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[92]? = some (⟨235,(15),[5,6],[174],1083⟩) from rfl))
private theorem rec12546 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 236 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(0),[5,6],[174],861⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[98]? = some (⟨236,(0),[5,6],[174],861⟩) from rfl))
private theorem rec12553 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 236 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(1),[5,6],[174],862⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[105]? = some (⟨236,(1),[5,6],[174],862⟩) from rfl))
private theorem rec12562 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 236 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(2),[6],[174],863⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[114]? = some (⟨236,(2),[6],[174],863⟩) from rfl))
private theorem rec12569 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 236 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(3),[5,6],[174],864⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[121]? = some (⟨236,(3),[5,6],[174],864⟩) from rfl))
private theorem rec12576 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(0),[5,6],[174],865⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[128]? = some (⟨237,(0),[5,6],[174],865⟩) from rfl))
private theorem rec12583 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(1),[5,6],[174],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[135]? = some (⟨237,(1),[5,6],[174],594⟩) from rfl))
private theorem rec12590 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(2),[5,6],[174],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[142]? = some (⟨237,(2),[5,6],[174],595⟩) from rfl))
private theorem rec12597 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(3),[5,6],[174],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[149]? = some (⟨237,(3),[5,6],[174],596⟩) from rfl))
private theorem rec12604 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(4),[5,6],[174],866⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[156]? = some (⟨237,(4),[5,6],[174],866⟩) from rfl))
private theorem rec12611 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(5),[5,6],[174],598⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[163]? = some (⟨237,(5),[5,6],[174],598⟩) from rfl))
private theorem rec12617 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(6),[5,6],[174],599⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[169]? = some (⟨237,(6),[5,6],[174],599⟩) from rfl))
private theorem rec12623 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(7),[5,6],[174],600⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[175]? = some (⟨237,(7),[5,6],[174],600⟩) from rfl))
private theorem rec12631 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(8),[6],[174],867⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[183]? = some (⟨237,(8),[6],[174],867⟩) from rfl))
private theorem rec12638 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(9),[5,6],[174],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[190]? = some (⟨237,(9),[5,6],[174],594⟩) from rfl))
private theorem rec12644 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(10),[5,6],[174],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[196]? = some (⟨237,(10),[5,6],[174],595⟩) from rfl))
private theorem rec12650 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(11),[5,6],[174],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[202]? = some (⟨237,(11),[5,6],[174],596⟩) from rfl))
private theorem rec12656 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(12),[5,6],[174],868⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[208]? = some (⟨237,(12),[5,6],[174],868⟩) from rfl))
private theorem rec12663 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(13),[5,6],[174],602⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[215]? = some (⟨237,(13),[5,6],[174],602⟩) from rfl))
private theorem rec12669 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(14),[5,6],[174],603⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[221]? = some (⟨237,(14),[5,6],[174],603⟩) from rfl))
private theorem rec12675 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(15),[5,6],[174],604⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[227]? = some (⟨237,(15),[5,6],[174],604⟩) from rfl))
private theorem rec12681 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(0),[5,6],[174],869⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[233]? = some (⟨238,(0),[5,6],[174],869⟩) from rfl))
private theorem rec12687 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(1),[5,6],[174],870⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[239]? = some (⟨238,(1),[5,6],[174],870⟩) from rfl))
private theorem rec12694 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(2),[5,6],[174],1084⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[246]? = some (⟨238,(2),[5,6],[174],1084⟩) from rfl))
private theorem rec12701 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(3),[5,6],[174],1085⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[253]? = some (⟨238,(3),[5,6],[174],1085⟩) from rfl))
private theorem rec12708 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(4),[5,6],[174],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[260]? = some (⟨238,(4),[5,6],[174],609⟩) from rfl))
private theorem rec12714 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(5),[5,6],[174],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[266]? = some (⟨238,(5),[5,6],[174],610⟩) from rfl))
private theorem rec12721 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(6),[5,6],[174],298⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[273]? = some (⟨238,(6),[5,6],[174],298⟩) from rfl))
private theorem rec12728 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(7),[5,6],[174],298⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[280]? = some (⟨238,(7),[5,6],[174],298⟩) from rfl))
private theorem rec12734 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(8),[5,6],[174],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[286]? = some (⟨238,(8),[5,6],[174],613⟩) from rfl))
private theorem rec12740 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(9),[5,6],[174],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[292]? = some (⟨238,(9),[5,6],[174],614⟩) from rfl))
private theorem rec12747 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(10),[5,6],[174],299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[299]? = some (⟨238,(10),[5,6],[174],299⟩) from rfl))
private theorem rec12754 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(11),[5,6],[174],299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[306]? = some (⟨238,(11),[5,6],[174],299⟩) from rfl))
private theorem rec12760 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(12),[5,6],[174],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[312]? = some (⟨238,(12),[5,6],[174],617⟩) from rfl))
private theorem rec12766 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(13),[5,6],[174],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[318]? = some (⟨238,(13),[5,6],[174],618⟩) from rfl))
private theorem rec12773 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(14),[5,6],[174],300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[325]? = some (⟨238,(14),[5,6],[174],300⟩) from rfl))
private theorem rec12780 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 238 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(15),[5,6],[174],300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[332]? = some (⟨238,(15),[5,6],[174],300⟩) from rfl))
private theorem rec12785 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(0),[5,6],[174],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[337]? = some (⟨242,(0),[5,6],[174],632⟩) from rfl))
private theorem rec12789 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(1),[5,6],[174],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[341]? = some (⟨242,(1),[5,6],[174],872⟩) from rfl))
private theorem rec12793 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(2),[5,6],[174],873⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[345]? = some (⟨242,(2),[5,6],[174],873⟩) from rfl))
private theorem rec12797 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(3),[5,6],[174],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[349]? = some (⟨242,(3),[5,6],[174],101⟩) from rfl))
private theorem rec12801 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(4),[5,6],[174],873⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[353]? = some (⟨242,(4),[5,6],[174],873⟩) from rfl))
private theorem rec12805 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(5),[5,6],[174],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[357]? = some (⟨242,(5),[5,6],[174],632⟩) from rfl))
private theorem rec12809 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(6),[5,6],[174],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[361]? = some (⟨242,(6),[5,6],[174],872⟩) from rfl))
private theorem rec12813 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(7),[5,6],[174],874⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[365]? = some (⟨242,(7),[5,6],[174],874⟩) from rfl))
private theorem rec12817 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(8),[5,6],[174],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[369]? = some (⟨242,(8),[5,6],[174],101⟩) from rfl))
private theorem rec12821 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(9),[5,6],[174],874⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[373]? = some (⟨242,(9),[5,6],[174],874⟩) from rfl))
private theorem rec12825 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(10),[5,6],[174],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[377]? = some (⟨242,(10),[5,6],[174],632⟩) from rfl))
private theorem rec12829 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(11),[5,6],[174],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[381]? = some (⟨242,(11),[5,6],[174],872⟩) from rfl))
private theorem rec12833 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(12),[5,6],[174],875⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[385]? = some (⟨242,(12),[5,6],[174],875⟩) from rfl))
private theorem rec12837 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(13),[5,6],[174],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[389]? = some (⟨242,(13),[5,6],[174],101⟩) from rfl))
private theorem rec12841 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(14),[5,6],[174],875⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[393]? = some (⟨242,(14),[5,6],[174],875⟩) from rfl))
private theorem rec12845 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(15),[5,6],[174],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[397]? = some (⟨242,(15),[5,6],[174],625⟩) from rfl))
private theorem rec12849 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(16),[5,6],[174],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[401]? = some (⟨242,(16),[5,6],[174],626⟩) from rfl))
private theorem rec12853 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(17),[5,6],[174],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[405]? = some (⟨242,(17),[5,6],[174],286⟩) from rfl))
private theorem rec12857 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(18),[5,6],[174],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[409]? = some (⟨242,(18),[5,6],[174],101⟩) from rfl))
private theorem rec12861 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(19),[5,6],[174],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[413]? = some (⟨242,(19),[5,6],[174],286⟩) from rfl))
private theorem rec12865 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(20),[5,6],[174],876⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[417]? = some (⟨242,(20),[5,6],[174],876⟩) from rfl))
private theorem rec12869 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(21),[5,6],[174],877⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[421]? = some (⟨242,(21),[5,6],[174],877⟩) from rfl))
private theorem rec12873 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(22),[5,6],[174],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[425]? = some (⟨242,(22),[5,6],[174],287⟩) from rfl))
private theorem rec12877 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(23),[5,6],[174],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[429]? = some (⟨242,(23),[5,6],[174],101⟩) from rfl))
private theorem rec12881 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 242 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(24),[5,6],[174],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[433]? = some (⟨242,(24),[5,6],[174],287⟩) from rfl))
private theorem rec12885 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 243 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(5),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[437]? = some (⟨243,(5),[5,6],[174],3⟩) from rfl))
private theorem rec12893 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 243 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(7),[6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[445]? = some (⟨243,(7),[6],[174],3⟩) from rfl))
private theorem rec12899 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 243 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(8),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[451]? = some (⟨243,(8),[5,6],[174],3⟩) from rfl))
private theorem rec12903 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 243 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(9),[5,6],[174],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[455]? = some (⟨243,(9),[5,6],[174],143⟩) from rfl))
private theorem rec12910 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 243 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(15),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[462]? = some (⟨243,(15),[5,6],[174],3⟩) from rfl))
private theorem rec12917 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 243 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(16),[5,6],[174],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[469]? = some (⟨243,(16),[5,6],[174],3⟩) from rfl))
private theorem rec12922 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 243 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(17),[5,6],[174],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[474]? = some (⟨243,(17),[5,6],[174],48⟩) from rfl))
private theorem rec12927 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 243 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(19),[5,6],[174],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[479]? = some (⟨243,(19),[5,6],[174],143⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 69).take 22, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 174 gs.1 j := by
  have hp : ((section14State section14Catalog 6).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 69).take 22) = [(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      exact rec11141 6 174 (by decide) (by decide)
    · right
      exact rec11147 6 174 (by decide) (by decide)
    · right
      exact rec11153 6 174 (by decide) (by decide)
    · right
      exact rec11159 6 174 (by decide) (by decide)
    · right
      exact rec11165 6 174 (by decide) (by decide)
    · right
      exact rec11172 6 174 (by decide) (by decide)
    · right
      exact rec11180 6 174 (by decide) (by decide)
    · right
      exact rec11188 6 174 (by decide) (by decide)
    · right
      exact rec11196 6 174 (by decide) (by decide)
    · right
      exact rec11204 6 174 (by decide) (by decide)
    · right
      exact rec11212 6 174 (by decide) (by decide)
    · right
      exact rec11220 6 174 (by decide) (by decide)
    · right
      exact rec11228 6 174 (by decide) (by decide)
    · right
      exact rec11236 6 174 (by decide) (by decide)
    · right
      exact rec11244 6 174 (by decide) (by decide)
    · right
      exact rec11252 6 174 (by decide) (by decide)
    · right
      exact rec11260 6 174 (by decide) (by decide)
    · right
      exact rec11268 6 174 (by decide) (by decide)
    · right
      exact rec11276 6 174 (by decide) (by decide)
    · right
      exact rec11284 6 174 (by decide) (by decide)
    · right
      exact rec11292 6 174 (by decide) (by decide)
    · right
      exact rec11300 6 174 (by decide) (by decide)
    · right
      exact rec11308 6 174 (by decide) (by decide)
    · right
      exact rec11316 6 174 (by decide) (by decide)
    · right
      exact rec11324 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 225)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11331 6 174 (by decide) (by decide)
    · right
      exact rec11337 6 174 (by decide) (by decide)
    · right
      exact rec11343 6 174 (by decide) (by decide)
    · right
      exact rec11350 6 174 (by decide) (by decide)
    · right
      exact rec11357 6 174 (by decide) (by decide)
    · right
      exact rec11364 6 174 (by decide) (by decide)
    · right
      exact rec11370 6 174 (by decide) (by decide)
    · right
      exact rec11377 6 174 (by decide) (by decide)
    · right
      exact rec11384 6 174 (by decide) (by decide)
    · right
      exact rec11392 6 174 (by decide) (by decide)
    · right
      exact rec11399 6 174 (by decide) (by decide)
    · right
      exact rec11405 6 174 (by decide) (by decide)
    · right
      exact rec11412 6 174 (by decide) (by decide)
    · right
      exact rec11419 6 174 (by decide) (by decide)
    · right
      exact rec11427 6 174 (by decide) (by decide)
    · right
      exact rec11434 6 174 (by decide) (by decide)
    · right
      exact rec11440 6 174 (by decide) (by decide)
    · right
      exact rec11447 6 174 (by decide) (by decide)
    · right
      exact rec11454 6 174 (by decide) (by decide)
    · right
      exact rec11462 6 174 (by decide) (by decide)
    · right
      exact rec11469 6 174 (by decide) (by decide)
    · right
      exact rec11475 6 174 (by decide) (by decide)
    · right
      exact rec11482 6 174 (by decide) (by decide)
    · right
      exact rec11489 6 174 (by decide) (by decide)
    · right
      exact rec11497 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 226)).length = 10 := by decide +kernel
    have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11504 6 174 (by decide) (by decide)
    · right
      exact rec11511 6 174 (by decide) (by decide)
    · right
      exact rec11517 6 174 (by decide) (by decide)
    · right
      exact rec11523 6 174 (by decide) (by decide)
    · right
      exact rec11529 6 174 (by decide) (by decide)
    · right
      exact rec11535 6 174 (by decide) (by decide)
    · right
      exact rec11541 6 174 (by decide) (by decide)
    · right
      exact rec11547 6 174 (by decide) (by decide)
    · right
      exact rec11553 6 174 (by decide) (by decide)
    · right
      exact rec11559 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 227)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11565 6 174 (by decide) (by decide)
    · right
      exact rec11571 6 174 (by decide) (by decide)
    · right
      exact rec11578 6 174 (by decide) (by decide)
    · right
      exact rec11585 6 174 (by decide) (by decide)
    · right
      exact rec11592 6 174 (by decide) (by decide)
    · right
      exact rec11599 6 174 (by decide) (by decide)
    · right
      exact rec11605 6 174 (by decide) (by decide)
    · right
      exact rec11612 6 174 (by decide) (by decide)
    · right
      exact rec11619 6 174 (by decide) (by decide)
    · right
      exact rec11626 6 174 (by decide) (by decide)
    · right
      exact rec11633 6 174 (by decide) (by decide)
    · right
      exact rec11639 6 174 (by decide) (by decide)
    · right
      exact rec11646 6 174 (by decide) (by decide)
    · right
      exact rec11653 6 174 (by decide) (by decide)
    · right
      exact rec11660 6 174 (by decide) (by decide)
    · right
      exact rec11667 6 174 (by decide) (by decide)
    · right
      exact rec11673 6 174 (by decide) (by decide)
    · right
      exact rec11680 6 174 (by decide) (by decide)
    · right
      exact rec11687 6 174 (by decide) (by decide)
    · right
      exact rec11694 6 174 (by decide) (by decide)
    · right
      exact rec11701 6 174 (by decide) (by decide)
    · right
      exact rec11707 6 174 (by decide) (by decide)
    · right
      exact rec11714 6 174 (by decide) (by decide)
    · right
      exact rec11721 6 174 (by decide) (by decide)
    · right
      exact rec11728 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 228)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11735 6 174 (by decide) (by decide)
    · right
      exact rec11742 6 174 (by decide) (by decide)
    · right
      exact rec11751 6 174 (by decide) (by decide)
    · right
      exact rec11759 6 174 (by decide) (by decide)
    · right
      exact rec11766 6 174 (by decide) (by decide)
    · right
      exact rec11772 6 174 (by decide) (by decide)
    · right
      exact rec11778 6 174 (by decide) (by decide)
    · right
      exact rec11784 6 174 (by decide) (by decide)
    · right
      exact rec11790 6 174 (by decide) (by decide)
    · right
      exact rec11796 6 174 (by decide) (by decide)
    · right
      exact rec11803 6 174 (by decide) (by decide)
    · right
      exact rec11809 6 174 (by decide) (by decide)
    · right
      exact rec11815 6 174 (by decide) (by decide)
    · right
      exact rec11821 6 174 (by decide) (by decide)
    · right
      exact rec11827 6 174 (by decide) (by decide)
    · right
      exact rec11833 6 174 (by decide) (by decide)
    · right
      exact rec11839 6 174 (by decide) (by decide)
    · right
      exact rec11845 6 174 (by decide) (by decide)
    · right
      exact rec11851 6 174 (by decide) (by decide)
    · right
      exact rec11857 6 174 (by decide) (by decide)
    · right
      exact rec11863 6 174 (by decide) (by decide)
    · right
      exact rec11869 6 174 (by decide) (by decide)
    · right
      exact rec11875 6 174 (by decide) (by decide)
    · right
      exact rec11881 6 174 (by decide) (by decide)
    · right
      exact rec11887 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 229)).length = 25 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 230)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11893 6 174 (by decide) (by decide)
    · right
      exact rec11899 6 174 (by decide) (by decide)
    · right
      exact rec11906 6 174 (by decide) (by decide)
    · right
      exact rec11912 6 174 (by decide) (by decide)
    · right
      exact rec11918 6 174 (by decide) (by decide)
    · right
      exact rec11924 6 174 (by decide) (by decide)
    · right
      exact rec11930 6 174 (by decide) (by decide)
    · right
      exact rec11939 6 174 (by decide) (by decide)
    · right
      exact rec11945 6 174 (by decide) (by decide)
    · right
      exact rec11954 6 174 (by decide) (by decide)
    · right
      exact rec11961 6 174 (by decide) (by decide)
    · right
      exact rec11967 6 174 (by decide) (by decide)
    · right
      exact rec11975 6 174 (by decide) (by decide)
    · right
      exact rec11981 6 174 (by decide) (by decide)
    · right
      exact rec11989 6 174 (by decide) (by decide)
    · right
      exact rec11996 6 174 (by decide) (by decide)
    · right
      exact rec12002 6 174 (by decide) (by decide)
    · right
      exact rec12009 6 174 (by decide) (by decide)
    · right
      exact rec12016 6 174 (by decide) (by decide)
    · right
      exact rec12023 6 174 (by decide) (by decide)
    · right
      exact rec12030 6 174 (by decide) (by decide)
    · right
      exact rec12036 6 174 (by decide) (by decide)
    · right
      exact rec12043 6 174 (by decide) (by decide)
    · right
      exact rec12050 6 174 (by decide) (by decide)
    · right
      exact rec12057 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 231)).length = 20 := by decide +kernel
    have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12064 6 174 (by decide) (by decide)
    · right
      exact rec12071 6 174 (by decide) (by decide)
    · right
      exact rec12079 6 174 (by decide) (by decide)
    · right
      exact rec12085 6 174 (by decide) (by decide)
    · right
      exact rec12091 6 174 (by decide) (by decide)
    · right
      exact rec12098 6 174 (by decide) (by decide)
    · right
      exact rec12106 6 174 (by decide) (by decide)
    · right
      exact rec12112 6 174 (by decide) (by decide)
    · right
      exact rec12118 6 174 (by decide) (by decide)
    · right
      exact rec12124 6 174 (by decide) (by decide)
    · right
      exact rec12130 6 174 (by decide) (by decide)
    · right
      exact rec12136 6 174 (by decide) (by decide)
    · right
      exact rec12142 6 174 (by decide) (by decide)
    · right
      exact rec12148 6 174 (by decide) (by decide)
    · right
      exact rec12154 6 174 (by decide) (by decide)
    · right
      exact rec12160 6 174 (by decide) (by decide)
    · right
      exact rec12166 6 174 (by decide) (by decide)
    · right
      exact rec12172 6 174 (by decide) (by decide)
    · right
      exact rec12178 6 174 (by decide) (by decide)
    · right
      exact rec12184 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 232)).length = 20 := by decide +kernel
    have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12190 6 174 (by decide) (by decide)
    · right
      exact rec12196 6 174 (by decide) (by decide)
    · right
      exact rec12202 6 174 (by decide) (by decide)
    · right
      exact rec12209 6 174 (by decide) (by decide)
    · right
      exact rec12217 6 174 (by decide) (by decide)
    · right
      exact rec12223 6 174 (by decide) (by decide)
    · right
      exact rec12229 6 174 (by decide) (by decide)
    · right
      exact rec12235 6 174 (by decide) (by decide)
    · right
      exact rec12242 6 174 (by decide) (by decide)
    · right
      exact rec12249 6 174 (by decide) (by decide)
    · right
      exact rec12256 6 174 (by decide) (by decide)
    · right
      exact rec12262 6 174 (by decide) (by decide)
    · right
      exact rec12268 6 174 (by decide) (by decide)
    · right
      exact rec12275 6 174 (by decide) (by decide)
    · right
      exact rec12282 6 174 (by decide) (by decide)
    · right
      exact rec12289 6 174 (by decide) (by decide)
    · right
      exact rec12295 6 174 (by decide) (by decide)
    · right
      exact rec12301 6 174 (by decide) (by decide)
    · right
      exact rec12308 6 174 (by decide) (by decide)
    · right
      exact rec12315 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 233)).length = 4 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 234)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12322 6 174 (by decide) (by decide)
    · right
      exact rec12329 6 174 (by decide) (by decide)
    · right
      exact rec12337 6 174 (by decide) (by decide)
    · right
      exact rec12345 6 174 (by decide) (by decide)
    · right
      exact rec12352 6 174 (by decide) (by decide)
    · right
      exact rec12359 6 174 (by decide) (by decide)
    · right
      exact rec12367 6 174 (by decide) (by decide)
    · right
      exact rec12375 6 174 (by decide) (by decide)
    · right
      exact rec12382 6 174 (by decide) (by decide)
    · right
      exact rec12389 6 174 (by decide) (by decide)
    · right
      exact rec12397 6 174 (by decide) (by decide)
    · right
      exact rec12405 6 174 (by decide) (by decide)
    · right
      exact rec12412 6 174 (by decide) (by decide)
    · right
      exact rec12419 6 174 (by decide) (by decide)
    · right
      exact rec12427 6 174 (by decide) (by decide)
    · right
      exact rec12435 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 235)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12442 6 174 (by decide) (by decide)
    · right
      exact rec12448 6 174 (by decide) (by decide)
    · right
      exact rec12455 6 174 (by decide) (by decide)
    · right
      exact rec12462 6 174 (by decide) (by decide)
    · right
      exact rec12468 6 174 (by decide) (by decide)
    · right
      exact rec12474 6 174 (by decide) (by decide)
    · right
      exact rec12481 6 174 (by decide) (by decide)
    · right
      exact rec12488 6 174 (by decide) (by decide)
    · right
      exact rec12494 6 174 (by decide) (by decide)
    · right
      exact rec12500 6 174 (by decide) (by decide)
    · right
      exact rec12507 6 174 (by decide) (by decide)
    · right
      exact rec12514 6 174 (by decide) (by decide)
    · right
      exact rec12520 6 174 (by decide) (by decide)
    · right
      exact rec12526 6 174 (by decide) (by decide)
    · right
      exact rec12533 6 174 (by decide) (by decide)
    · right
      exact rec12540 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 236)).length = 4 := by decide +kernel
    have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12546 6 174 (by decide) (by decide)
    · right
      exact rec12553 6 174 (by decide) (by decide)
    · right
      exact rec12562 6 174 (by decide) (by decide)
    · right
      exact rec12569 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 237)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12576 6 174 (by decide) (by decide)
    · right
      exact rec12583 6 174 (by decide) (by decide)
    · right
      exact rec12590 6 174 (by decide) (by decide)
    · right
      exact rec12597 6 174 (by decide) (by decide)
    · right
      exact rec12604 6 174 (by decide) (by decide)
    · right
      exact rec12611 6 174 (by decide) (by decide)
    · right
      exact rec12617 6 174 (by decide) (by decide)
    · right
      exact rec12623 6 174 (by decide) (by decide)
    · right
      exact rec12631 6 174 (by decide) (by decide)
    · right
      exact rec12638 6 174 (by decide) (by decide)
    · right
      exact rec12644 6 174 (by decide) (by decide)
    · right
      exact rec12650 6 174 (by decide) (by decide)
    · right
      exact rec12656 6 174 (by decide) (by decide)
    · right
      exact rec12663 6 174 (by decide) (by decide)
    · right
      exact rec12669 6 174 (by decide) (by decide)
    · right
      exact rec12675 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 238)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12681 6 174 (by decide) (by decide)
    · right
      exact rec12687 6 174 (by decide) (by decide)
    · right
      exact rec12694 6 174 (by decide) (by decide)
    · right
      exact rec12701 6 174 (by decide) (by decide)
    · right
      exact rec12708 6 174 (by decide) (by decide)
    · right
      exact rec12714 6 174 (by decide) (by decide)
    · right
      exact rec12721 6 174 (by decide) (by decide)
    · right
      exact rec12728 6 174 (by decide) (by decide)
    · right
      exact rec12734 6 174 (by decide) (by decide)
    · right
      exact rec12740 6 174 (by decide) (by decide)
    · right
      exact rec12747 6 174 (by decide) (by decide)
    · right
      exact rec12754 6 174 (by decide) (by decide)
    · right
      exact rec12760 6 174 (by decide) (by decide)
    · right
      exact rec12766 6 174 (by decide) (by decide)
    · right
      exact rec12773 6 174 (by decide) (by decide)
    · right
      exact rec12780 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 239)).length = 20 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 240)).length = 20 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 241)).length = 10 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 242)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12785 6 174 (by decide) (by decide)
    · right
      exact rec12789 6 174 (by decide) (by decide)
    · right
      exact rec12793 6 174 (by decide) (by decide)
    · right
      exact rec12797 6 174 (by decide) (by decide)
    · right
      exact rec12801 6 174 (by decide) (by decide)
    · right
      exact rec12805 6 174 (by decide) (by decide)
    · right
      exact rec12809 6 174 (by decide) (by decide)
    · right
      exact rec12813 6 174 (by decide) (by decide)
    · right
      exact rec12817 6 174 (by decide) (by decide)
    · right
      exact rec12821 6 174 (by decide) (by decide)
    · right
      exact rec12825 6 174 (by decide) (by decide)
    · right
      exact rec12829 6 174 (by decide) (by decide)
    · right
      exact rec12833 6 174 (by decide) (by decide)
    · right
      exact rec12837 6 174 (by decide) (by decide)
    · right
      exact rec12841 6 174 (by decide) (by decide)
    · right
      exact rec12845 6 174 (by decide) (by decide)
    · right
      exact rec12849 6 174 (by decide) (by decide)
    · right
      exact rec12853 6 174 (by decide) (by decide)
    · right
      exact rec12857 6 174 (by decide) (by decide)
    · right
      exact rec12861 6 174 (by decide) (by decide)
    · right
      exact rec12865 6 174 (by decide) (by decide)
    · right
      exact rec12869 6 174 (by decide) (by decide)
    · right
      exact rec12873 6 174 (by decide) (by decide)
    · right
      exact rec12877 6 174 (by decide) (by decide)
    · right
      exact rec12881 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 243)).length = 20 := by decide +kernel
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
    · right
      exact rec12885 6 174 (by decide) (by decide)
    · left
      decide +kernel
    · right
      exact rec12893 6 174 (by decide) (by decide)
    · right
      exact rec12899 6 174 (by decide) (by decide)
    · right
      exact rec12903 6 174 (by decide) (by decide)
    · left
      decide +kernel
    · left
      decide +kernel
    · left
      decide +kernel
    · left
      decide +kernel
    · left
      decide +kernel
    · right
      exact rec12910 6 174 (by decide) (by decide)
    · right
      exact rec12917 6 174 (by decide) (by decide)
    · right
      exact rec12922 6 174 (by decide) (by decide)
    · left
      decide +kernel
    · right
      exact rec12927 6 174 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 244)).length = 10 := by decide +kernel
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
end Section14CoverageSpec_6_5_p174_69_91

#print axioms solution
