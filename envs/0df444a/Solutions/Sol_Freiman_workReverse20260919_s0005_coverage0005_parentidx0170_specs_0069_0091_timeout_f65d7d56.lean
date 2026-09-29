-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_coverage0005_parentidx0170_specs_0069_0091_timeout_f65d7d56
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T04:14:49.867477+00:00
-- url     : https://prove2.me/submissions/0f1f944c-55fe-4713-acfe-ce58dc9eb792

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
namespace Section14CoverageSpec_5_5_p170_69_91
private theorem rec11138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(0),[1,2,5,6,13,14],[170],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[409]? = some (⟨224,(0),[1,2,5,6,13,14],[170],539⟩) from rfl))
private theorem rec11144 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(1),[1,2,5,6,13,14],[170],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[415]? = some (⟨224,(1),[1,2,5,6,13,14],[170],539⟩) from rfl))
private theorem rec11150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(2),[1,2,5,6,13,14],[170],540⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[421]? = some (⟨224,(2),[1,2,5,6,13,14],[170],540⟩) from rfl))
private theorem rec11156 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(3),[1,2,5,6,13,14],[170],541⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[427]? = some (⟨224,(3),[1,2,5,6,13,14],[170],541⟩) from rfl))
private theorem rec11162 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(4),[1,2,5,6,13,14],[170],542⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[433]? = some (⟨224,(4),[1,2,5,6,13,14],[170],542⟩) from rfl))
private theorem rec11168 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(5),[1,2,5,6,13,14],[170],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[439]? = some (⟨224,(5),[1,2,5,6,13,14],[170],543⟩) from rfl))
private theorem rec11176 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(6),[1,2,5,6,13,14],[170],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[447]? = some (⟨224,(6),[1,2,5,6,13,14],[170],543⟩) from rfl))
private theorem rec11184 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(7),[1,2,5,6,13,14],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[455]? = some (⟨224,(7),[1,2,5,6,13,14],[170],544⟩) from rfl))
private theorem rec11192 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(8),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[463]? = some (⟨224,(8),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec11200 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(9),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[471]? = some (⟨224,(9),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec11208 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(10),[1,2,5,6,13,14],[170],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[479]? = some (⟨224,(10),[1,2,5,6,13,14],[170],545⟩) from rfl))
private theorem rec11216 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(11),[1,2,5,6,13,14],[170],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[487]? = some (⟨224,(11),[1,2,5,6,13,14],[170],545⟩) from rfl))
private theorem rec11224 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(12),[1,2,5,6,13,14],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[495]? = some (⟨224,(12),[1,2,5,6,13,14],[170],544⟩) from rfl))
private theorem rec11232 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(13),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[503]? = some (⟨224,(13),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec11240 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(14),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[511]? = some (⟨224,(14),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec11248 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(15),[1,2,5,6,13,14],[170],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[519]? = some (⟨224,(15),[1,2,5,6,13,14],[170],546⟩) from rfl))
private theorem rec11256 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(16),[1,2,5,6,13,14],[170],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[527]? = some (⟨224,(16),[1,2,5,6,13,14],[170],546⟩) from rfl))
private theorem rec11264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(17),[1,2,5,6,13,14],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[535]? = some (⟨224,(17),[1,2,5,6,13,14],[170],544⟩) from rfl))
private theorem rec11272 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(18),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[543]? = some (⟨224,(18),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec11280 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(19),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[551]? = some (⟨224,(19),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec11288 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(20),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[559]? = some (⟨224,(20),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11296 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(21),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[567]? = some (⟨224,(21),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11304 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(22),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[575]? = some (⟨224,(22),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11312 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(23),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[583]? = some (⟨224,(23),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec11320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(24),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[591]? = some (⟨224,(24),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec11328 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(0),[1,2,5,6,13,14],[170],747⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[599]? = some (⟨225,(0),[1,2,5,6,13,14],[170],747⟩) from rfl))
private theorem rec11334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(1),[1,2,5,6,13,14],[170],748⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[605]? = some (⟨225,(1),[1,2,5,6,13,14],[170],748⟩) from rfl))
private theorem rec11340 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(2),[1,2,5,6,13,14],[170],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[611]? = some (⟨225,(2),[1,2,5,6,13,14],[170],749⟩) from rfl))
private theorem rec11347 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(3),[1,2,5,6,13,14],[170],750⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[618]? = some (⟨225,(3),[1,2,5,6,13,14],[170],750⟩) from rfl))
private theorem rec11354 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(4),[1,2,5,6,13,14],[170],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[625]? = some (⟨225,(4),[1,2,5,6,13,14],[170],749⟩) from rfl))
private theorem rec11361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(5),[1,2,5,6,13,14],[170],751⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[632]? = some (⟨225,(5),[1,2,5,6,13,14],[170],751⟩) from rfl))
private theorem rec11367 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(6),[1,2,5,6,13,14],[170],752⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[638]? = some (⟨225,(6),[1,2,5,6,13,14],[170],752⟩) from rfl))
private theorem rec11373 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(7),[1,2,5,6,13,14],[170],753⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[644]? = some (⟨225,(7),[1,2,5,6,13,14],[170],753⟩) from rfl))
private theorem rec11381 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(8),[1,2,5,6,13,14],[170],754⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[652]? = some (⟨225,(8),[1,2,5,6,13,14],[170],754⟩) from rfl))
private theorem rec11388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(9),[1,2,5,6,13,14],[170],753⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[659]? = some (⟨225,(9),[1,2,5,6,13,14],[170],753⟩) from rfl))
private theorem rec11396 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(10),[1,2,5,6,13,14],[170],755⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[667]? = some (⟨225,(10),[1,2,5,6,13,14],[170],755⟩) from rfl))
private theorem rec11402 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(11),[1,2,5,6,13,14],[170],756⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[673]? = some (⟨225,(11),[1,2,5,6,13,14],[170],756⟩) from rfl))
private theorem rec11408 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(12),[1,2,5,6,13,14],[170],757⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[679]? = some (⟨225,(12),[1,2,5,6,13,14],[170],757⟩) from rfl))
private theorem rec11416 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(13),[1,2,5,6,13,14],[170],758⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[687]? = some (⟨225,(13),[1,2,5,6,13,14],[170],758⟩) from rfl))
private theorem rec11423 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(14),[1,2,5,6,13,14],[170],757⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[694]? = some (⟨225,(14),[1,2,5,6,13,14],[170],757⟩) from rfl))
private theorem rec11431 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(15),[1,2,5,6,13,14],[170],759⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[702]? = some (⟨225,(15),[1,2,5,6,13,14],[170],759⟩) from rfl))
private theorem rec11437 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(16),[1,2,5,6,13,14],[170],760⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[708]? = some (⟨225,(16),[1,2,5,6,13,14],[170],760⟩) from rfl))
private theorem rec11443 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(17),[1,2,5,6,13,14],[170],761⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[714]? = some (⟨225,(17),[1,2,5,6,13,14],[170],761⟩) from rfl))
private theorem rec11451 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(18),[1,2,5,6,13,14],[170],762⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[722]? = some (⟨225,(18),[1,2,5,6,13,14],[170],762⟩) from rfl))
private theorem rec11458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(19),[1,2,5,6,13,14],[170],761⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[729]? = some (⟨225,(19),[1,2,5,6,13,14],[170],761⟩) from rfl))
private theorem rec11466 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(20),[1,2,5,6,13,14],[170],763⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[737]? = some (⟨225,(20),[1,2,5,6,13,14],[170],763⟩) from rfl))
private theorem rec11472 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(21),[1,2,5,6,13,14],[170],764⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[743]? = some (⟨225,(21),[1,2,5,6,13,14],[170],764⟩) from rfl))
private theorem rec11478 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(22),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[749]? = some (⟨225,(22),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11486 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(23),[1,2,5,6,13,14],[170],765⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[757]? = some (⟨225,(23),[1,2,5,6,13,14],[170],765⟩) from rfl))
private theorem rec11493 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(24),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[764]? = some (⟨225,(24),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11501 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(0),[1,2,5,6,13,14],[170],766⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[772]? = some (⟨226,(0),[1,2,5,6,13,14],[170],766⟩) from rfl))
private theorem rec11508 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(1),[1,2,5,6,13,14],[170],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[779]? = some (⟨226,(1),[1,2,5,6,13,14],[170],767⟩) from rfl))
private theorem rec11514 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(2),[1,2,5,6,13,14],[170],768⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[785]? = some (⟨226,(2),[1,2,5,6,13,14],[170],768⟩) from rfl))
private theorem rec11520 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(3),[1,2,5,6,13,14],[170],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[791]? = some (⟨226,(3),[1,2,5,6,13,14],[170],767⟩) from rfl))
private theorem rec11526 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(4),[1,2,5,6,13,14],[170],769⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[797]? = some (⟨226,(4),[1,2,5,6,13,14],[170],769⟩) from rfl))
private theorem rec11532 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(5),[1,2,5,6,13,14],[170],770⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[803]? = some (⟨226,(5),[1,2,5,6,13,14],[170],770⟩) from rfl))
private theorem rec11538 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(6),[1,2,5,6,13,14],[170],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[809]? = some (⟨226,(6),[1,2,5,6,13,14],[170],771⟩) from rfl))
private theorem rec11544 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(7),[1,2,5,6,13,14],[170],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[815]? = some (⟨226,(7),[1,2,5,6,13,14],[170],771⟩) from rfl))
private theorem rec11550 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(8),[1,2,5,6,13,14],[170],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[821]? = some (⟨226,(8),[1,2,5,6,13,14],[170],772⟩) from rfl))
private theorem rec11556 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(9),[1,2,5,6,13,14],[170],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[827]? = some (⟨226,(9),[1,2,5,6,13,14],[170],772⟩) from rfl))
private theorem rec11562 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(0),[1,2,5,6,13,14],[170],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[833]? = some (⟨227,(0),[1,2,5,6,13,14],[170],773⟩) from rfl))
private theorem rec11568 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(1),[1,2,5,6,13,14],[170],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[839]? = some (⟨227,(1),[1,2,5,6,13,14],[170],774⟩) from rfl))
private theorem rec11574 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(2),[1,2,5,6,13,14],[170],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[845]? = some (⟨227,(2),[1,2,5,6,13,14],[170],775⟩) from rfl))
private theorem rec11582 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(3),[1,2,5,6,13,14],[170],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[853]? = some (⟨227,(3),[1,2,5,6,13,14],[170],776⟩) from rfl))
private theorem rec11588 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(4),[1,2,5,6,13,14],[170],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[859]? = some (⟨227,(4),[1,2,5,6,13,14],[170],775⟩) from rfl))
private theorem rec11596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(5),[1,2,5,6,13,14],[170],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[867]? = some (⟨227,(5),[1,2,5,6,13,14],[170],773⟩) from rfl))
private theorem rec11602 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(6),[1,2,5,6,13,14],[170],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[873]? = some (⟨227,(6),[1,2,5,6,13,14],[170],774⟩) from rfl))
private theorem rec11608 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(7),[1,2,5,6,13,14],[170],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[879]? = some (⟨227,(7),[1,2,5,6,13,14],[170],775⟩) from rfl))
private theorem rec11616 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(8),[1,2,5,6,13,14],[170],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[887]? = some (⟨227,(8),[1,2,5,6,13,14],[170],776⟩) from rfl))
private theorem rec11622 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(9),[1,2,5,6,13,14],[170],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[893]? = some (⟨227,(9),[1,2,5,6,13,14],[170],775⟩) from rfl))
private theorem rec11630 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(10),[1,2,5,6,13,14],[170],777⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[901]? = some (⟨227,(10),[1,2,5,6,13,14],[170],777⟩) from rfl))
private theorem rec11636 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(11),[1,2,5,6,13,14],[170],778⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[907]? = some (⟨227,(11),[1,2,5,6,13,14],[170],778⟩) from rfl))
private theorem rec11642 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(12),[1,2,5,6,13,14],[170],779⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[913]? = some (⟨227,(12),[1,2,5,6,13,14],[170],779⟩) from rfl))
private theorem rec11650 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(13),[1,2,5,6,13,14],[170],780⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[921]? = some (⟨227,(13),[1,2,5,6,13,14],[170],780⟩) from rfl))
private theorem rec11656 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(14),[1,2,5,6,13,14],[170],779⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[927]? = some (⟨227,(14),[1,2,5,6,13,14],[170],779⟩) from rfl))
private theorem rec11664 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(15),[1,2,5,6,13,14],[170],781⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[935]? = some (⟨227,(15),[1,2,5,6,13,14],[170],781⟩) from rfl))
private theorem rec11670 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(16),[1,2,5,6,13,14],[170],782⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[941]? = some (⟨227,(16),[1,2,5,6,13,14],[170],782⟩) from rfl))
private theorem rec11676 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(17),[1,2,5,6,13,14],[170],783⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[947]? = some (⟨227,(17),[1,2,5,6,13,14],[170],783⟩) from rfl))
private theorem rec11684 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(18),[1,2,5,6,13,14],[170],784⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[955]? = some (⟨227,(18),[1,2,5,6,13,14],[170],784⟩) from rfl))
private theorem rec11690 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(19),[1,2,5,6,13,14],[170],783⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[961]? = some (⟨227,(19),[1,2,5,6,13,14],[170],783⟩) from rfl))
private theorem rec11698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(20),[1,2,5,6,13,14],[170],785⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[969]? = some (⟨227,(20),[1,2,5,6,13,14],[170],785⟩) from rfl))
private theorem rec11704 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(21),[1,2,5,6,13,14],[170],786⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[975]? = some (⟨227,(21),[1,2,5,6,13,14],[170],786⟩) from rfl))
private theorem rec11710 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(22),[1,2,5,6,13,14],[170],787⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[981]? = some (⟨227,(22),[1,2,5,6,13,14],[170],787⟩) from rfl))
private theorem rec11718 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(23),[1,2,5,6,13,14],[170],788⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[989]? = some (⟨227,(23),[1,2,5,6,13,14],[170],788⟩) from rfl))
private theorem rec11724 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(24),[1,2,5,6,13,14],[170],787⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[995]? = some (⟨227,(24),[1,2,5,6,13,14],[170],787⟩) from rfl))
private theorem rec11732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(0),[1,2,5,6,13,14],[170],789⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1003]? = some (⟨228,(0),[1,2,5,6,13,14],[170],789⟩) from rfl))
private theorem rec11739 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(1),[1,2,5,6,13,14],[170],790⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1010]? = some (⟨228,(1),[1,2,5,6,13,14],[170],790⟩) from rfl))
private theorem rec11746 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(2),[1,5,6,13],[170],791⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1017]? = some (⟨228,(2),[1,5,6,13],[170],791⟩) from rfl))
private theorem rec11756 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(3),[1,2,5,6,13,14],[170],792⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1027]? = some (⟨228,(3),[1,2,5,6,13,14],[170],792⟩) from rfl))
private theorem rec11763 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(4),[1,2,5,6,13,14],[170],793⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1034]? = some (⟨228,(4),[1,2,5,6,13,14],[170],793⟩) from rfl))
private theorem rec11769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(5),[1,2,5,6,13,14],[170],794⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1040]? = some (⟨228,(5),[1,2,5,6,13,14],[170],794⟩) from rfl))
private theorem rec11775 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(6),[1,2,5,6,13,14],[170],795⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1046]? = some (⟨228,(6),[1,2,5,6,13,14],[170],795⟩) from rfl))
private theorem rec11781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(7),[1,2,5,6,13,14],[170],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1052]? = some (⟨228,(7),[1,2,5,6,13,14],[170],796⟩) from rfl))
private theorem rec11787 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(8),[1,2,5,6,13,14],[170],797⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1058]? = some (⟨228,(8),[1,2,5,6,13,14],[170],797⟩) from rfl))
private theorem rec11793 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(9),[1,2,5,6,13,14],[170],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1064]? = some (⟨228,(9),[1,2,5,6,13,14],[170],796⟩) from rfl))
private theorem rec11800 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(10),[1,2,5,6,13,14],[170],798⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1071]? = some (⟨228,(10),[1,2,5,6,13,14],[170],798⟩) from rfl))
private theorem rec11806 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(11),[1,2,5,6,13,14],[170],799⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1077]? = some (⟨228,(11),[1,2,5,6,13,14],[170],799⟩) from rfl))
private theorem rec11812 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(12),[1,2,5,6,13,14],[170],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1083]? = some (⟨228,(12),[1,2,5,6,13,14],[170],800⟩) from rfl))
private theorem rec11818 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(13),[1,2,5,6,13,14],[170],801⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1089]? = some (⟨228,(13),[1,2,5,6,13,14],[170],801⟩) from rfl))
private theorem rec11824 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(14),[1,2,5,6,13,14],[170],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1095]? = some (⟨228,(14),[1,2,5,6,13,14],[170],800⟩) from rfl))
private theorem rec11830 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(15),[1,2,5,6,13,14],[170],802⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1101]? = some (⟨228,(15),[1,2,5,6,13,14],[170],802⟩) from rfl))
private theorem rec11836 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(16),[1,2,5,6,13,14],[170],803⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1107]? = some (⟨228,(16),[1,2,5,6,13,14],[170],803⟩) from rfl))
private theorem rec11842 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(17),[1,2,5,6,13,14],[170],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1113]? = some (⟨228,(17),[1,2,5,6,13,14],[170],804⟩) from rfl))
private theorem rec11848 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(18),[1,2,5,6,13,14],[170],805⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1119]? = some (⟨228,(18),[1,2,5,6,13,14],[170],805⟩) from rfl))
private theorem rec11854 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(19),[1,2,5,6,13,14],[170],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1125]? = some (⟨228,(19),[1,2,5,6,13,14],[170],804⟩) from rfl))
private theorem rec11860 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(20),[1,2,5,6,13,14],[170],806⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1131]? = some (⟨228,(20),[1,2,5,6,13,14],[170],806⟩) from rfl))
private theorem rec11866 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(21),[1,2,5,6,13,14],[170],807⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1137]? = some (⟨228,(21),[1,2,5,6,13,14],[170],807⟩) from rfl))
private theorem rec11872 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(22),[1,2,5,6,13,14],[170],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1143]? = some (⟨228,(22),[1,2,5,6,13,14],[170],808⟩) from rfl))
private theorem rec11878 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(23),[1,2,5,6,13,14],[170],809⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1149]? = some (⟨228,(23),[1,2,5,6,13,14],[170],809⟩) from rfl))
private theorem rec11884 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(24),[1,2,5,6,13,14],[170],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1155]? = some (⟨228,(24),[1,2,5,6,13,14],[170],808⟩) from rfl))
private theorem rec11890 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(0),[1,2,5,6,13,14],[170],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1161]? = some (⟨230,(0),[1,2,5,6,13,14],[170],810⟩) from rfl))
private theorem rec11896 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(1),[1,2,5,6,13,14],[170],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1167]? = some (⟨230,(1),[1,2,5,6,13,14],[170],811⟩) from rfl))
private theorem rec11903 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(2),[1,2,5,6,13,14],[170],812⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1174]? = some (⟨230,(2),[1,2,5,6,13,14],[170],812⟩) from rfl))
private theorem rec11909 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(3),[1,2,5,6,13,14],[170],813⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1180]? = some (⟨230,(3),[1,2,5,6,13,14],[170],813⟩) from rfl))
private theorem rec11915 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(4),[1,2,5,6,13,14],[170],814⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1186]? = some (⟨230,(4),[1,2,5,6,13,14],[170],814⟩) from rfl))
private theorem rec11921 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(5),[1,2,5,6,13,14],[170],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1192]? = some (⟨230,(5),[1,2,5,6,13,14],[170],810⟩) from rfl))
private theorem rec11927 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(6),[1,2,5,6,13,14],[170],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1198]? = some (⟨230,(6),[1,2,5,6,13,14],[170],811⟩) from rfl))
private theorem rec11934 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(7),[1,5,6,13],[170],815⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[5]? = some (⟨230,(7),[1,5,6,13],[170],815⟩) from rfl))
private theorem rec11942 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(8),[1,2,5,6,13,14],[170],816⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[13]? = some (⟨230,(8),[1,2,5,6,13,14],[170],816⟩) from rfl))
private theorem rec11953 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(9),[5],[170],1375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[24]? = some (⟨230,(9),[5],[170],1375⟩) from rfl))
private theorem rec11958 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(10),[1,2,5,6,13,14],[170],818⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[29]? = some (⟨230,(10),[1,2,5,6,13,14],[170],818⟩) from rfl))
private theorem rec11964 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(11),[1,2,5,6,13,14],[170],819⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[35]? = some (⟨230,(11),[1,2,5,6,13,14],[170],819⟩) from rfl))
private theorem rec11970 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(12),[1,5,13],[170],820⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[41]? = some (⟨230,(12),[1,5,13],[170],820⟩) from rfl))
private theorem rec11978 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(13),[1,2,5,6,13,14],[170],821⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[49]? = some (⟨230,(13),[1,2,5,6,13,14],[170],821⟩) from rfl))
private theorem rec11988 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(14),[5],[170],1375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[59]? = some (⟨230,(14),[5],[170],1375⟩) from rfl))
private theorem rec11993 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(15),[1,2,5,6,13,14],[170],822⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[64]? = some (⟨230,(15),[1,2,5,6,13,14],[170],822⟩) from rfl))
private theorem rec11999 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(16),[1,2,5,6,13,14],[170],823⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[70]? = some (⟨230,(16),[1,2,5,6,13,14],[170],823⟩) from rfl))
private theorem rec12005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(17),[1,2,5,6,13,14],[170],824⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[76]? = some (⟨230,(17),[1,2,5,6,13,14],[170],824⟩) from rfl))
private theorem rec12013 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(18),[1,2,5,6,13,14],[170],825⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[84]? = some (⟨230,(18),[1,2,5,6,13,14],[170],825⟩) from rfl))
private theorem rec12019 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(19),[1,2,5,6,13,14],[170],824⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[90]? = some (⟨230,(19),[1,2,5,6,13,14],[170],824⟩) from rfl))
private theorem rec12027 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(20),[1,2,5,6,13,14],[170],826⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[98]? = some (⟨230,(20),[1,2,5,6,13,14],[170],826⟩) from rfl))
private theorem rec12033 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(21),[1,2,5,6,13,14],[170],827⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[104]? = some (⟨230,(21),[1,2,5,6,13,14],[170],827⟩) from rfl))
private theorem rec12039 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(22),[1,2,5,6,13,14],[170],828⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[110]? = some (⟨230,(22),[1,2,5,6,13,14],[170],828⟩) from rfl))
private theorem rec12047 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(23),[1,2,5,6,13,14],[170],829⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[118]? = some (⟨230,(23),[1,2,5,6,13,14],[170],829⟩) from rfl))
private theorem rec12053 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(24),[1,2,5,6,13,14],[170],828⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[124]? = some (⟨230,(24),[1,2,5,6,13,14],[170],828⟩) from rfl))
private theorem rec12061 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(0),[1,2,5,6,13,14],[170],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[132]? = some (⟨231,(0),[1,2,5,6,13,14],[170],830⟩) from rfl))
private theorem rec12068 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(1),[1,2,5,6,13,14],[170],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[139]? = some (⟨231,(1),[1,2,5,6,13,14],[170],831⟩) from rfl))
private theorem rec12076 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(2),[1,2,5,6,13,14],[170],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[147]? = some (⟨231,(2),[1,2,5,6,13,14],[170],832⟩) from rfl))
private theorem rec12082 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(3),[1,2,5,6,13,14],[170],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[153]? = some (⟨231,(3),[1,2,5,6,13,14],[170],833⟩) from rfl))
private theorem rec12088 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(4),[1,2,5,6,13,14],[170],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[159]? = some (⟨231,(4),[1,2,5,6,13,14],[170],830⟩) from rfl))
private theorem rec12095 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(5),[1,2,5,6,13,14],[170],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[166]? = some (⟨231,(5),[1,2,5,6,13,14],[170],831⟩) from rfl))
private theorem rec12103 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(6),[1,2,5,6,13,14],[170],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[174]? = some (⟨231,(6),[1,2,5,6,13,14],[170],832⟩) from rfl))
private theorem rec12109 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(7),[1,2,5,6,13,14],[170],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[180]? = some (⟨231,(7),[1,2,5,6,13,14],[170],833⟩) from rfl))
private theorem rec12115 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(8),[1,2,5,6,13,14],[170],834⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[186]? = some (⟨231,(8),[1,2,5,6,13,14],[170],834⟩) from rfl))
private theorem rec12121 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(9),[1,2,5,6,13,14],[170],835⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[192]? = some (⟨231,(9),[1,2,5,6,13,14],[170],835⟩) from rfl))
private theorem rec12127 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(10),[1,2,5,6,13,14],[170],836⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[198]? = some (⟨231,(10),[1,2,5,6,13,14],[170],836⟩) from rfl))
private theorem rec12133 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(11),[1,2,5,6,13,14],[170],837⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[204]? = some (⟨231,(11),[1,2,5,6,13,14],[170],837⟩) from rfl))
private theorem rec12139 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(12),[1,2,5,6,13,14],[170],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[210]? = some (⟨231,(12),[1,2,5,6,13,14],[170],838⟩) from rfl))
private theorem rec12145 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(13),[1,2,5,6,13,14],[170],839⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[216]? = some (⟨231,(13),[1,2,5,6,13,14],[170],839⟩) from rfl))
private theorem rec12151 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(14),[1,2,5,6,13,14],[170],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[222]? = some (⟨231,(14),[1,2,5,6,13,14],[170],838⟩) from rfl))
private theorem rec12157 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(15),[1,2,5,6,13,14],[170],840⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[228]? = some (⟨231,(15),[1,2,5,6,13,14],[170],840⟩) from rfl))
private theorem rec12163 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(16),[1,2,5,6,13,14],[170],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[234]? = some (⟨231,(16),[1,2,5,6,13,14],[170],841⟩) from rfl))
private theorem rec12169 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(17),[1,2,5,6,13,14],[170],842⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[240]? = some (⟨231,(17),[1,2,5,6,13,14],[170],842⟩) from rfl))
private theorem rec12175 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(18),[1,2,5,6,13,14],[170],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[246]? = some (⟨231,(18),[1,2,5,6,13,14],[170],841⟩) from rfl))
private theorem rec12181 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(19),[1,2,5,6,13,14],[170],843⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[252]? = some (⟨231,(19),[1,2,5,6,13,14],[170],843⟩) from rfl))
private theorem rec12187 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(0),[1,2,5,6,13,14],[170],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[258]? = some (⟨232,(0),[1,2,5,6,13,14],[170],844⟩) from rfl))
private theorem rec12193 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(1),[1,2,5,6,13,14],[170],845⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[264]? = some (⟨232,(1),[1,2,5,6,13,14],[170],845⟩) from rfl))
private theorem rec12199 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(2),[1,2,5,6,13,14],[170],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[270]? = some (⟨232,(2),[1,2,5,6,13,14],[170],846⟩) from rfl))
private theorem rec12206 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(3),[1,2,5,6,13,14],[170],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[277]? = some (⟨232,(3),[1,2,5,6,13,14],[170],847⟩) from rfl))
private theorem rec12212 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(4),[1,5,6,13],[170],848⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[283]? = some (⟨232,(4),[1,5,6,13],[170],848⟩) from rfl))
private theorem rec12220 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(5),[1,2,5,6,13,14],[170],849⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[291]? = some (⟨232,(5),[1,2,5,6,13,14],[170],849⟩) from rfl))
private theorem rec12226 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(6),[1,2,5,6,13,14],[170],850⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[297]? = some (⟨232,(6),[1,2,5,6,13,14],[170],850⟩) from rfl))
private theorem rec12232 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(7),[1,2,5,6,13,14],[170],851⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[303]? = some (⟨232,(7),[1,2,5,6,13,14],[170],851⟩) from rfl))
private theorem rec12239 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(8),[1,2,5,6,13,14],[170],852⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[310]? = some (⟨232,(8),[1,2,5,6,13,14],[170],852⟩) from rfl))
private theorem rec12245 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(9),[1,2,5,6,13,14],[170],853⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[316]? = some (⟨232,(9),[1,2,5,6,13,14],[170],853⟩) from rfl))
private theorem rec12253 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(10),[1,2,5,6,13,14],[170],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[324]? = some (⟨232,(10),[1,2,5,6,13,14],[170],844⟩) from rfl))
private theorem rec12259 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(11),[1,2,5,6,13,14],[170],854⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[330]? = some (⟨232,(11),[1,2,5,6,13,14],[170],854⟩) from rfl))
private theorem rec12265 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(12),[1,2,5,6,13,14],[170],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[336]? = some (⟨232,(12),[1,2,5,6,13,14],[170],846⟩) from rfl))
private theorem rec12272 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(13),[1,2,5,6,13,14],[170],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[343]? = some (⟨232,(13),[1,2,5,6,13,14],[170],847⟩) from rfl))
private theorem rec12278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[349]? = some (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) from rfl))
private theorem rec12286 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[357]? = some (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) from rfl))
private theorem rec12292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[363]? = some (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) from rfl))
private theorem rec12298 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[369]? = some (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) from rfl))
private theorem rec12305 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[376]? = some (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) from rfl))
private theorem rec12311 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[382]? = some (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) from rfl))
private theorem rec12319 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[390]? = some (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) from rfl))
private theorem rec12325 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[396]? = some (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) from rfl))
private theorem rec12333 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[404]? = some (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) from rfl))
private theorem rec12341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[412]? = some (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) from rfl))
private theorem rec12349 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[420]? = some (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) from rfl))
private theorem rec12355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[426]? = some (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) from rfl))
private theorem rec12363 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[434]? = some (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) from rfl))
private theorem rec12371 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[442]? = some (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) from rfl))
private theorem rec12379 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[450]? = some (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) from rfl))
private theorem rec12385 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[456]? = some (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) from rfl))
private theorem rec12393 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[464]? = some (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) from rfl))
private theorem rec12401 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[472]? = some (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) from rfl))
private theorem rec12409 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[480]? = some (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) from rfl))
private theorem rec12415 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[486]? = some (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) from rfl))
private theorem rec12423 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[494]? = some (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) from rfl))
private theorem rec12431 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[502]? = some (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) from rfl))
private theorem rec12439 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[510]? = some (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) from rfl))
private theorem rec12445 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[516]? = some (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) from rfl))
private theorem rec12451 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[3]? = some (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) from rfl))
private theorem rec12459 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[11]? = some (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) from rfl))
private theorem rec12465 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[17]? = some (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) from rfl))
private theorem rec12471 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[23]? = some (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) from rfl))
private theorem rec12477 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[29]? = some (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) from rfl))
private theorem rec12485 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[37]? = some (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) from rfl))
private theorem rec12491 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(8),[1,2,5,6,13,14],[170],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[43]? = some (⟨235,(8),[1,2,5,6,13,14],[170],578⟩) from rfl))
private theorem rec12497 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(9),[1,2,5,6,13,14],[170],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[49]? = some (⟨235,(9),[1,2,5,6,13,14],[170],579⟩) from rfl))
private theorem rec12503 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(10),[1,2,5,6,13,14],[170],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[55]? = some (⟨235,(10),[1,2,5,6,13,14],[170],580⟩) from rfl))
private theorem rec12511 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(11),[1,2,5,6,13,14],[170],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[63]? = some (⟨235,(11),[1,2,5,6,13,14],[170],581⟩) from rfl))
private theorem rec12517 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(12),[1,2,5,6,13,14],[170],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[69]? = some (⟨235,(12),[1,2,5,6,13,14],[170],586⟩) from rfl))
private theorem rec12523 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(13),[1,2,5,6,13,14],[170],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[75]? = some (⟨235,(13),[1,2,5,6,13,14],[170],587⟩) from rfl))
private theorem rec12529 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(14),[1,2,5,6,13,14],[170],588⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[81]? = some (⟨235,(14),[1,2,5,6,13,14],[170],588⟩) from rfl))
private theorem rec12537 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(15),[1,2,5,6,13,14],[170],589⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[89]? = some (⟨235,(15),[1,2,5,6,13,14],[170],589⟩) from rfl))
private theorem rec12543 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 236 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(0),[1,2,5,6,13,14],[170],861⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[95]? = some (⟨236,(0),[1,2,5,6,13,14],[170],861⟩) from rfl))
private theorem rec12550 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 236 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(1),[1,2,5,6,13,14],[170],862⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[102]? = some (⟨236,(1),[1,2,5,6,13,14],[170],862⟩) from rfl))
private theorem rec12561 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 236 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(2),[5],[170,174],861⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[113]? = some (⟨236,(2),[5],[170,174],861⟩) from rfl))
private theorem rec12566 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 236 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(3),[1,2,5,6,13,14],[170],864⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[118]? = some (⟨236,(3),[1,2,5,6,13,14],[170],864⟩) from rfl))
private theorem rec12573 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(0),[1,2,5,6,13,14],[170],865⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[125]? = some (⟨237,(0),[1,2,5,6,13,14],[170],865⟩) from rfl))
private theorem rec12580 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(1),[1,2,5,6,13,14],[170],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[132]? = some (⟨237,(1),[1,2,5,6,13,14],[170],594⟩) from rfl))
private theorem rec12587 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(2),[1,2,5,6,13,14],[170],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[139]? = some (⟨237,(2),[1,2,5,6,13,14],[170],595⟩) from rfl))
private theorem rec12593 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(3),[1,2,5,6,13,14],[170],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[145]? = some (⟨237,(3),[1,2,5,6,13,14],[170],596⟩) from rfl))
private theorem rec12601 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(4),[1,2,5,6,13,14],[170],866⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[153]? = some (⟨237,(4),[1,2,5,6,13,14],[170],866⟩) from rfl))
private theorem rec12608 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(5),[1,2,5,6,13,14],[170],598⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[160]? = some (⟨237,(5),[1,2,5,6,13,14],[170],598⟩) from rfl))
private theorem rec12614 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(6),[1,2,5,6,13,14],[170],599⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[166]? = some (⟨237,(6),[1,2,5,6,13,14],[170],599⟩) from rfl))
private theorem rec12620 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(7),[1,2,5,6,13,14],[170],600⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[172]? = some (⟨237,(7),[1,2,5,6,13,14],[170],600⟩) from rfl))
private theorem rec12630 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 237 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(8),[5],[170,174],865⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[182]? = some (⟨237,(8),[5],[170,174],865⟩) from rfl))
private theorem rec12635 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(9),[1,2,5,6,13,14],[170],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[187]? = some (⟨237,(9),[1,2,5,6,13,14],[170],594⟩) from rfl))
private theorem rec12641 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(10),[1,2,5,6,13,14],[170],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[193]? = some (⟨237,(10),[1,2,5,6,13,14],[170],595⟩) from rfl))
private theorem rec12647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(11),[1,2,5,6,13,14],[170],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[199]? = some (⟨237,(11),[1,2,5,6,13,14],[170],596⟩) from rfl))
private theorem rec12653 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(12),[1,2,5,6,13,14],[170],868⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[205]? = some (⟨237,(12),[1,2,5,6,13,14],[170],868⟩) from rfl))
private theorem rec12660 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(13),[1,2,5,6,13,14],[170],602⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[212]? = some (⟨237,(13),[1,2,5,6,13,14],[170],602⟩) from rfl))
private theorem rec12666 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(14),[1,2,5,6,13,14],[170],603⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[218]? = some (⟨237,(14),[1,2,5,6,13,14],[170],603⟩) from rfl))
private theorem rec12672 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(15),[1,2,5,6,13,14],[170],604⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[224]? = some (⟨237,(15),[1,2,5,6,13,14],[170],604⟩) from rfl))
private theorem rec12678 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[230]? = some (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) from rfl))
private theorem rec12684 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[236]? = some (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) from rfl))
private theorem rec12690 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[242]? = some (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) from rfl))
private theorem rec12698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[250]? = some (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) from rfl))
private theorem rec12705 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[257]? = some (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) from rfl))
private theorem rec12711 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[263]? = some (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) from rfl))
private theorem rec12717 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(6),[1,2,5,6,13,14],[170],611⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[269]? = some (⟨238,(6),[1,2,5,6,13,14],[170],611⟩) from rfl))
private theorem rec12725 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(7),[1,2,5,6,13,14],[170],612⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[277]? = some (⟨238,(7),[1,2,5,6,13,14],[170],612⟩) from rfl))
private theorem rec12731 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(8),[1,2,5,6,13,14],[170],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[283]? = some (⟨238,(8),[1,2,5,6,13,14],[170],613⟩) from rfl))
private theorem rec12737 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(9),[1,2,5,6,13,14],[170],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[289]? = some (⟨238,(9),[1,2,5,6,13,14],[170],614⟩) from rfl))
private theorem rec12743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(10),[1,2,5,6,13,14],[170],615⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[295]? = some (⟨238,(10),[1,2,5,6,13,14],[170],615⟩) from rfl))
private theorem rec12751 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(11),[1,2,5,6,13,14],[170],616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[303]? = some (⟨238,(11),[1,2,5,6,13,14],[170],616⟩) from rfl))
private theorem rec12757 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(12),[1,2,5,6,13,14],[170],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[309]? = some (⟨238,(12),[1,2,5,6,13,14],[170],617⟩) from rfl))
private theorem rec12763 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(13),[1,2,5,6,13,14],[170],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[315]? = some (⟨238,(13),[1,2,5,6,13,14],[170],618⟩) from rfl))
private theorem rec12769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(14),[1,2,5,6,13,14],[170],619⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[321]? = some (⟨238,(14),[1,2,5,6,13,14],[170],619⟩) from rfl))
private theorem rec12777 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(15),[1,2,5,6,13,14],[170],620⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[329]? = some (⟨238,(15),[1,2,5,6,13,14],[170],620⟩) from rfl))
private theorem rec12783 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(0),[1,2,5,6],[170],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[335]? = some (⟨242,(0),[1,2,5,6],[170],632⟩) from rfl))
private theorem rec12787 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(1),[1,2,5,6],[170],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[339]? = some (⟨242,(1),[1,2,5,6],[170],872⟩) from rfl))
private theorem rec12791 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(2),[1,2,5,6],[170],873⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[343]? = some (⟨242,(2),[1,2,5,6],[170],873⟩) from rfl))
private theorem rec12795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(3),[1,2,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[347]? = some (⟨242,(3),[1,2,5,6],[170],101⟩) from rfl))
private theorem rec12799 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(4),[1,2,5,6],[170],873⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[351]? = some (⟨242,(4),[1,2,5,6],[170],873⟩) from rfl))
private theorem rec12803 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(5),[1,2,5,6],[170],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[355]? = some (⟨242,(5),[1,2,5,6],[170],632⟩) from rfl))
private theorem rec12807 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(6),[1,2,5,6],[170],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[359]? = some (⟨242,(6),[1,2,5,6],[170],872⟩) from rfl))
private theorem rec12811 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(7),[1,2,5,6],[170],874⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[363]? = some (⟨242,(7),[1,2,5,6],[170],874⟩) from rfl))
private theorem rec12815 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(8),[1,2,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[367]? = some (⟨242,(8),[1,2,5,6],[170],101⟩) from rfl))
private theorem rec12819 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(9),[1,2,5,6],[170],874⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[371]? = some (⟨242,(9),[1,2,5,6],[170],874⟩) from rfl))
private theorem rec12823 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(10),[1,2,5,6],[170],632⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[375]? = some (⟨242,(10),[1,2,5,6],[170],632⟩) from rfl))
private theorem rec12827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(11),[1,2,5,6],[170],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[379]? = some (⟨242,(11),[1,2,5,6],[170],872⟩) from rfl))
private theorem rec12831 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(12),[1,2,5,6],[170],875⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[383]? = some (⟨242,(12),[1,2,5,6],[170],875⟩) from rfl))
private theorem rec12835 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(13),[1,2,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[387]? = some (⟨242,(13),[1,2,5,6],[170],101⟩) from rfl))
private theorem rec12839 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(14),[1,2,5,6],[170],875⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[391]? = some (⟨242,(14),[1,2,5,6],[170],875⟩) from rfl))
private theorem rec12843 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(15),[1,2,5,6],[170],625⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[395]? = some (⟨242,(15),[1,2,5,6],[170],625⟩) from rfl))
private theorem rec12847 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(16),[1,2,5,6],[170],626⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[399]? = some (⟨242,(16),[1,2,5,6],[170],626⟩) from rfl))
private theorem rec12851 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(17),[1,2,5,6],[170],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[403]? = some (⟨242,(17),[1,2,5,6],[170],286⟩) from rfl))
private theorem rec12855 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(18),[1,2,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[407]? = some (⟨242,(18),[1,2,5,6],[170],101⟩) from rfl))
private theorem rec12859 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(19),[1,2,5,6],[170],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[411]? = some (⟨242,(19),[1,2,5,6],[170],286⟩) from rfl))
private theorem rec12863 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(20),[1,2,5,6],[170],876⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[415]? = some (⟨242,(20),[1,2,5,6],[170],876⟩) from rfl))
private theorem rec12867 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(21),[1,2,5,6],[170],877⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[419]? = some (⟨242,(21),[1,2,5,6],[170],877⟩) from rfl))
private theorem rec12871 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(22),[1,2,5,6],[170],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[423]? = some (⟨242,(22),[1,2,5,6],[170],287⟩) from rfl))
private theorem rec12875 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(23),[1,2,5,6],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[427]? = some (⟨242,(23),[1,2,5,6],[170],101⟩) from rfl))
private theorem rec12879 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 242 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨242,(24),[1,2,5,6],[170],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[431]? = some (⟨242,(24),[1,2,5,6],[170],287⟩) from rfl))
private theorem rec12883 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(5),[1,2,5,6,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[435]? = some (⟨243,(5),[1,2,5,6,14],[170],3⟩) from rfl))
private theorem rec12889 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[441]? = some (⟨243,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12895 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(8),[1,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[447]? = some (⟨243,(8),[1,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12904 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(9),[5,6,13,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[456]? = some (⟨243,(9),[5,6,13,14],[170],143⟩) from rfl))
private theorem rec12911 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(15),[5,13],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[463]? = some (⟨243,(15),[5,13],[170],48⟩) from rfl))
private theorem rec12913 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(16),[1,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[465]? = some (⟨243,(16),[1,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(17),[1,2,5,6,13,14],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[471]? = some (⟨243,(17),[1,2,5,6,13,14],[170],48⟩) from rfl))
private theorem rec12924 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(19),[2,5,6,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[476]? = some (⟨243,(19),[2,5,6,14],[170],143⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 69).take 22, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 170 gs.1 j := by
  have hp : ((section14State section14Catalog 5).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(214,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(215,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(216,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(241,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(242,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(244,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
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
      exact rec11138 5 170 (by decide) (by decide)
    · right
      exact rec11144 5 170 (by decide) (by decide)
    · right
      exact rec11150 5 170 (by decide) (by decide)
    · right
      exact rec11156 5 170 (by decide) (by decide)
    · right
      exact rec11162 5 170 (by decide) (by decide)
    · right
      exact rec11168 5 170 (by decide) (by decide)
    · right
      exact rec11176 5 170 (by decide) (by decide)
    · right
      exact rec11184 5 170 (by decide) (by decide)
    · right
      exact rec11192 5 170 (by decide) (by decide)
    · right
      exact rec11200 5 170 (by decide) (by decide)
    · right
      exact rec11208 5 170 (by decide) (by decide)
    · right
      exact rec11216 5 170 (by decide) (by decide)
    · right
      exact rec11224 5 170 (by decide) (by decide)
    · right
      exact rec11232 5 170 (by decide) (by decide)
    · right
      exact rec11240 5 170 (by decide) (by decide)
    · right
      exact rec11248 5 170 (by decide) (by decide)
    · right
      exact rec11256 5 170 (by decide) (by decide)
    · right
      exact rec11264 5 170 (by decide) (by decide)
    · right
      exact rec11272 5 170 (by decide) (by decide)
    · right
      exact rec11280 5 170 (by decide) (by decide)
    · right
      exact rec11288 5 170 (by decide) (by decide)
    · right
      exact rec11296 5 170 (by decide) (by decide)
    · right
      exact rec11304 5 170 (by decide) (by decide)
    · right
      exact rec11312 5 170 (by decide) (by decide)
    · right
      exact rec11320 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 225)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11328 5 170 (by decide) (by decide)
    · right
      exact rec11334 5 170 (by decide) (by decide)
    · right
      exact rec11340 5 170 (by decide) (by decide)
    · right
      exact rec11347 5 170 (by decide) (by decide)
    · right
      exact rec11354 5 170 (by decide) (by decide)
    · right
      exact rec11361 5 170 (by decide) (by decide)
    · right
      exact rec11367 5 170 (by decide) (by decide)
    · right
      exact rec11373 5 170 (by decide) (by decide)
    · right
      exact rec11381 5 170 (by decide) (by decide)
    · right
      exact rec11388 5 170 (by decide) (by decide)
    · right
      exact rec11396 5 170 (by decide) (by decide)
    · right
      exact rec11402 5 170 (by decide) (by decide)
    · right
      exact rec11408 5 170 (by decide) (by decide)
    · right
      exact rec11416 5 170 (by decide) (by decide)
    · right
      exact rec11423 5 170 (by decide) (by decide)
    · right
      exact rec11431 5 170 (by decide) (by decide)
    · right
      exact rec11437 5 170 (by decide) (by decide)
    · right
      exact rec11443 5 170 (by decide) (by decide)
    · right
      exact rec11451 5 170 (by decide) (by decide)
    · right
      exact rec11458 5 170 (by decide) (by decide)
    · right
      exact rec11466 5 170 (by decide) (by decide)
    · right
      exact rec11472 5 170 (by decide) (by decide)
    · right
      exact rec11478 5 170 (by decide) (by decide)
    · right
      exact rec11486 5 170 (by decide) (by decide)
    · right
      exact rec11493 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 226)).length = 10 := by decide +kernel
    have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11501 5 170 (by decide) (by decide)
    · right
      exact rec11508 5 170 (by decide) (by decide)
    · right
      exact rec11514 5 170 (by decide) (by decide)
    · right
      exact rec11520 5 170 (by decide) (by decide)
    · right
      exact rec11526 5 170 (by decide) (by decide)
    · right
      exact rec11532 5 170 (by decide) (by decide)
    · right
      exact rec11538 5 170 (by decide) (by decide)
    · right
      exact rec11544 5 170 (by decide) (by decide)
    · right
      exact rec11550 5 170 (by decide) (by decide)
    · right
      exact rec11556 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 227)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11562 5 170 (by decide) (by decide)
    · right
      exact rec11568 5 170 (by decide) (by decide)
    · right
      exact rec11574 5 170 (by decide) (by decide)
    · right
      exact rec11582 5 170 (by decide) (by decide)
    · right
      exact rec11588 5 170 (by decide) (by decide)
    · right
      exact rec11596 5 170 (by decide) (by decide)
    · right
      exact rec11602 5 170 (by decide) (by decide)
    · right
      exact rec11608 5 170 (by decide) (by decide)
    · right
      exact rec11616 5 170 (by decide) (by decide)
    · right
      exact rec11622 5 170 (by decide) (by decide)
    · right
      exact rec11630 5 170 (by decide) (by decide)
    · right
      exact rec11636 5 170 (by decide) (by decide)
    · right
      exact rec11642 5 170 (by decide) (by decide)
    · right
      exact rec11650 5 170 (by decide) (by decide)
    · right
      exact rec11656 5 170 (by decide) (by decide)
    · right
      exact rec11664 5 170 (by decide) (by decide)
    · right
      exact rec11670 5 170 (by decide) (by decide)
    · right
      exact rec11676 5 170 (by decide) (by decide)
    · right
      exact rec11684 5 170 (by decide) (by decide)
    · right
      exact rec11690 5 170 (by decide) (by decide)
    · right
      exact rec11698 5 170 (by decide) (by decide)
    · right
      exact rec11704 5 170 (by decide) (by decide)
    · right
      exact rec11710 5 170 (by decide) (by decide)
    · right
      exact rec11718 5 170 (by decide) (by decide)
    · right
      exact rec11724 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 228)).length = 25 := by decide +kernel
    have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec11732 5 170 (by decide) (by decide)
    · right
      exact rec11739 5 170 (by decide) (by decide)
    · right
      exact rec11746 5 170 (by decide) (by decide)
    · right
      exact rec11756 5 170 (by decide) (by decide)
    · right
      exact rec11763 5 170 (by decide) (by decide)
    · right
      exact rec11769 5 170 (by decide) (by decide)
    · right
      exact rec11775 5 170 (by decide) (by decide)
    · right
      exact rec11781 5 170 (by decide) (by decide)
    · right
      exact rec11787 5 170 (by decide) (by decide)
    · right
      exact rec11793 5 170 (by decide) (by decide)
    · right
      exact rec11800 5 170 (by decide) (by decide)
    · right
      exact rec11806 5 170 (by decide) (by decide)
    · right
      exact rec11812 5 170 (by decide) (by decide)
    · right
      exact rec11818 5 170 (by decide) (by decide)
    · right
      exact rec11824 5 170 (by decide) (by decide)
    · right
      exact rec11830 5 170 (by decide) (by decide)
    · right
      exact rec11836 5 170 (by decide) (by decide)
    · right
      exact rec11842 5 170 (by decide) (by decide)
    · right
      exact rec11848 5 170 (by decide) (by decide)
    · right
      exact rec11854 5 170 (by decide) (by decide)
    · right
      exact rec11860 5 170 (by decide) (by decide)
    · right
      exact rec11866 5 170 (by decide) (by decide)
    · right
      exact rec11872 5 170 (by decide) (by decide)
    · right
      exact rec11878 5 170 (by decide) (by decide)
    · right
      exact rec11884 5 170 (by decide) (by decide)
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
      exact rec11890 5 170 (by decide) (by decide)
    · right
      exact rec11896 5 170 (by decide) (by decide)
    · right
      exact rec11903 5 170 (by decide) (by decide)
    · right
      exact rec11909 5 170 (by decide) (by decide)
    · right
      exact rec11915 5 170 (by decide) (by decide)
    · right
      exact rec11921 5 170 (by decide) (by decide)
    · right
      exact rec11927 5 170 (by decide) (by decide)
    · right
      exact rec11934 5 170 (by decide) (by decide)
    · right
      exact rec11942 5 170 (by decide) (by decide)
    · right
      exact rec11953 5 170 (by decide) (by decide)
    · right
      exact rec11958 5 170 (by decide) (by decide)
    · right
      exact rec11964 5 170 (by decide) (by decide)
    · right
      exact rec11970 5 170 (by decide) (by decide)
    · right
      exact rec11978 5 170 (by decide) (by decide)
    · right
      exact rec11988 5 170 (by decide) (by decide)
    · right
      exact rec11993 5 170 (by decide) (by decide)
    · right
      exact rec11999 5 170 (by decide) (by decide)
    · right
      exact rec12005 5 170 (by decide) (by decide)
    · right
      exact rec12013 5 170 (by decide) (by decide)
    · right
      exact rec12019 5 170 (by decide) (by decide)
    · right
      exact rec12027 5 170 (by decide) (by decide)
    · right
      exact rec12033 5 170 (by decide) (by decide)
    · right
      exact rec12039 5 170 (by decide) (by decide)
    · right
      exact rec12047 5 170 (by decide) (by decide)
    · right
      exact rec12053 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 231)).length = 20 := by decide +kernel
    have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12061 5 170 (by decide) (by decide)
    · right
      exact rec12068 5 170 (by decide) (by decide)
    · right
      exact rec12076 5 170 (by decide) (by decide)
    · right
      exact rec12082 5 170 (by decide) (by decide)
    · right
      exact rec12088 5 170 (by decide) (by decide)
    · right
      exact rec12095 5 170 (by decide) (by decide)
    · right
      exact rec12103 5 170 (by decide) (by decide)
    · right
      exact rec12109 5 170 (by decide) (by decide)
    · right
      exact rec12115 5 170 (by decide) (by decide)
    · right
      exact rec12121 5 170 (by decide) (by decide)
    · right
      exact rec12127 5 170 (by decide) (by decide)
    · right
      exact rec12133 5 170 (by decide) (by decide)
    · right
      exact rec12139 5 170 (by decide) (by decide)
    · right
      exact rec12145 5 170 (by decide) (by decide)
    · right
      exact rec12151 5 170 (by decide) (by decide)
    · right
      exact rec12157 5 170 (by decide) (by decide)
    · right
      exact rec12163 5 170 (by decide) (by decide)
    · right
      exact rec12169 5 170 (by decide) (by decide)
    · right
      exact rec12175 5 170 (by decide) (by decide)
    · right
      exact rec12181 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 232)).length = 20 := by decide +kernel
    have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12187 5 170 (by decide) (by decide)
    · right
      exact rec12193 5 170 (by decide) (by decide)
    · right
      exact rec12199 5 170 (by decide) (by decide)
    · right
      exact rec12206 5 170 (by decide) (by decide)
    · right
      exact rec12212 5 170 (by decide) (by decide)
    · right
      exact rec12220 5 170 (by decide) (by decide)
    · right
      exact rec12226 5 170 (by decide) (by decide)
    · right
      exact rec12232 5 170 (by decide) (by decide)
    · right
      exact rec12239 5 170 (by decide) (by decide)
    · right
      exact rec12245 5 170 (by decide) (by decide)
    · right
      exact rec12253 5 170 (by decide) (by decide)
    · right
      exact rec12259 5 170 (by decide) (by decide)
    · right
      exact rec12265 5 170 (by decide) (by decide)
    · right
      exact rec12272 5 170 (by decide) (by decide)
    · right
      exact rec12278 5 170 (by decide) (by decide)
    · right
      exact rec12286 5 170 (by decide) (by decide)
    · right
      exact rec12292 5 170 (by decide) (by decide)
    · right
      exact rec12298 5 170 (by decide) (by decide)
    · right
      exact rec12305 5 170 (by decide) (by decide)
    · right
      exact rec12311 5 170 (by decide) (by decide)
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
      exact rec12319 5 170 (by decide) (by decide)
    · right
      exact rec12325 5 170 (by decide) (by decide)
    · right
      exact rec12333 5 170 (by decide) (by decide)
    · right
      exact rec12341 5 170 (by decide) (by decide)
    · right
      exact rec12349 5 170 (by decide) (by decide)
    · right
      exact rec12355 5 170 (by decide) (by decide)
    · right
      exact rec12363 5 170 (by decide) (by decide)
    · right
      exact rec12371 5 170 (by decide) (by decide)
    · right
      exact rec12379 5 170 (by decide) (by decide)
    · right
      exact rec12385 5 170 (by decide) (by decide)
    · right
      exact rec12393 5 170 (by decide) (by decide)
    · right
      exact rec12401 5 170 (by decide) (by decide)
    · right
      exact rec12409 5 170 (by decide) (by decide)
    · right
      exact rec12415 5 170 (by decide) (by decide)
    · right
      exact rec12423 5 170 (by decide) (by decide)
    · right
      exact rec12431 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 235)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12439 5 170 (by decide) (by decide)
    · right
      exact rec12445 5 170 (by decide) (by decide)
    · right
      exact rec12451 5 170 (by decide) (by decide)
    · right
      exact rec12459 5 170 (by decide) (by decide)
    · right
      exact rec12465 5 170 (by decide) (by decide)
    · right
      exact rec12471 5 170 (by decide) (by decide)
    · right
      exact rec12477 5 170 (by decide) (by decide)
    · right
      exact rec12485 5 170 (by decide) (by decide)
    · right
      exact rec12491 5 170 (by decide) (by decide)
    · right
      exact rec12497 5 170 (by decide) (by decide)
    · right
      exact rec12503 5 170 (by decide) (by decide)
    · right
      exact rec12511 5 170 (by decide) (by decide)
    · right
      exact rec12517 5 170 (by decide) (by decide)
    · right
      exact rec12523 5 170 (by decide) (by decide)
    · right
      exact rec12529 5 170 (by decide) (by decide)
    · right
      exact rec12537 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 236)).length = 4 := by decide +kernel
    have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12543 5 170 (by decide) (by decide)
    · right
      exact rec12550 5 170 (by decide) (by decide)
    · right
      exact rec12561 5 170 (by decide) (by decide)
    · right
      exact rec12566 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 237)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12573 5 170 (by decide) (by decide)
    · right
      exact rec12580 5 170 (by decide) (by decide)
    · right
      exact rec12587 5 170 (by decide) (by decide)
    · right
      exact rec12593 5 170 (by decide) (by decide)
    · right
      exact rec12601 5 170 (by decide) (by decide)
    · right
      exact rec12608 5 170 (by decide) (by decide)
    · right
      exact rec12614 5 170 (by decide) (by decide)
    · right
      exact rec12620 5 170 (by decide) (by decide)
    · right
      exact rec12630 5 170 (by decide) (by decide)
    · right
      exact rec12635 5 170 (by decide) (by decide)
    · right
      exact rec12641 5 170 (by decide) (by decide)
    · right
      exact rec12647 5 170 (by decide) (by decide)
    · right
      exact rec12653 5 170 (by decide) (by decide)
    · right
      exact rec12660 5 170 (by decide) (by decide)
    · right
      exact rec12666 5 170 (by decide) (by decide)
    · right
      exact rec12672 5 170 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 238)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12678 5 170 (by decide) (by decide)
    · right
      exact rec12684 5 170 (by decide) (by decide)
    · right
      exact rec12690 5 170 (by decide) (by decide)
    · right
      exact rec12698 5 170 (by decide) (by decide)
    · right
      exact rec12705 5 170 (by decide) (by decide)
    · right
      exact rec12711 5 170 (by decide) (by decide)
    · right
      exact rec12717 5 170 (by decide) (by decide)
    · right
      exact rec12725 5 170 (by decide) (by decide)
    · right
      exact rec12731 5 170 (by decide) (by decide)
    · right
      exact rec12737 5 170 (by decide) (by decide)
    · right
      exact rec12743 5 170 (by decide) (by decide)
    · right
      exact rec12751 5 170 (by decide) (by decide)
    · right
      exact rec12757 5 170 (by decide) (by decide)
    · right
      exact rec12763 5 170 (by decide) (by decide)
    · right
      exact rec12769 5 170 (by decide) (by decide)
    · right
      exact rec12777 5 170 (by decide) (by decide)
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
      exact rec12783 5 170 (by decide) (by decide)
    · right
      exact rec12787 5 170 (by decide) (by decide)
    · right
      exact rec12791 5 170 (by decide) (by decide)
    · right
      exact rec12795 5 170 (by decide) (by decide)
    · right
      exact rec12799 5 170 (by decide) (by decide)
    · right
      exact rec12803 5 170 (by decide) (by decide)
    · right
      exact rec12807 5 170 (by decide) (by decide)
    · right
      exact rec12811 5 170 (by decide) (by decide)
    · right
      exact rec12815 5 170 (by decide) (by decide)
    · right
      exact rec12819 5 170 (by decide) (by decide)
    · right
      exact rec12823 5 170 (by decide) (by decide)
    · right
      exact rec12827 5 170 (by decide) (by decide)
    · right
      exact rec12831 5 170 (by decide) (by decide)
    · right
      exact rec12835 5 170 (by decide) (by decide)
    · right
      exact rec12839 5 170 (by decide) (by decide)
    · right
      exact rec12843 5 170 (by decide) (by decide)
    · right
      exact rec12847 5 170 (by decide) (by decide)
    · right
      exact rec12851 5 170 (by decide) (by decide)
    · right
      exact rec12855 5 170 (by decide) (by decide)
    · right
      exact rec12859 5 170 (by decide) (by decide)
    · right
      exact rec12863 5 170 (by decide) (by decide)
    · right
      exact rec12867 5 170 (by decide) (by decide)
    · right
      exact rec12871 5 170 (by decide) (by decide)
    · right
      exact rec12875 5 170 (by decide) (by decide)
    · right
      exact rec12879 5 170 (by decide) (by decide)
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
      exact rec12883 5 170 (by decide) (by decide)
    · left
      decide +kernel
    · right
      exact rec12889 5 170 (by decide) (by decide)
    · right
      exact rec12895 5 170 (by decide) (by decide)
    · right
      exact rec12904 5 170 (by decide) (by decide)
    · left
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
      exact rec12911 5 170 (by decide) (by decide)
    · right
      exact rec12913 5 170 (by decide) (by decide)
    · right
      exact rec12919 5 170 (by decide) (by decide)
    · left
      decide +kernel
    · right
      exact rec12924 5 170 (by decide) (by decide)
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
end Section14CoverageSpec_5_5_p170_69_91

#print axioms solution
