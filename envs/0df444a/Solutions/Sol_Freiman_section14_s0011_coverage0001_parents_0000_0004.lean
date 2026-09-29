-- Prove2me | solution 1 for Freiman.section14_s0011_coverage0001_parents_0000_0004
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T11:33:52.355924+00:00
-- url     : https://prove2.me/submissions/41e560e1-43c2-454b-a6ac-fe37b219b21c

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
namespace Section14Coverage_11_1_p0_4
private theorem rec416 (si parent : ℕ) (hs : si ∈ ([3, 7, 11, 15] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[3,7,11,15],[0],914⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[416]? = some (⟨16,(-1),[3,7,11,15],[0],914⟩) from rfl))
private theorem rec488 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[11],[1],66⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[488]? = some (⟨16,(-1),[11],[1],66⟩) from rfl))
private theorem rec489 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([3] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[11],[3],242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[489]? = some (⟨16,(-1),[11],[3],242⟩) from rfl))
private theorem rec1387 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[11],[2],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[218]? = some (⟨25,(0),[11],[2],189⟩) from rfl))
private theorem rec1411 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[11],[2],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[242]? = some (⟨25,(1),[11],[2],216⟩) from rfl))
private theorem rec1435 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[11],[2],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[266]? = some (⟨25,(2),[11],[2],217⟩) from rfl))
private theorem rec1459 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[11],[2],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[290]? = some (⟨25,(3),[11],[2],218⟩) from rfl))
private theorem rec1483 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[11],[2],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[314]? = some (⟨25,(4),[11],[2],219⟩) from rfl))
private theorem rec1504 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[11],[2],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[335]? = some (⟨25,(5),[11],[2],189⟩) from rfl))
private theorem rec1528 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[11],[2],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[359]? = some (⟨25,(6),[11],[2],216⟩) from rfl))
private theorem rec1552 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[11],[2],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[383]? = some (⟨25,(7),[11],[2],217⟩) from rfl))
private theorem rec1576 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[11],[2],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[407]? = some (⟨25,(8),[11],[2],218⟩) from rfl))
private theorem rec1600 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[11],[2],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[431]? = some (⟨25,(9),[11],[2],219⟩) from rfl))
private theorem rec1621 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[11],[2],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[452]? = some (⟨25,(10),[11],[2],194⟩) from rfl))
private theorem rec1645 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[11],[2],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[476]? = some (⟨25,(11),[11],[2],220⟩) from rfl))
private theorem rec1669 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[11],[2],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[500]? = some (⟨25,(12),[11],[2],220⟩) from rfl))
private theorem rec1693 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[11],[2],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[524]? = some (⟨25,(13),[11],[2],220⟩) from rfl))
private theorem rec1717 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[11],[2],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[548]? = some (⟨25,(14),[11],[2],219⟩) from rfl))
private theorem rec1738 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[11],[2],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[569]? = some (⟨25,(15),[11],[2],196⟩) from rfl))
private theorem rec1762 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[11],[2],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[593]? = some (⟨25,(16),[11],[2],221⟩) from rfl))
private theorem rec1786 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[11],[2],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[617]? = some (⟨25,(17),[11],[2],221⟩) from rfl))
private theorem rec1810 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[11],[2],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[641]? = some (⟨25,(18),[11],[2],221⟩) from rfl))
private theorem rec1834 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[11],[2],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[665]? = some (⟨25,(19),[11],[2],221⟩) from rfl))
private theorem rec1855 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[11],[2],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[686]? = some (⟨25,(20),[11],[2],198⟩) from rfl))
private theorem rec1879 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[11],[2],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[710]? = some (⟨25,(21),[11],[2],222⟩) from rfl))
private theorem rec1903 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[11],[2],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[734]? = some (⟨25,(22),[11],[2],222⟩) from rfl))
private theorem rec1927 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[11],[2],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[758]? = some (⟨25,(23),[11],[2],222⟩) from rfl))
private theorem rec1951 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[11],[2],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[782]? = some (⟨25,(24),[11],[2],222⟩) from rfl))
private theorem rec2368 (si parent : ℕ) (hs : si ∈ ([11, 12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[11,12],[2],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1199]? = some (⟨30,(0),[11,12],[2],152⟩) from rfl))
private theorem rec2383 (si parent : ℕ) (hs : si ∈ ([11, 12] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[11,12],[2],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1214]? = some (⟨30,(1),[11,12],[2],153⟩) from rfl))
private theorem rec2402 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[11],[2],200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1233]? = some (⟨30,(2),[11],[2],200⟩) from rfl))
private theorem rec2426 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[11],[2],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1257]? = some (⟨30,(3),[11],[2],230⟩) from rfl))
private theorem rec2450 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[11],[2],231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[7]? = some (⟨30,(4),[11],[2],231⟩) from rfl))
private theorem rec2474 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[11],[2],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[31]? = some (⟨30,(5),[11],[2],230⟩) from rfl))
private theorem rec2498 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[11],[2],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[55]? = some (⟨30,(6),[11],[2],232⟩) from rfl))
private theorem rec2522 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[11],[2],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[79]? = some (⟨30,(7),[11],[2],232⟩) from rfl))
private theorem rec2546 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[11],[2],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[103]? = some (⟨30,(8),[11],[2],233⟩) from rfl))
private theorem rec2570 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[11],[2],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[127]? = some (⟨30,(9),[11],[2],233⟩) from rfl))
private theorem rec14718 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(0),[11],[2],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1115]? = some (⟨335,(0),[11],[2],106⟩) from rfl))
private theorem rec14722 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(1),[11],[2],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1119]? = some (⟨335,(1),[11],[2],106⟩) from rfl))
private theorem rec14726 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(2),[11],[2],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1123]? = some (⟨335,(2),[11],[2],107⟩) from rfl))
private theorem rec14730 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(3),[11],[2],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1127]? = some (⟨335,(3),[11],[2],107⟩) from rfl))
private theorem rec14734 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(4),[11],[2],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1131]? = some (⟨335,(4),[11],[2],108⟩) from rfl))
private theorem rec14738 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(5),[11],[2],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1135]? = some (⟨335,(5),[11],[2],110⟩) from rfl))
private theorem rec14742 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(6),[11],[2],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1139]? = some (⟨335,(6),[11],[2],108⟩) from rfl))
private theorem rec14746 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(7),[11],[2],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1143]? = some (⟨335,(7),[11],[2],112⟩) from rfl))
private theorem rec14750 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(8),[11],[2],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1147]? = some (⟨335,(8),[11],[2],108⟩) from rfl))
private theorem rec14754 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 335 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨335,(9),[11],[2],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1151]? = some (⟨335,(9),[11],[2],110⟩) from rfl))
private theorem rec14757 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(0),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1154]? = some (⟨339,(0),[11],[2],2⟩) from rfl))
private theorem rec14760 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(1),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1157]? = some (⟨339,(1),[11],[2],2⟩) from rfl))
private theorem rec14763 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(2),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1160]? = some (⟨339,(2),[11],[2],2⟩) from rfl))
private theorem rec14766 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(3),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1163]? = some (⟨339,(3),[11],[2],2⟩) from rfl))
private theorem rec14769 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(4),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1166]? = some (⟨339,(4),[11],[2],2⟩) from rfl))
private theorem rec14772 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(5),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1169]? = some (⟨339,(5),[11],[2],2⟩) from rfl))
private theorem rec14775 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(6),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1172]? = some (⟨339,(6),[11],[2],2⟩) from rfl))
private theorem rec14778 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(7),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1175]? = some (⟨339,(7),[11],[2],2⟩) from rfl))
private theorem rec14781 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(8),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1178]? = some (⟨339,(8),[11],[2],2⟩) from rfl))
private theorem rec14784 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 339 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨339,(9),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1181]? = some (⟨339,(9),[11],[2],2⟩) from rfl))
private theorem rec14788 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(0),[11],[2],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1185]? = some (⟨343,(0),[11],[2],113⟩) from rfl))
private theorem rec14792 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(1),[11],[2],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1189]? = some (⟨343,(1),[11],[2],113⟩) from rfl))
private theorem rec14796 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(2),[11],[2],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1193]? = some (⟨343,(2),[11],[2],114⟩) from rfl))
private theorem rec14800 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(3),[11],[2],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1197]? = some (⟨343,(3),[11],[2],114⟩) from rfl))
private theorem rec14804 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(4),[11],[2],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1201]? = some (⟨343,(4),[11],[2],115⟩) from rfl))
private theorem rec14808 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(5),[11],[2],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1205]? = some (⟨343,(5),[11],[2],117⟩) from rfl))
private theorem rec14812 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(6),[11],[2],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1209]? = some (⟨343,(6),[11],[2],115⟩) from rfl))
private theorem rec14816 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(7),[11],[2],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1213]? = some (⟨343,(7),[11],[2],119⟩) from rfl))
private theorem rec14820 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(8),[11],[2],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1217]? = some (⟨343,(8),[11],[2],115⟩) from rfl))
private theorem rec14824 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 343 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨343,(9),[11],[2],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1221]? = some (⟨343,(9),[11],[2],117⟩) from rfl))
private theorem rec14827 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 347 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(0),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1224]? = some (⟨347,(0),[11],[2],2⟩) from rfl))
private theorem rec14830 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 347 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(1),[11],[2],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1227]? = some (⟨347,(1),[11],[2],2⟩) from rfl))
private theorem rec14833 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 347 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(2),[11],[2],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1230]? = some (⟨347,(2),[11],[2],159⟩) from rfl))
private theorem rec14836 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 347 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨347,(3),[11],[2],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1233]? = some (⟨347,(3),[11],[2],99⟩) from rfl))
private theorem rec14840 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 349 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(0),[11],[2],121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1237]? = some (⟨349,(0),[11],[2],121⟩) from rfl))
private theorem rec14844 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 349 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(1),[11],[2],122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1241]? = some (⟨349,(1),[11],[2],122⟩) from rfl))
private theorem rec14848 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 349 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(2),[11],[2],931⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1245]? = some (⟨349,(2),[11],[2],931⟩) from rfl))
private theorem rec14852 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 349 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨349,(3),[11],[2],124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part13 (List.mem_of_getElem? (show section14DataRecords4Part2[1249]? = some (⟨349,(3),[11],[2],124⟩) from rfl))
private theorem rec16265 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(0),[11],[2],1688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[57]? = some (⟨547,(0),[11],[2],1688⟩) from rfl))
private theorem rec16268 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(1),[11],[2],1689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[60]? = some (⟨547,(1),[11],[2],1689⟩) from rfl))
private theorem rec16271 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(2),[11],[2],1688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[63]? = some (⟨547,(2),[11],[2],1688⟩) from rfl))
private theorem rec16274 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(3),[11],[2],1690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[66]? = some (⟨547,(3),[11],[2],1690⟩) from rfl))
private theorem rec16277 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(4),[11],[2],212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[69]? = some (⟨547,(4),[11],[2],212⟩) from rfl))
private theorem rec16280 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(5),[11],[2],1688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[72]? = some (⟨547,(5),[11],[2],1688⟩) from rfl))
private theorem rec16283 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(6),[11],[2],1689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[75]? = some (⟨547,(6),[11],[2],1689⟩) from rfl))
private theorem rec16286 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(7),[11],[2],1688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[78]? = some (⟨547,(7),[11],[2],1688⟩) from rfl))
private theorem rec16289 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(8),[11],[2],1690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[81]? = some (⟨547,(8),[11],[2],1690⟩) from rfl))
private theorem rec16292 (si parent : ℕ) (hs : si ∈ ([11] : List ℕ)) (hp : parent ∈ ([2] : List ℕ)) : section14Recorded section14Catalog si parent 547 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨547,(9),[11],[2],212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[84]? = some (⟨547,(9),[11],[2],212⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 11).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 11)).drop 0).take 4, section14Recorded section14Catalog 11 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 11 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 11).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(592,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(593,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(342,⟨([3],[]),true,([3],[]),false,false,[]⟩),(343,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(344,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(345,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(594,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(348,⟨([2],[]),true,([3],[]),false,false,[]⟩),(349,⟨([3],[]),true,([2],[]),false,false,[]⟩),(550,⟨([1],[]),true,([],[]),true,false,[]⟩),(350,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 11)).drop 0).take 4 = [⟨5,0,[⟨true,false,12⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨5,1,[⟨true,false,16⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨5,2,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨5,3,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · left
    exact rec416 11 0 (by decide) (by decide)
  · left
    exact rec488 11 1 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(592,⟨([1],[]),true,([1],[]),false,false,[]⟩),(335,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(336,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(593,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(338,⟨([2],[]),true,([2],[]),false,false,[]⟩),(339,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(340,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(341,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(342,⟨([3],[]),true,([3],[]),false,false,[]⟩),(343,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(344,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(345,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(594,⟨([1],[]),true,([2],[]),false,false,[]⟩),(347,⟨([2],[]),true,([1],[]),false,false,[]⟩),(348,⟨([2],[]),true,([3],[]),false,false,[]⟩),(349,⟨([3],[]),true,([2],[]),false,false,[]⟩),(550,⟨([1],[]),true,([],[]),true,false,[]⟩),(350,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 592)).length = 1 := by decide +kernel
      have hjj : j < 1 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 335)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14718 11 2 (by decide) (by decide)
      · right
        exact rec14722 11 2 (by decide) (by decide)
      · right
        exact rec14726 11 2 (by decide) (by decide)
      · right
        exact rec14730 11 2 (by decide) (by decide)
      · right
        exact rec14734 11 2 (by decide) (by decide)
      · right
        exact rec14738 11 2 (by decide) (by decide)
      · right
        exact rec14742 11 2 (by decide) (by decide)
      · right
        exact rec14746 11 2 (by decide) (by decide)
      · right
        exact rec14750 11 2 (by decide) (by decide)
      · right
        exact rec14754 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 336)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 547)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16265 11 2 (by decide) (by decide)
      · right
        exact rec16268 11 2 (by decide) (by decide)
      · right
        exact rec16271 11 2 (by decide) (by decide)
      · right
        exact rec16274 11 2 (by decide) (by decide)
      · right
        exact rec16277 11 2 (by decide) (by decide)
      · right
        exact rec16280 11 2 (by decide) (by decide)
      · right
        exact rec16283 11 2 (by decide) (by decide)
      · right
        exact rec16286 11 2 (by decide) (by decide)
      · right
        exact rec16289 11 2 (by decide) (by decide)
      · right
        exact rec16292 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 593)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 338)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 339)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14757 11 2 (by decide) (by decide)
      · right
        exact rec14760 11 2 (by decide) (by decide)
      · right
        exact rec14763 11 2 (by decide) (by decide)
      · right
        exact rec14766 11 2 (by decide) (by decide)
      · right
        exact rec14769 11 2 (by decide) (by decide)
      · right
        exact rec14772 11 2 (by decide) (by decide)
      · right
        exact rec14775 11 2 (by decide) (by decide)
      · right
        exact rec14778 11 2 (by decide) (by decide)
      · right
        exact rec14781 11 2 (by decide) (by decide)
      · right
        exact rec14784 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 340)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1387 11 2 (by decide) (by decide)
      · right
        exact rec1411 11 2 (by decide) (by decide)
      · right
        exact rec1435 11 2 (by decide) (by decide)
      · right
        exact rec1459 11 2 (by decide) (by decide)
      · right
        exact rec1483 11 2 (by decide) (by decide)
      · right
        exact rec1504 11 2 (by decide) (by decide)
      · right
        exact rec1528 11 2 (by decide) (by decide)
      · right
        exact rec1552 11 2 (by decide) (by decide)
      · right
        exact rec1576 11 2 (by decide) (by decide)
      · right
        exact rec1600 11 2 (by decide) (by decide)
      · right
        exact rec1621 11 2 (by decide) (by decide)
      · right
        exact rec1645 11 2 (by decide) (by decide)
      · right
        exact rec1669 11 2 (by decide) (by decide)
      · right
        exact rec1693 11 2 (by decide) (by decide)
      · right
        exact rec1717 11 2 (by decide) (by decide)
      · right
        exact rec1738 11 2 (by decide) (by decide)
      · right
        exact rec1762 11 2 (by decide) (by decide)
      · right
        exact rec1786 11 2 (by decide) (by decide)
      · right
        exact rec1810 11 2 (by decide) (by decide)
      · right
        exact rec1834 11 2 (by decide) (by decide)
      · right
        exact rec1855 11 2 (by decide) (by decide)
      · right
        exact rec1879 11 2 (by decide) (by decide)
      · right
        exact rec1903 11 2 (by decide) (by decide)
      · right
        exact rec1927 11 2 (by decide) (by decide)
      · right
        exact rec1951 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 341)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 342)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 343)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14788 11 2 (by decide) (by decide)
      · right
        exact rec14792 11 2 (by decide) (by decide)
      · right
        exact rec14796 11 2 (by decide) (by decide)
      · right
        exact rec14800 11 2 (by decide) (by decide)
      · right
        exact rec14804 11 2 (by decide) (by decide)
      · right
        exact rec14808 11 2 (by decide) (by decide)
      · right
        exact rec14812 11 2 (by decide) (by decide)
      · right
        exact rec14816 11 2 (by decide) (by decide)
      · right
        exact rec14820 11 2 (by decide) (by decide)
      · right
        exact rec14824 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 344)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 30)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2368 11 2 (by decide) (by decide)
      · right
        exact rec2383 11 2 (by decide) (by decide)
      · right
        exact rec2402 11 2 (by decide) (by decide)
      · right
        exact rec2426 11 2 (by decide) (by decide)
      · right
        exact rec2450 11 2 (by decide) (by decide)
      · right
        exact rec2474 11 2 (by decide) (by decide)
      · right
        exact rec2498 11 2 (by decide) (by decide)
      · right
        exact rec2522 11 2 (by decide) (by decide)
      · right
        exact rec2546 11 2 (by decide) (by decide)
      · right
        exact rec2570 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 345)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 594)).length = 1 := by decide +kernel
      have hjj : j < 1 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 347)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14827 11 2 (by decide) (by decide)
      · right
        exact rec14830 11 2 (by decide) (by decide)
      · right
        exact rec14833 11 2 (by decide) (by decide)
      · right
        exact rec14836 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 348)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 349)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec14840 11 2 (by decide) (by decide)
      · right
        exact rec14844 11 2 (by decide) (by decide)
      · right
        exact rec14848 11 2 (by decide) (by decide)
      · right
        exact rec14852 11 2 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 550)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 350)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec489 11 3 (by decide) (by decide)
end Section14Coverage_11_1_p0_4

#print axioms solution
