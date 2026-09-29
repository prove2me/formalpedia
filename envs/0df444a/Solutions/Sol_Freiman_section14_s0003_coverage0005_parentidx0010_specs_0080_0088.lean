-- Prove2me | solution 1 for Freiman.section14_s0003_coverage0005_parentidx0010_specs_0080_0088
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:40:13.391098+00:00
-- url     : https://prove2.me/submissions/2d571c36-b365-40d9-904f-86bcef59a49c

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
namespace Section14CoverageSpec_3_5_p10_80_88
private theorem rec12320 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(0),[3,4,7,8,12,15,16],[10],568⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[391]? = some (⟨234,(0),[3,4,7,8,12,15,16],[10],568⟩) from rfl))
private theorem rec12327 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(1),[3,7,15],[10],569⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[398]? = some (⟨234,(1),[3,7,15],[10],569⟩) from rfl))
private theorem rec12335 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(2),[3,7,15],[10],570⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[406]? = some (⟨234,(2),[3,7,15],[10],570⟩) from rfl))
private theorem rec12343 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(3),[3,7,15],[10],571⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[414]? = some (⟨234,(3),[3,7,15],[10],571⟩) from rfl))
private theorem rec12350 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(4),[3,4,7,8,12,15,16],[10],572⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[421]? = some (⟨234,(4),[3,4,7,8,12,15,16],[10],572⟩) from rfl))
private theorem rec12357 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(5),[3,7,15],[10],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[428]? = some (⟨234,(5),[3,7,15],[10],573⟩) from rfl))
private theorem rec12365 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(6),[3,7,15],[10],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[436]? = some (⟨234,(6),[3,7,15],[10],573⟩) from rfl))
private theorem rec12373 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(7),[3,7,15],[10],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[444]? = some (⟨234,(7),[3,7,15],[10],573⟩) from rfl))
private theorem rec12380 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(8),[3,4,7,8,12,15,16],[10],574⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[451]? = some (⟨234,(8),[3,4,7,8,12,15,16],[10],574⟩) from rfl))
private theorem rec12387 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(9),[3,7,15],[10],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[458]? = some (⟨234,(9),[3,7,15],[10],575⟩) from rfl))
private theorem rec12395 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(10),[3,7,15],[10],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[466]? = some (⟨234,(10),[3,7,15],[10],575⟩) from rfl))
private theorem rec12403 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(11),[3,7,15],[10],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[474]? = some (⟨234,(11),[3,7,15],[10],575⟩) from rfl))
private theorem rec12410 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(12),[3,4,7,8,12,15,16],[10],576⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[481]? = some (⟨234,(12),[3,4,7,8,12,15,16],[10],576⟩) from rfl))
private theorem rec12417 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(13),[3,7,15],[10],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[488]? = some (⟨234,(13),[3,7,15],[10],577⟩) from rfl))
private theorem rec12425 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(14),[3,7,15],[10],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[496]? = some (⟨234,(14),[3,7,15],[10],577⟩) from rfl))
private theorem rec12433 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 234 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(15),[3,7,15],[10],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[504]? = some (⟨234,(15),[3,7,15],[10],577⟩) from rfl))
private theorem rec12440 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(0),[3,4,7,8,12,15,16],[10],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[511]? = some (⟨235,(0),[3,4,7,8,12,15,16],[10],578⟩) from rfl))
private theorem rec12446 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(1),[3,4,7,8,12,15,16],[10],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[517]? = some (⟨235,(1),[3,4,7,8,12,15,16],[10],579⟩) from rfl))
private theorem rec12453 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(2),[3,7,15],[10],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[5]? = some (⟨235,(2),[3,7,15],[10],580⟩) from rfl))
private theorem rec12460 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(3),[3,4,7,8,12,15,16],[10],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[12]? = some (⟨235,(3),[3,4,7,8,12,15,16],[10],581⟩) from rfl))
private theorem rec12466 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(4),[3,4,7,8,12,15,16],[10],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[18]? = some (⟨235,(4),[3,4,7,8,12,15,16],[10],582⟩) from rfl))
private theorem rec12472 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(5),[3,4,7,8,12,15,16],[10],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[24]? = some (⟨235,(5),[3,4,7,8,12,15,16],[10],583⟩) from rfl))
private theorem rec12479 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(6),[3,7,15],[10],584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[31]? = some (⟨235,(6),[3,7,15],[10],584⟩) from rfl))
private theorem rec12486 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(7),[3,4,7,8,12,15,16],[10],585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[38]? = some (⟨235,(7),[3,4,7,8,12,15,16],[10],585⟩) from rfl))
private theorem rec12492 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(8),[3,4,7,8,12,15,16],[10],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[44]? = some (⟨235,(8),[3,4,7,8,12,15,16],[10],578⟩) from rfl))
private theorem rec12498 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(9),[3,4,7,8,12,15,16],[10],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[50]? = some (⟨235,(9),[3,4,7,8,12,15,16],[10],579⟩) from rfl))
private theorem rec12505 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(10),[3,7,15],[10],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[57]? = some (⟨235,(10),[3,7,15],[10],580⟩) from rfl))
private theorem rec12512 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(11),[3,4,7,8,12,15,16],[10],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[64]? = some (⟨235,(11),[3,4,7,8,12,15,16],[10],581⟩) from rfl))
private theorem rec12518 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(12),[3,4,7,8,12,15,16],[10],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[70]? = some (⟨235,(12),[3,4,7,8,12,15,16],[10],586⟩) from rfl))
private theorem rec12524 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(13),[3,4,7,8,12,15,16],[10],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[76]? = some (⟨235,(13),[3,4,7,8,12,15,16],[10],587⟩) from rfl))
private theorem rec12531 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(14),[3,7,15],[10],588⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[83]? = some (⟨235,(14),[3,7,15],[10],588⟩) from rfl))
private theorem rec12538 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 235 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(15),[3,4,7,8,12,15,16],[10],589⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[90]? = some (⟨235,(15),[3,4,7,8,12,15,16],[10],589⟩) from rfl))
private theorem rec12544 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 236 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(0),[3,4,8,12,15,16],[10],861⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[96]? = some (⟨236,(0),[3,4,8,12,15,16],[10],861⟩) from rfl))
private theorem rec12551 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 236 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(1),[3,4,8,12,15,16],[10],862⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[103]? = some (⟨236,(1),[3,4,8,12,15,16],[10],862⟩) from rfl))
private theorem rec12559 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 236 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(2),[3,7,15],[10],863⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[111]? = some (⟨236,(2),[3,7,15],[10],863⟩) from rfl))
private theorem rec12567 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 236 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(3),[3,4,8,12,15,16],[10],864⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[119]? = some (⟨236,(3),[3,4,8,12,15,16],[10],864⟩) from rfl))
private theorem rec12574 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(0),[3,4,8,12,15,16],[10],865⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[126]? = some (⟨237,(0),[3,4,8,12,15,16],[10],865⟩) from rfl))
private theorem rec12581 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(1),[3,4,7,8,15,16],[10],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[133]? = some (⟨237,(1),[3,4,7,8,15,16],[10],594⟩) from rfl))
private theorem rec12588 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(2),[3,4,7,8,12,15,16],[10],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[140]? = some (⟨237,(2),[3,4,7,8,12,15,16],[10],595⟩) from rfl))
private theorem rec12595 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(3),[3,7,15],[10],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[147]? = some (⟨237,(3),[3,7,15],[10],596⟩) from rfl))
private theorem rec12602 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(4),[3,4,8,12,15,16],[10],866⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[154]? = some (⟨237,(4),[3,4,8,12,15,16],[10],866⟩) from rfl))
private theorem rec12609 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(5),[3,4,7,8,12,15,16],[10],598⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[161]? = some (⟨237,(5),[3,4,7,8,12,15,16],[10],598⟩) from rfl))
private theorem rec12615 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(6),[3,4,7,8,12,15,16],[10],599⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[167]? = some (⟨237,(6),[3,4,7,8,12,15,16],[10],599⟩) from rfl))
private theorem rec12621 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(7),[3,4,7,8,12,15,16],[10],600⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[173]? = some (⟨237,(7),[3,4,7,8,12,15,16],[10],600⟩) from rfl))
private theorem rec12628 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(8),[3,7,15],[10],867⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[180]? = some (⟨237,(8),[3,7,15],[10],867⟩) from rfl))
private theorem rec12636 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(9),[3,4,7,8,12,15,16],[10],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[188]? = some (⟨237,(9),[3,4,7,8,12,15,16],[10],594⟩) from rfl))
private theorem rec12642 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(10),[3,4,7,8,12,15,16],[10],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[194]? = some (⟨237,(10),[3,4,7,8,12,15,16],[10],595⟩) from rfl))
private theorem rec12648 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(11),[3,4,7,8,12,15,16],[10],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[200]? = some (⟨237,(11),[3,4,7,8,12,15,16],[10],596⟩) from rfl))
private theorem rec12654 (si parent : ℕ) (hs : si ∈ ([3, 4, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(12),[3,4,8,12,15,16],[10],868⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[206]? = some (⟨237,(12),[3,4,8,12,15,16],[10],868⟩) from rfl))
private theorem rec12661 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(13),[3,4,7,8,12,15,16],[10],602⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[213]? = some (⟨237,(13),[3,4,7,8,12,15,16],[10],602⟩) from rfl))
private theorem rec12667 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(14),[3,4,7,8,12,15,16],[10],603⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[219]? = some (⟨237,(14),[3,4,7,8,12,15,16],[10],603⟩) from rfl))
private theorem rec12673 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 237 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(15),[3,4,7,8,12,15,16],[10],604⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[225]? = some (⟨237,(15),[3,4,7,8,12,15,16],[10],604⟩) from rfl))
private theorem rec12679 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(0),[3,4,7,8,12,15,16],[10],869⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[231]? = some (⟨238,(0),[3,4,7,8,12,15,16],[10],869⟩) from rfl))
private theorem rec12685 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(1),[3,4,7,8,12,15,16],[10],870⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[237]? = some (⟨238,(1),[3,4,7,8,12,15,16],[10],870⟩) from rfl))
private theorem rec12692 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(2),[3,7,15],[10],607⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[244]? = some (⟨238,(2),[3,7,15],[10],607⟩) from rfl))
private theorem rec12700 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(3),[3,4,7,8,12,15,16],[10],871⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[252]? = some (⟨238,(3),[3,4,7,8,12,15,16],[10],871⟩) from rfl))
private theorem rec12706 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(4),[3,4,7,8,12,15,16],[10],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[258]? = some (⟨238,(4),[3,4,7,8,12,15,16],[10],609⟩) from rfl))
private theorem rec12712 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(5),[3,4,7,8,12,15,16],[10],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[264]? = some (⟨238,(5),[3,4,7,8,12,15,16],[10],610⟩) from rfl))
private theorem rec12719 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(6),[3,7,15],[10],611⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[271]? = some (⟨238,(6),[3,7,15],[10],611⟩) from rfl))
private theorem rec12726 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(7),[3,4,7,8,12,15,16],[10],612⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[278]? = some (⟨238,(7),[3,4,7,8,12,15,16],[10],612⟩) from rfl))
private theorem rec12732 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(8),[3,4,7,8,12,15,16],[10],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[284]? = some (⟨238,(8),[3,4,7,8,12,15,16],[10],613⟩) from rfl))
private theorem rec12738 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(9),[3,4,7,8,12,15,16],[10],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[290]? = some (⟨238,(9),[3,4,7,8,12,15,16],[10],614⟩) from rfl))
private theorem rec12745 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(10),[3,7,15],[10],615⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[297]? = some (⟨238,(10),[3,7,15],[10],615⟩) from rfl))
private theorem rec12752 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(11),[3,4,7,8,12,15,16],[10],616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[304]? = some (⟨238,(11),[3,4,7,8,12,15,16],[10],616⟩) from rfl))
private theorem rec12758 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(12),[3,4,7,8,12,15,16],[10],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[310]? = some (⟨238,(12),[3,4,7,8,12,15,16],[10],617⟩) from rfl))
private theorem rec12764 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(13),[3,4,7,8,12,15,16],[10],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[316]? = some (⟨238,(13),[3,4,7,8,12,15,16],[10],618⟩) from rfl))
private theorem rec12771 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(14),[3,7,15],[10],619⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[323]? = some (⟨238,(14),[3,7,15],[10],619⟩) from rfl))
private theorem rec12778 (si parent : ℕ) (hs : si ∈ ([3, 4, 7, 8, 12, 15, 16] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 238 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(15),[3,4,7,8,12,15,16],[10],620⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[330]? = some (⟨238,(15),[3,4,7,8,12,15,16],[10],620⟩) from rfl))
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 80).take 8, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 3 10 gs.1 j := by
  have hp : ((section14State section14Catalog 3).plans[5]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  have hs : (((⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(398,⟨([1],[]),true,([1],[]),false,false,[]⟩),(399,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(400,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(401,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(402,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(403,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(404,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(405,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(406,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(407,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(217,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(218,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(408,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(411,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(412,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan).specs.drop 80).take 8) = [(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(409,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(410,⟨([2],[1]),true,([3],[1]),false,false,[]⟩)] := by rfl
  rw [hs]
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 234)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12320 3 10 (by decide) (by decide)
    · right
      exact rec12327 3 10 (by decide) (by decide)
    · right
      exact rec12335 3 10 (by decide) (by decide)
    · right
      exact rec12343 3 10 (by decide) (by decide)
    · right
      exact rec12350 3 10 (by decide) (by decide)
    · right
      exact rec12357 3 10 (by decide) (by decide)
    · right
      exact rec12365 3 10 (by decide) (by decide)
    · right
      exact rec12373 3 10 (by decide) (by decide)
    · right
      exact rec12380 3 10 (by decide) (by decide)
    · right
      exact rec12387 3 10 (by decide) (by decide)
    · right
      exact rec12395 3 10 (by decide) (by decide)
    · right
      exact rec12403 3 10 (by decide) (by decide)
    · right
      exact rec12410 3 10 (by decide) (by decide)
    · right
      exact rec12417 3 10 (by decide) (by decide)
    · right
      exact rec12425 3 10 (by decide) (by decide)
    · right
      exact rec12433 3 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 235)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12440 3 10 (by decide) (by decide)
    · right
      exact rec12446 3 10 (by decide) (by decide)
    · right
      exact rec12453 3 10 (by decide) (by decide)
    · right
      exact rec12460 3 10 (by decide) (by decide)
    · right
      exact rec12466 3 10 (by decide) (by decide)
    · right
      exact rec12472 3 10 (by decide) (by decide)
    · right
      exact rec12479 3 10 (by decide) (by decide)
    · right
      exact rec12486 3 10 (by decide) (by decide)
    · right
      exact rec12492 3 10 (by decide) (by decide)
    · right
      exact rec12498 3 10 (by decide) (by decide)
    · right
      exact rec12505 3 10 (by decide) (by decide)
    · right
      exact rec12512 3 10 (by decide) (by decide)
    · right
      exact rec12518 3 10 (by decide) (by decide)
    · right
      exact rec12524 3 10 (by decide) (by decide)
    · right
      exact rec12531 3 10 (by decide) (by decide)
    · right
      exact rec12538 3 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 236)).length = 4 := by decide +kernel
    have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12544 3 10 (by decide) (by decide)
    · right
      exact rec12551 3 10 (by decide) (by decide)
    · right
      exact rec12559 3 10 (by decide) (by decide)
    · right
      exact rec12567 3 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 237)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12574 3 10 (by decide) (by decide)
    · right
      exact rec12581 3 10 (by decide) (by decide)
    · right
      exact rec12588 3 10 (by decide) (by decide)
    · right
      exact rec12595 3 10 (by decide) (by decide)
    · right
      exact rec12602 3 10 (by decide) (by decide)
    · right
      exact rec12609 3 10 (by decide) (by decide)
    · right
      exact rec12615 3 10 (by decide) (by decide)
    · right
      exact rec12621 3 10 (by decide) (by decide)
    · right
      exact rec12628 3 10 (by decide) (by decide)
    · right
      exact rec12636 3 10 (by decide) (by decide)
    · right
      exact rec12642 3 10 (by decide) (by decide)
    · right
      exact rec12648 3 10 (by decide) (by decide)
    · right
      exact rec12654 3 10 (by decide) (by decide)
    · right
      exact rec12661 3 10 (by decide) (by decide)
    · right
      exact rec12667 3 10 (by decide) (by decide)
    · right
      exact rec12673 3 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 238)).length = 16 := by decide +kernel
    have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
    interval_cases j
    · right
      exact rec12679 3 10 (by decide) (by decide)
    · right
      exact rec12685 3 10 (by decide) (by decide)
    · right
      exact rec12692 3 10 (by decide) (by decide)
    · right
      exact rec12700 3 10 (by decide) (by decide)
    · right
      exact rec12706 3 10 (by decide) (by decide)
    · right
      exact rec12712 3 10 (by decide) (by decide)
    · right
      exact rec12719 3 10 (by decide) (by decide)
    · right
      exact rec12726 3 10 (by decide) (by decide)
    · right
      exact rec12732 3 10 (by decide) (by decide)
    · right
      exact rec12738 3 10 (by decide) (by decide)
    · right
      exact rec12745 3 10 (by decide) (by decide)
    · right
      exact rec12752 3 10 (by decide) (by decide)
    · right
      exact rec12758 3 10 (by decide) (by decide)
    · right
      exact rec12764 3 10 (by decide) (by decide)
    · right
      exact rec12771 3 10 (by decide) (by decide)
    · right
      exact rec12778 3 10 (by decide) (by decide)
  · intro j hj
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 409)).length = 8 := by decide +kernel
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
    have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 410)).length = 10 := by decide +kernel
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
end Section14CoverageSpec_3_5_p10_80_88

#print axioms solution
