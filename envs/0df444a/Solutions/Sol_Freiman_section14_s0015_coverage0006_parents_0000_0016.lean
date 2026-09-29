-- Prove2me | solution 1 for Freiman.section14_s0015_coverage0006_parents_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:36:32.128215+00:00
-- url     : https://prove2.me/submissions/3b3b87af-fb4a-48b5-b58b-1de411a4de11

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
namespace Section14Coverage_15_6_p0_16
private theorem rec15178 (si parent : ℕ) (hs : si ∈ ([3, 7, 11, 15] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[3,7,11,15],[0],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[257]? = some (⟨413,(-1),[3,7,11,15],[0],881⟩) from rfl))
private theorem rec15179 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([1, 2, 3] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[3,7,15],[1,2,3],881⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[258]? = some (⟨413,(-1),[3,7,15],[1,2,3],881⟩) from rfl))
private theorem rec15180 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([4, 5, 6, 7] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[3,7,15],[4,5,6,7],883⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[259]? = some (⟨413,(-1),[3,7,15],[4,5,6,7],883⟩) from rfl))
private theorem rec15181 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([8] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[3,7,15],[8],885⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[260]? = some (⟨413,(-1),[3,7,15],[8],885⟩) from rfl))
private theorem rec15182 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([9] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[3,7,15],[9],887⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[261]? = some (⟨413,(-1),[3,7,15],[9],887⟩) from rfl))
private theorem rec15183 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([11] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[3,7,15],[11],908⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[262]? = some (⟨413,(-1),[3,7,15],[11],908⟩) from rfl))
private theorem rec15184 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([12, 13, 14, 15] : List ℕ)) : section14Recorded section14Catalog si parent 413 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨413,(-1),[3,7,15],[12,13,14,15],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[263]? = some (⟨413,(-1),[3,7,15],[12,13,14,15],910⟩) from rfl))
private theorem rec15187 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(0),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[266]? = some (⟨415,(0),[3,7,15],[10],3⟩) from rfl))
private theorem rec15189 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(1),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[268]? = some (⟨415,(1),[3,7,15],[10],3⟩) from rfl))
private theorem rec15191 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(2),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[270]? = some (⟨415,(2),[3,7,15],[10],3⟩) from rfl))
private theorem rec15193 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(3),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[272]? = some (⟨415,(3),[3,7,15],[10],3⟩) from rfl))
private theorem rec15195 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(4),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[274]? = some (⟨415,(4),[3,7,15],[10],3⟩) from rfl))
private theorem rec15197 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(5),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[276]? = some (⟨415,(5),[3,7,15],[10],3⟩) from rfl))
private theorem rec15199 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(6),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[278]? = some (⟨415,(6),[3,7,15],[10],3⟩) from rfl))
private theorem rec15201 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(7),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[280]? = some (⟨415,(7),[3,7,15],[10],3⟩) from rfl))
private theorem rec15203 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(8),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[282]? = some (⟨415,(8),[3,7,15],[10],3⟩) from rfl))
private theorem rec15205 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 415 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨415,(9),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[284]? = some (⟨415,(9),[3,7,15],[10],3⟩) from rfl))
private theorem rec15207 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(0),[3,7,15],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[286]? = some (⟨417,(0),[3,7,15],[10],10⟩) from rfl))
private theorem rec15208 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(1),[3,7,15],[10],924⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[287]? = some (⟨417,(1),[3,7,15],[10],924⟩) from rfl))
private theorem rec15209 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(2),[3,7,15],[10],888⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[288]? = some (⟨417,(2),[3,7,15],[10],888⟩) from rfl))
private theorem rec15210 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(3),[3,7,15],[10],889⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[289]? = some (⟨417,(3),[3,7,15],[10],889⟩) from rfl))
private theorem rec15211 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(4),[3,7,15],[10],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[290]? = some (⟨417,(4),[3,7,15],[10],890⟩) from rfl))
private theorem rec15212 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(5),[3,7,15],[10],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[291]? = some (⟨417,(5),[3,7,15],[10],10⟩) from rfl))
private theorem rec15213 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(6),[3,7,15],[10],924⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[292]? = some (⟨417,(6),[3,7,15],[10],924⟩) from rfl))
private theorem rec15214 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(7),[3,7,15],[10],888⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[293]? = some (⟨417,(7),[3,7,15],[10],888⟩) from rfl))
private theorem rec15215 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(8),[3,7,15],[10],889⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[294]? = some (⟨417,(8),[3,7,15],[10],889⟩) from rfl))
private theorem rec15216 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(9),[3,7,15],[10],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[295]? = some (⟨417,(9),[3,7,15],[10],890⟩) from rfl))
private theorem rec15217 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(10),[3,7,15],[10],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[296]? = some (⟨417,(10),[3,7,15],[10],18⟩) from rfl))
private theorem rec15218 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(11),[3,7,15],[10],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[297]? = some (⟨417,(11),[3,7,15],[10],891⟩) from rfl))
private theorem rec15219 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(12),[3,7,15],[10],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[298]? = some (⟨417,(12),[3,7,15],[10],891⟩) from rfl))
private theorem rec15220 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(13),[3,7,15],[10],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[299]? = some (⟨417,(13),[3,7,15],[10],891⟩) from rfl))
private theorem rec15221 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(14),[3,7,15],[10],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[300]? = some (⟨417,(14),[3,7,15],[10],890⟩) from rfl))
private theorem rec15222 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(15),[3,7,15],[10],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[301]? = some (⟨417,(15),[3,7,15],[10],21⟩) from rfl))
private theorem rec15223 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(16),[3,7,15],[10],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[302]? = some (⟨417,(16),[3,7,15],[10],892⟩) from rfl))
private theorem rec15224 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(17),[3,7,15],[10],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[303]? = some (⟨417,(17),[3,7,15],[10],892⟩) from rfl))
private theorem rec15225 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(18),[3,7,15],[10],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[304]? = some (⟨417,(18),[3,7,15],[10],892⟩) from rfl))
private theorem rec15226 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(19),[3,7,15],[10],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[305]? = some (⟨417,(19),[3,7,15],[10],892⟩) from rfl))
private theorem rec15227 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(20),[3,7,15],[10],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[306]? = some (⟨417,(20),[3,7,15],[10],24⟩) from rfl))
private theorem rec15228 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(21),[3,7,15],[10],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[307]? = some (⟨417,(21),[3,7,15],[10],893⟩) from rfl))
private theorem rec15229 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(22),[3,7,15],[10],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[308]? = some (⟨417,(22),[3,7,15],[10],893⟩) from rfl))
private theorem rec15230 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(23),[3,7,15],[10],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[309]? = some (⟨417,(23),[3,7,15],[10],893⟩) from rfl))
private theorem rec15231 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 417 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨417,(24),[3,7,15],[10],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[310]? = some (⟨417,(24),[3,7,15],[10],893⟩) from rfl))
private theorem rec15232 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(0),[3,7,15],[10],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[311]? = some (⟨420,(0),[3,7,15],[10],1086⟩) from rfl))
private theorem rec15234 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(1),[3,7,15],[10],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[313]? = some (⟨420,(1),[3,7,15],[10],1087⟩) from rfl))
private theorem rec15236 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(2),[3,7,15],[10],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[315]? = some (⟨420,(2),[3,7,15],[10],1088⟩) from rfl))
private theorem rec15238 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(3),[3,7,15],[10],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[317]? = some (⟨420,(3),[3,7,15],[10],1089⟩) from rfl))
private theorem rec15240 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(4),[3,7,15],[10],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[319]? = some (⟨420,(4),[3,7,15],[10],1086⟩) from rfl))
private theorem rec15242 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(5),[3,7,15],[10],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[321]? = some (⟨420,(5),[3,7,15],[10],1087⟩) from rfl))
private theorem rec15244 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(6),[3,7,15],[10],1090⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[323]? = some (⟨420,(6),[3,7,15],[10],1090⟩) from rfl))
private theorem rec15246 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(7),[3,7,15],[10],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[325]? = some (⟨420,(7),[3,7,15],[10],1089⟩) from rfl))
private theorem rec15248 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(8),[3,7,15],[10],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[327]? = some (⟨420,(8),[3,7,15],[10],1086⟩) from rfl))
private theorem rec15250 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(9),[3,7,15],[10],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[329]? = some (⟨420,(9),[3,7,15],[10],1087⟩) from rfl))
private theorem rec15252 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(10),[3,7,15],[10],1088⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[331]? = some (⟨420,(10),[3,7,15],[10],1088⟩) from rfl))
private theorem rec15254 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(11),[3,7,15],[10],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[333]? = some (⟨420,(11),[3,7,15],[10],1089⟩) from rfl))
private theorem rec15256 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(12),[3,7,15],[10],1086⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[335]? = some (⟨420,(12),[3,7,15],[10],1086⟩) from rfl))
private theorem rec15258 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(13),[3,7,15],[10],1087⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[337]? = some (⟨420,(13),[3,7,15],[10],1087⟩) from rfl))
private theorem rec15260 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(14),[3,7,15],[10],1091⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[339]? = some (⟨420,(14),[3,7,15],[10],1091⟩) from rfl))
private theorem rec15262 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 420 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨420,(15),[3,7,15],[10],1089⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[341]? = some (⟨420,(15),[3,7,15],[10],1089⟩) from rfl))
private theorem rec15264 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(0),[3,7,15],[10],1092⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[343]? = some (⟨423,(0),[3,7,15],[10],1092⟩) from rfl))
private theorem rec15266 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(1),[3,7,15],[10],1093⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[345]? = some (⟨423,(1),[3,7,15],[10],1093⟩) from rfl))
private theorem rec15268 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(2),[3,7,15],[10],1092⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[347]? = some (⟨423,(2),[3,7,15],[10],1092⟩) from rfl))
private theorem rec15270 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(3),[3,7,15],[10],1094⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[349]? = some (⟨423,(3),[3,7,15],[10],1094⟩) from rfl))
private theorem rec15272 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(4),[3,7,15],[10],1095⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[351]? = some (⟨423,(4),[3,7,15],[10],1095⟩) from rfl))
private theorem rec15274 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(5),[3,7,15],[10],1095⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[353]? = some (⟨423,(5),[3,7,15],[10],1095⟩) from rfl))
private theorem rec15276 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(6),[3,7,15],[10],1095⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[355]? = some (⟨423,(6),[3,7,15],[10],1095⟩) from rfl))
private theorem rec15278 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(7),[3,7,15],[10],1095⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[357]? = some (⟨423,(7),[3,7,15],[10],1095⟩) from rfl))
private theorem rec15280 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(8),[3,7,15],[10],1096⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[359]? = some (⟨423,(8),[3,7,15],[10],1096⟩) from rfl))
private theorem rec15282 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(9),[3,7,15],[10],1096⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[361]? = some (⟨423,(9),[3,7,15],[10],1096⟩) from rfl))
private theorem rec15284 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(10),[3,7,15],[10],1096⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[363]? = some (⟨423,(10),[3,7,15],[10],1096⟩) from rfl))
private theorem rec15286 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(11),[3,7,15],[10],1096⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[365]? = some (⟨423,(11),[3,7,15],[10],1096⟩) from rfl))
private theorem rec15288 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(12),[3,7,15],[10],1097⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[367]? = some (⟨423,(12),[3,7,15],[10],1097⟩) from rfl))
private theorem rec15290 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(13),[3,7,15],[10],1097⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[369]? = some (⟨423,(13),[3,7,15],[10],1097⟩) from rfl))
private theorem rec15292 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(14),[3,7,15],[10],1097⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[371]? = some (⟨423,(14),[3,7,15],[10],1097⟩) from rfl))
private theorem rec15294 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 423 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨423,(15),[3,7,15],[10],1097⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[373]? = some (⟨423,(15),[3,7,15],[10],1097⟩) from rfl))
private theorem rec15296 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(0),[3,7,15],[10],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[375]? = some (⟨426,(0),[3,7,15],[10],1098⟩) from rfl))
private theorem rec15298 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(1),[3,7,15],[10],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[377]? = some (⟨426,(1),[3,7,15],[10],1099⟩) from rfl))
private theorem rec15300 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(2),[3,7,15],[10],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[379]? = some (⟨426,(2),[3,7,15],[10],1100⟩) from rfl))
private theorem rec15302 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(3),[3,7,15],[10],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[381]? = some (⟨426,(3),[3,7,15],[10],1100⟩) from rfl))
private theorem rec15304 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(4),[3,7,15],[10],1100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[383]? = some (⟨426,(4),[3,7,15],[10],1100⟩) from rfl))
private theorem rec15306 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(5),[3,7,15],[10],1098⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[385]? = some (⟨426,(5),[3,7,15],[10],1098⟩) from rfl))
private theorem rec15308 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(6),[3,7,15],[10],1099⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[387]? = some (⟨426,(6),[3,7,15],[10],1099⟩) from rfl))
private theorem rec15310 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(7),[3,7,15],[10],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[389]? = some (⟨426,(7),[3,7,15],[10],1101⟩) from rfl))
private theorem rec15312 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(8),[3,7,15],[10],1102⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[391]? = some (⟨426,(8),[3,7,15],[10],1102⟩) from rfl))
private theorem rec15314 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 426 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨426,(9),[3,7,15],[10],1101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[393]? = some (⟨426,(9),[3,7,15],[10],1101⟩) from rfl))
private theorem rec15316 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(0),[3,7,15],[10],1103⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[395]? = some (⟨428,(0),[3,7,15],[10],1103⟩) from rfl))
private theorem rec15318 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(1),[3,7,15],[10],1103⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[397]? = some (⟨428,(1),[3,7,15],[10],1103⟩) from rfl))
private theorem rec15320 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(2),[3,7,15],[10],1104⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[399]? = some (⟨428,(2),[3,7,15],[10],1104⟩) from rfl))
private theorem rec15322 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(3),[3,7,15],[10],1105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[401]? = some (⟨428,(3),[3,7,15],[10],1105⟩) from rfl))
private theorem rec15324 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(4),[3,7,15],[10],1106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[403]? = some (⟨428,(4),[3,7,15],[10],1106⟩) from rfl))
private theorem rec15326 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(5),[3,7,15],[10],1107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[405]? = some (⟨428,(5),[3,7,15],[10],1107⟩) from rfl))
private theorem rec15328 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(6),[3,7,15],[10],1107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[407]? = some (⟨428,(6),[3,7,15],[10],1107⟩) from rfl))
private theorem rec15330 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(7),[3,7,15],[10],1107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[409]? = some (⟨428,(7),[3,7,15],[10],1107⟩) from rfl))
private theorem rec15332 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(8),[3,7,15],[10],1105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[411]? = some (⟨428,(8),[3,7,15],[10],1105⟩) from rfl))
private theorem rec15334 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 428 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨428,(9),[3,7,15],[10],1106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[413]? = some (⟨428,(9),[3,7,15],[10],1106⟩) from rfl))
private theorem rec15336 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(0),[3,7,15],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[415]? = some (⟨431,(0),[3,7,15],[10],1108⟩) from rfl))
private theorem rec15338 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(1),[3,7,15],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[417]? = some (⟨431,(1),[3,7,15],[10],1109⟩) from rfl))
private theorem rec15340 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(2),[3,7,15],[10],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[419]? = some (⟨431,(2),[3,7,15],[10],1110⟩) from rfl))
private theorem rec15342 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(3),[3,7,15],[10],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[421]? = some (⟨431,(3),[3,7,15],[10],1110⟩) from rfl))
private theorem rec15344 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(4),[3,7,15],[10],1110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[423]? = some (⟨431,(4),[3,7,15],[10],1110⟩) from rfl))
private theorem rec15346 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(5),[3,7,15],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[425]? = some (⟨431,(5),[3,7,15],[10],1108⟩) from rfl))
private theorem rec15348 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(6),[3,7,15],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[427]? = some (⟨431,(6),[3,7,15],[10],1109⟩) from rfl))
private theorem rec15350 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(7),[3,7,15],[10],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[429]? = some (⟨431,(7),[3,7,15],[10],1111⟩) from rfl))
private theorem rec15352 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(8),[3,7,15],[10],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[431]? = some (⟨431,(8),[3,7,15],[10],1112⟩) from rfl))
private theorem rec15354 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(9),[3,7,15],[10],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[433]? = some (⟨431,(9),[3,7,15],[10],1111⟩) from rfl))
private theorem rec15356 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(10),[3,7,15],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[435]? = some (⟨431,(10),[3,7,15],[10],1108⟩) from rfl))
private theorem rec15358 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(11),[3,7,15],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[437]? = some (⟨431,(11),[3,7,15],[10],1109⟩) from rfl))
private theorem rec15360 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(12),[3,7,15],[10],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[439]? = some (⟨431,(12),[3,7,15],[10],1113⟩) from rfl))
private theorem rec15362 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(13),[3,7,15],[10],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[441]? = some (⟨431,(13),[3,7,15],[10],1112⟩) from rfl))
private theorem rec15364 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(14),[3,7,15],[10],1113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[443]? = some (⟨431,(14),[3,7,15],[10],1113⟩) from rfl))
private theorem rec15366 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(15),[3,7,15],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[445]? = some (⟨431,(15),[3,7,15],[10],1108⟩) from rfl))
private theorem rec15368 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(16),[3,7,15],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[447]? = some (⟨431,(16),[3,7,15],[10],1109⟩) from rfl))
private theorem rec15370 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(17),[3,7,15],[10],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[449]? = some (⟨431,(17),[3,7,15],[10],1111⟩) from rfl))
private theorem rec15372 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(18),[3,7,15],[10],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[451]? = some (⟨431,(18),[3,7,15],[10],1112⟩) from rfl))
private theorem rec15374 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(19),[3,7,15],[10],1111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[453]? = some (⟨431,(19),[3,7,15],[10],1111⟩) from rfl))
private theorem rec15376 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(20),[3,7,15],[10],1108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[455]? = some (⟨431,(20),[3,7,15],[10],1108⟩) from rfl))
private theorem rec15378 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(21),[3,7,15],[10],1109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[457]? = some (⟨431,(21),[3,7,15],[10],1109⟩) from rfl))
private theorem rec15380 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(22),[3,7,15],[10],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[459]? = some (⟨431,(22),[3,7,15],[10],1114⟩) from rfl))
private theorem rec15382 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(23),[3,7,15],[10],1112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[461]? = some (⟨431,(23),[3,7,15],[10],1112⟩) from rfl))
private theorem rec15384 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 431 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨431,(24),[3,7,15],[10],1114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[463]? = some (⟨431,(24),[3,7,15],[10],1114⟩) from rfl))
private theorem rec15386 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(0),[3,7,15],[10],1115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[465]? = some (⟨433,(0),[3,7,15],[10],1115⟩) from rfl))
private theorem rec15388 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(1),[3,7,15],[10],1115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[467]? = some (⟨433,(1),[3,7,15],[10],1115⟩) from rfl))
private theorem rec15390 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(2),[3,7,15],[10],1116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[469]? = some (⟨433,(2),[3,7,15],[10],1116⟩) from rfl))
private theorem rec15392 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(3),[3,7,15],[10],1117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[471]? = some (⟨433,(3),[3,7,15],[10],1117⟩) from rfl))
private theorem rec15394 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(4),[3,7,15],[10],1118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[473]? = some (⟨433,(4),[3,7,15],[10],1118⟩) from rfl))
private theorem rec15396 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(5),[3,7,15],[10],1119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[475]? = some (⟨433,(5),[3,7,15],[10],1119⟩) from rfl))
private theorem rec15398 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(6),[3,7,15],[10],1119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[477]? = some (⟨433,(6),[3,7,15],[10],1119⟩) from rfl))
private theorem rec15400 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(7),[3,7,15],[10],1119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[479]? = some (⟨433,(7),[3,7,15],[10],1119⟩) from rfl))
private theorem rec15402 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(8),[3,7,15],[10],1117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[481]? = some (⟨433,(8),[3,7,15],[10],1117⟩) from rfl))
private theorem rec15404 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 433 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨433,(9),[3,7,15],[10],1118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[483]? = some (⟨433,(9),[3,7,15],[10],1118⟩) from rfl))
private theorem rec15406 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(0),[3,7,15],[10],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[485]? = some (⟨436,(0),[3,7,15],[10],1120⟩) from rfl))
private theorem rec15408 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(1),[3,7,15],[10],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[487]? = some (⟨436,(1),[3,7,15],[10],1121⟩) from rfl))
private theorem rec15410 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(2),[3,7,15],[10],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[489]? = some (⟨436,(2),[3,7,15],[10],1122⟩) from rfl))
private theorem rec15412 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(3),[3,7,15],[10],1122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[491]? = some (⟨436,(3),[3,7,15],[10],1122⟩) from rfl))
private theorem rec15414 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(4),[3,7,15],[10],1123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[493]? = some (⟨436,(4),[3,7,15],[10],1123⟩) from rfl))
private theorem rec15416 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(5),[3,7,15],[10],1120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[495]? = some (⟨436,(5),[3,7,15],[10],1120⟩) from rfl))
private theorem rec15418 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(6),[3,7,15],[10],1121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[497]? = some (⟨436,(6),[3,7,15],[10],1121⟩) from rfl))
private theorem rec15420 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(7),[3,7,15],[10],1124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[499]? = some (⟨436,(7),[3,7,15],[10],1124⟩) from rfl))
private theorem rec15422 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(8),[3,7,15],[10],1125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[501]? = some (⟨436,(8),[3,7,15],[10],1125⟩) from rfl))
private theorem rec15424 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 436 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨436,(9),[3,7,15],[10],1126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[503]? = some (⟨436,(9),[3,7,15],[10],1126⟩) from rfl))
private theorem rec15426 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(0),[3,7,15],[10],1127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[505]? = some (⟨438,(0),[3,7,15],[10],1127⟩) from rfl))
private theorem rec15428 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(1),[3,7,15],[10],1127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[507]? = some (⟨438,(1),[3,7,15],[10],1127⟩) from rfl))
private theorem rec15430 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(2),[3,7,15],[10],1128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[509]? = some (⟨438,(2),[3,7,15],[10],1128⟩) from rfl))
private theorem rec15432 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(3),[3,7,15],[10],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[511]? = some (⟨438,(3),[3,7,15],[10],1129⟩) from rfl))
private theorem rec15434 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(4),[3,7,15],[10],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[513]? = some (⟨438,(4),[3,7,15],[10],1130⟩) from rfl))
private theorem rec15436 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(5),[3,7,15],[10],1131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[515]? = some (⟨438,(5),[3,7,15],[10],1131⟩) from rfl))
private theorem rec15438 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(6),[3,7,15],[10],1131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[517]? = some (⟨438,(6),[3,7,15],[10],1131⟩) from rfl))
private theorem rec15440 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(7),[3,7,15],[10],1128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[519]? = some (⟨438,(7),[3,7,15],[10],1128⟩) from rfl))
private theorem rec15442 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(8),[3,7,15],[10],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[521]? = some (⟨438,(8),[3,7,15],[10],1129⟩) from rfl))
private theorem rec15444 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(9),[3,7,15],[10],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[523]? = some (⟨438,(9),[3,7,15],[10],1130⟩) from rfl))
private theorem rec15446 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(10),[3,7,15],[10],1127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[525]? = some (⟨438,(10),[3,7,15],[10],1127⟩) from rfl))
private theorem rec15448 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(11),[3,7,15],[10],1127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[527]? = some (⟨438,(11),[3,7,15],[10],1127⟩) from rfl))
private theorem rec15450 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(12),[3,7,15],[10],1128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[529]? = some (⟨438,(12),[3,7,15],[10],1128⟩) from rfl))
private theorem rec15452 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(13),[3,7,15],[10],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[531]? = some (⟨438,(13),[3,7,15],[10],1129⟩) from rfl))
private theorem rec15454 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(14),[3,7,15],[10],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[533]? = some (⟨438,(14),[3,7,15],[10],1130⟩) from rfl))
private theorem rec15456 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(15),[3,7,15],[10],1132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[535]? = some (⟨438,(15),[3,7,15],[10],1132⟩) from rfl))
private theorem rec15458 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(16),[3,7,15],[10],1132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[537]? = some (⟨438,(16),[3,7,15],[10],1132⟩) from rfl))
private theorem rec15460 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(17),[3,7,15],[10],1128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[539]? = some (⟨438,(17),[3,7,15],[10],1128⟩) from rfl))
private theorem rec15462 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(18),[3,7,15],[10],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[541]? = some (⟨438,(18),[3,7,15],[10],1129⟩) from rfl))
private theorem rec15464 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(19),[3,7,15],[10],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[543]? = some (⟨438,(19),[3,7,15],[10],1130⟩) from rfl))
private theorem rec15466 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(20),[3,7,15],[10],1133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[545]? = some (⟨438,(20),[3,7,15],[10],1133⟩) from rfl))
private theorem rec15468 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(21),[3,7,15],[10],1133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[547]? = some (⟨438,(21),[3,7,15],[10],1133⟩) from rfl))
private theorem rec15470 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(22),[3,7,15],[10],1133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[549]? = some (⟨438,(22),[3,7,15],[10],1133⟩) from rfl))
private theorem rec15472 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(23),[3,7,15],[10],1129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[551]? = some (⟨438,(23),[3,7,15],[10],1129⟩) from rfl))
private theorem rec15474 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 438 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨438,(24),[3,7,15],[10],1130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[553]? = some (⟨438,(24),[3,7,15],[10],1130⟩) from rfl))
private theorem rec15476 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(0),[3,7,15],[10],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[555]? = some (⟨441,(0),[3,7,15],[10],1134⟩) from rfl))
private theorem rec15478 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(1),[3,7,15],[10],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[557]? = some (⟨441,(1),[3,7,15],[10],1135⟩) from rfl))
private theorem rec15480 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(2),[3,7,15],[10],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[559]? = some (⟨441,(2),[3,7,15],[10],1136⟩) from rfl))
private theorem rec15482 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(3),[3,7,15],[10],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[561]? = some (⟨441,(3),[3,7,15],[10],1136⟩) from rfl))
private theorem rec15484 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(4),[3,7,15],[10],1136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[563]? = some (⟨441,(4),[3,7,15],[10],1136⟩) from rfl))
private theorem rec15486 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(5),[3,7,15],[10],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[565]? = some (⟨441,(5),[3,7,15],[10],1134⟩) from rfl))
private theorem rec15488 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(6),[3,7,15],[10],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[567]? = some (⟨441,(6),[3,7,15],[10],1135⟩) from rfl))
private theorem rec15490 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(7),[3,7,15],[10],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[569]? = some (⟨441,(7),[3,7,15],[10],1137⟩) from rfl))
private theorem rec15492 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(8),[3,7,15],[10],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[571]? = some (⟨441,(8),[3,7,15],[10],1138⟩) from rfl))
private theorem rec15494 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(9),[3,7,15],[10],1137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[573]? = some (⟨441,(9),[3,7,15],[10],1137⟩) from rfl))
private theorem rec15496 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(10),[3,7,15],[10],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[575]? = some (⟨441,(10),[3,7,15],[10],1134⟩) from rfl))
private theorem rec15498 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(11),[3,7,15],[10],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[577]? = some (⟨441,(11),[3,7,15],[10],1135⟩) from rfl))
private theorem rec15500 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(12),[3,7,15],[10],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[579]? = some (⟨441,(12),[3,7,15],[10],1139⟩) from rfl))
private theorem rec15502 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(13),[3,7,15],[10],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[581]? = some (⟨441,(13),[3,7,15],[10],1138⟩) from rfl))
private theorem rec15504 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(14),[3,7,15],[10],1139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[583]? = some (⟨441,(14),[3,7,15],[10],1139⟩) from rfl))
private theorem rec15506 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(15),[3,7,15],[10],1140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[585]? = some (⟨441,(15),[3,7,15],[10],1140⟩) from rfl))
private theorem rec15508 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(16),[3,7,15],[10],1141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[587]? = some (⟨441,(16),[3,7,15],[10],1141⟩) from rfl))
private theorem rec15510 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(17),[3,7,15],[10],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[589]? = some (⟨441,(17),[3,7,15],[10],1142⟩) from rfl))
private theorem rec15512 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(18),[3,7,15],[10],1143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[591]? = some (⟨441,(18),[3,7,15],[10],1143⟩) from rfl))
private theorem rec15514 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(19),[3,7,15],[10],1142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[593]? = some (⟨441,(19),[3,7,15],[10],1142⟩) from rfl))
private theorem rec15516 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(20),[3,7,15],[10],1134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[595]? = some (⟨441,(20),[3,7,15],[10],1134⟩) from rfl))
private theorem rec15518 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(21),[3,7,15],[10],1135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[597]? = some (⟨441,(21),[3,7,15],[10],1135⟩) from rfl))
private theorem rec15520 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(22),[3,7,15],[10],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[599]? = some (⟨441,(22),[3,7,15],[10],1144⟩) from rfl))
private theorem rec15522 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(23),[3,7,15],[10],1138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[601]? = some (⟨441,(23),[3,7,15],[10],1138⟩) from rfl))
private theorem rec15524 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 441 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨441,(24),[3,7,15],[10],1144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[603]? = some (⟨441,(24),[3,7,15],[10],1144⟩) from rfl))
private theorem rec15526 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(0),[3,7,15],[10],1145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[605]? = some (⟨443,(0),[3,7,15],[10],1145⟩) from rfl))
private theorem rec15528 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(1),[3,7,15],[10],1145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[607]? = some (⟨443,(1),[3,7,15],[10],1145⟩) from rfl))
private theorem rec15530 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(2),[3,7,15],[10],1146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[609]? = some (⟨443,(2),[3,7,15],[10],1146⟩) from rfl))
private theorem rec15532 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(3),[3,7,15],[10],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[611]? = some (⟨443,(3),[3,7,15],[10],1147⟩) from rfl))
private theorem rec15534 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(4),[3,7,15],[10],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[613]? = some (⟨443,(4),[3,7,15],[10],1148⟩) from rfl))
private theorem rec15536 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(5),[3,7,15],[10],1149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[615]? = some (⟨443,(5),[3,7,15],[10],1149⟩) from rfl))
private theorem rec15538 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(6),[3,7,15],[10],1149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[617]? = some (⟨443,(6),[3,7,15],[10],1149⟩) from rfl))
private theorem rec15540 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(7),[3,7,15],[10],1146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[619]? = some (⟨443,(7),[3,7,15],[10],1146⟩) from rfl))
private theorem rec15542 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(8),[3,7,15],[10],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[621]? = some (⟨443,(8),[3,7,15],[10],1147⟩) from rfl))
private theorem rec15544 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(9),[3,7,15],[10],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[623]? = some (⟨443,(9),[3,7,15],[10],1148⟩) from rfl))
private theorem rec15546 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(10),[3,7,15],[10],1145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[625]? = some (⟨443,(10),[3,7,15],[10],1145⟩) from rfl))
private theorem rec15548 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(11),[3,7,15],[10],1145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[627]? = some (⟨443,(11),[3,7,15],[10],1145⟩) from rfl))
private theorem rec15550 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(12),[3,7,15],[10],1146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[629]? = some (⟨443,(12),[3,7,15],[10],1146⟩) from rfl))
private theorem rec15552 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(13),[3,7,15],[10],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[631]? = some (⟨443,(13),[3,7,15],[10],1147⟩) from rfl))
private theorem rec15554 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(14),[3,7,15],[10],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[633]? = some (⟨443,(14),[3,7,15],[10],1148⟩) from rfl))
private theorem rec15556 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(15),[3,7,15],[10],1150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[635]? = some (⟨443,(15),[3,7,15],[10],1150⟩) from rfl))
private theorem rec15558 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(16),[3,7,15],[10],1150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[637]? = some (⟨443,(16),[3,7,15],[10],1150⟩) from rfl))
private theorem rec15560 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(17),[3,7,15],[10],1146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[639]? = some (⟨443,(17),[3,7,15],[10],1146⟩) from rfl))
private theorem rec15562 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(18),[3,7,15],[10],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[641]? = some (⟨443,(18),[3,7,15],[10],1147⟩) from rfl))
private theorem rec15564 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(19),[3,7,15],[10],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[643]? = some (⟨443,(19),[3,7,15],[10],1148⟩) from rfl))
private theorem rec15566 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(20),[3,7,15],[10],1151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[645]? = some (⟨443,(20),[3,7,15],[10],1151⟩) from rfl))
private theorem rec15568 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(21),[3,7,15],[10],1151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[647]? = some (⟨443,(21),[3,7,15],[10],1151⟩) from rfl))
private theorem rec15570 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(22),[3,7,15],[10],1151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[649]? = some (⟨443,(22),[3,7,15],[10],1151⟩) from rfl))
private theorem rec15572 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(23),[3,7,15],[10],1147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[651]? = some (⟨443,(23),[3,7,15],[10],1147⟩) from rfl))
private theorem rec15574 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 443 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨443,(24),[3,7,15],[10],1148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[653]? = some (⟨443,(24),[3,7,15],[10],1148⟩) from rfl))
private theorem rec15576 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(0),[3,7,15],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[655]? = some (⟨446,(0),[3,7,15],[10],1152⟩) from rfl))
private theorem rec15578 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(1),[3,7,15],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[657]? = some (⟨446,(1),[3,7,15],[10],1153⟩) from rfl))
private theorem rec15580 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(2),[3,7,15],[10],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[659]? = some (⟨446,(2),[3,7,15],[10],1154⟩) from rfl))
private theorem rec15582 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(3),[3,7,15],[10],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[661]? = some (⟨446,(3),[3,7,15],[10],1154⟩) from rfl))
private theorem rec15584 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(4),[3,7,15],[10],1154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[663]? = some (⟨446,(4),[3,7,15],[10],1154⟩) from rfl))
private theorem rec15586 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(5),[3,7,15],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[665]? = some (⟨446,(5),[3,7,15],[10],1152⟩) from rfl))
private theorem rec15588 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(6),[3,7,15],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[667]? = some (⟨446,(6),[3,7,15],[10],1153⟩) from rfl))
private theorem rec15590 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(7),[3,7,15],[10],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[669]? = some (⟨446,(7),[3,7,15],[10],1155⟩) from rfl))
private theorem rec15592 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(8),[3,7,15],[10],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[671]? = some (⟨446,(8),[3,7,15],[10],1156⟩) from rfl))
private theorem rec15594 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(9),[3,7,15],[10],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[673]? = some (⟨446,(9),[3,7,15],[10],1155⟩) from rfl))
private theorem rec15596 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(10),[3,7,15],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[675]? = some (⟨446,(10),[3,7,15],[10],1152⟩) from rfl))
private theorem rec15598 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(11),[3,7,15],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[677]? = some (⟨446,(11),[3,7,15],[10],1153⟩) from rfl))
private theorem rec15600 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(12),[3,7,15],[10],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[679]? = some (⟨446,(12),[3,7,15],[10],1157⟩) from rfl))
private theorem rec15602 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(13),[3,7,15],[10],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[681]? = some (⟨446,(13),[3,7,15],[10],1156⟩) from rfl))
private theorem rec15604 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(14),[3,7,15],[10],1157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[683]? = some (⟨446,(14),[3,7,15],[10],1157⟩) from rfl))
private theorem rec15606 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(15),[3,7,15],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[685]? = some (⟨446,(15),[3,7,15],[10],1152⟩) from rfl))
private theorem rec15608 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(16),[3,7,15],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[687]? = some (⟨446,(16),[3,7,15],[10],1153⟩) from rfl))
private theorem rec15610 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(17),[3,7,15],[10],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[689]? = some (⟨446,(17),[3,7,15],[10],1155⟩) from rfl))
private theorem rec15612 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(18),[3,7,15],[10],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[691]? = some (⟨446,(18),[3,7,15],[10],1156⟩) from rfl))
private theorem rec15614 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(19),[3,7,15],[10],1155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[693]? = some (⟨446,(19),[3,7,15],[10],1155⟩) from rfl))
private theorem rec15616 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(20),[3,7,15],[10],1152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[695]? = some (⟨446,(20),[3,7,15],[10],1152⟩) from rfl))
private theorem rec15618 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(21),[3,7,15],[10],1153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[697]? = some (⟨446,(21),[3,7,15],[10],1153⟩) from rfl))
private theorem rec15620 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(22),[3,7,15],[10],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[699]? = some (⟨446,(22),[3,7,15],[10],1158⟩) from rfl))
private theorem rec15622 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(23),[3,7,15],[10],1156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[701]? = some (⟨446,(23),[3,7,15],[10],1156⟩) from rfl))
private theorem rec15624 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 446 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨446,(24),[3,7,15],[10],1158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[703]? = some (⟨446,(24),[3,7,15],[10],1158⟩) from rfl))
private theorem rec15626 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(0),[3,7,15],[10],1159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[705]? = some (⟨448,(0),[3,7,15],[10],1159⟩) from rfl))
private theorem rec15628 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(1),[3,7,15],[10],1159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[707]? = some (⟨448,(1),[3,7,15],[10],1159⟩) from rfl))
private theorem rec15630 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(2),[3,7,15],[10],1160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[709]? = some (⟨448,(2),[3,7,15],[10],1160⟩) from rfl))
private theorem rec15632 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(3),[3,7,15],[10],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[711]? = some (⟨448,(3),[3,7,15],[10],1161⟩) from rfl))
private theorem rec15634 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(4),[3,7,15],[10],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[713]? = some (⟨448,(4),[3,7,15],[10],1162⟩) from rfl))
private theorem rec15636 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(5),[3,7,15],[10],1163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[715]? = some (⟨448,(5),[3,7,15],[10],1163⟩) from rfl))
private theorem rec15638 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(6),[3,7,15],[10],1163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[717]? = some (⟨448,(6),[3,7,15],[10],1163⟩) from rfl))
private theorem rec15640 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(7),[3,7,15],[10],1160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[719]? = some (⟨448,(7),[3,7,15],[10],1160⟩) from rfl))
private theorem rec15642 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(8),[3,7,15],[10],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[721]? = some (⟨448,(8),[3,7,15],[10],1161⟩) from rfl))
private theorem rec15644 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(9),[3,7,15],[10],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[723]? = some (⟨448,(9),[3,7,15],[10],1162⟩) from rfl))
private theorem rec15646 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(10),[3,7,15],[10],1159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[725]? = some (⟨448,(10),[3,7,15],[10],1159⟩) from rfl))
private theorem rec15648 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(11),[3,7,15],[10],1159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[727]? = some (⟨448,(11),[3,7,15],[10],1159⟩) from rfl))
private theorem rec15650 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(12),[3,7,15],[10],1160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[729]? = some (⟨448,(12),[3,7,15],[10],1160⟩) from rfl))
private theorem rec15652 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(13),[3,7,15],[10],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[731]? = some (⟨448,(13),[3,7,15],[10],1161⟩) from rfl))
private theorem rec15654 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(14),[3,7,15],[10],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[733]? = some (⟨448,(14),[3,7,15],[10],1162⟩) from rfl))
private theorem rec15656 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(15),[3,7,15],[10],1164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[735]? = some (⟨448,(15),[3,7,15],[10],1164⟩) from rfl))
private theorem rec15658 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(16),[3,7,15],[10],1164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[737]? = some (⟨448,(16),[3,7,15],[10],1164⟩) from rfl))
private theorem rec15660 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(17),[3,7,15],[10],1160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[739]? = some (⟨448,(17),[3,7,15],[10],1160⟩) from rfl))
private theorem rec15662 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(18),[3,7,15],[10],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[741]? = some (⟨448,(18),[3,7,15],[10],1161⟩) from rfl))
private theorem rec15664 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(19),[3,7,15],[10],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[743]? = some (⟨448,(19),[3,7,15],[10],1162⟩) from rfl))
private theorem rec15666 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(20),[3,7,15],[10],1165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[745]? = some (⟨448,(20),[3,7,15],[10],1165⟩) from rfl))
private theorem rec15668 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(21),[3,7,15],[10],1165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[747]? = some (⟨448,(21),[3,7,15],[10],1165⟩) from rfl))
private theorem rec15670 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(22),[3,7,15],[10],1165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[749]? = some (⟨448,(22),[3,7,15],[10],1165⟩) from rfl))
private theorem rec15672 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(23),[3,7,15],[10],1161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[751]? = some (⟨448,(23),[3,7,15],[10],1161⟩) from rfl))
private theorem rec15674 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 448 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨448,(24),[3,7,15],[10],1162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[753]? = some (⟨448,(24),[3,7,15],[10],1162⟩) from rfl))
private theorem rec15676 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 450 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨450,(0),[3,7,15],[10],1166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[755]? = some (⟨450,(0),[3,7,15],[10],1166⟩) from rfl))
private theorem rec15678 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 450 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨450,(1),[3,7,15],[10],1167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[757]? = some (⟨450,(1),[3,7,15],[10],1167⟩) from rfl))
private theorem rec15680 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 450 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨450,(2),[3,7,15],[10],1168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[759]? = some (⟨450,(2),[3,7,15],[10],1168⟩) from rfl))
private theorem rec15682 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 450 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨450,(3),[3,7,15],[10],1169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[761]? = some (⟨450,(3),[3,7,15],[10],1169⟩) from rfl))
private theorem rec15684 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(0),[3,7,15],[10],1170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[763]? = some (⟨453,(0),[3,7,15],[10],1170⟩) from rfl))
private theorem rec15686 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(1),[3,7,15],[10],1171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[765]? = some (⟨453,(1),[3,7,15],[10],1171⟩) from rfl))
private theorem rec15688 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(2),[3,7,15],[10],1170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[767]? = some (⟨453,(2),[3,7,15],[10],1170⟩) from rfl))
private theorem rec15690 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(3),[3,7,15],[10],1172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[769]? = some (⟨453,(3),[3,7,15],[10],1172⟩) from rfl))
private theorem rec15692 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(4),[3,7,15],[10],1173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[771]? = some (⟨453,(4),[3,7,15],[10],1173⟩) from rfl))
private theorem rec15694 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(5),[3,7,15],[10],1173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[773]? = some (⟨453,(5),[3,7,15],[10],1173⟩) from rfl))
private theorem rec15696 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(6),[3,15],[10],1174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[775]? = some (⟨453,(6),[3,15],[10],1174⟩) from rfl))
private theorem rec15699 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(7),[3,7,15],[10],1173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[778]? = some (⟨453,(7),[3,7,15],[10],1173⟩) from rfl))
private theorem rec15701 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(8),[3,7,15],[10],1175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[780]? = some (⟨453,(8),[3,7,15],[10],1175⟩) from rfl))
private theorem rec15703 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(9),[3,7,15],[10],1175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[782]? = some (⟨453,(9),[3,7,15],[10],1175⟩) from rfl))
private theorem rec15705 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(10),[3,7,15],[10],1175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[784]? = some (⟨453,(10),[3,7,15],[10],1175⟩) from rfl))
private theorem rec15707 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(11),[3,7,15],[10],1175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[786]? = some (⟨453,(11),[3,7,15],[10],1175⟩) from rfl))
private theorem rec15709 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(12),[3,7,15],[10],1176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[788]? = some (⟨453,(12),[3,7,15],[10],1176⟩) from rfl))
private theorem rec15711 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(13),[3,7,15],[10],1176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[790]? = some (⟨453,(13),[3,7,15],[10],1176⟩) from rfl))
private theorem rec15713 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(14),[3,7,15],[10],1176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[792]? = some (⟨453,(14),[3,7,15],[10],1176⟩) from rfl))
private theorem rec15715 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 453 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨453,(15),[3,7,15],[10],1176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[794]? = some (⟨453,(15),[3,7,15],[10],1176⟩) from rfl))
private theorem rec15734 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 460 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(0),[3,7,15],[10],1184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[813]? = some (⟨460,(0),[3,7,15],[10],1184⟩) from rfl))
private theorem rec15736 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 460 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(1),[3,7,15],[10],958⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[815]? = some (⟨460,(1),[3,7,15],[10],958⟩) from rfl))
private theorem rec15738 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 460 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(2),[3,7,15],[10],959⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[817]? = some (⟨460,(2),[3,7,15],[10],959⟩) from rfl))
private theorem rec15740 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 460 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(3),[3,7,15],[10],960⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[819]? = some (⟨460,(3),[3,7,15],[10],960⟩) from rfl))
private theorem rec15742 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 460 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨460,(4),[3,7,15],[10],961⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[821]? = some (⟨460,(4),[3,7,15],[10],961⟩) from rfl))
private theorem rec15744 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 461 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨461,(8),[3,7,15],[10],1185⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[823]? = some (⟨461,(8),[3,7,15],[10],1185⟩) from rfl))
private theorem rec15746 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 461 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨461,(9),[3,7,15],[10],1186⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[825]? = some (⟨461,(9),[3,7,15],[10],1186⟩) from rfl))
private theorem rec15748 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 461 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨461,(10),[3,7,15],[10],1185⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[827]? = some (⟨461,(10),[3,7,15],[10],1185⟩) from rfl))
private theorem rec15750 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 461 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨461,(11),[3,7,15],[10],1187⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[829]? = some (⟨461,(11),[3,7,15],[10],1187⟩) from rfl))
private theorem rec15752 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 462 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(0),[3,7,15],[10],1188⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[831]? = some (⟨462,(0),[3,7,15],[10],1188⟩) from rfl))
private theorem rec15754 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 462 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(1),[3,7,15],[10],1189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[833]? = some (⟨462,(1),[3,7,15],[10],1189⟩) from rfl))
private theorem rec15756 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 462 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(2),[3,7,15],[10],1190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[835]? = some (⟨462,(2),[3,7,15],[10],1190⟩) from rfl))
private theorem rec15758 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 462 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(3),[3,7,15],[10],1191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[837]? = some (⟨462,(3),[3,7,15],[10],1191⟩) from rfl))
private theorem rec15760 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 462 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨462,(4),[3,7,15],[10],1192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[839]? = some (⟨462,(4),[3,7,15],[10],1192⟩) from rfl))
private theorem rec15762 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 464 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨464,(0),[3,7,15],[10],1193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[841]? = some (⟨464,(0),[3,7,15],[10],1193⟩) from rfl))
private theorem rec15764 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 464 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨464,(1),[3,7,15],[10],1194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[843]? = some (⟨464,(1),[3,7,15],[10],1194⟩) from rfl))
private theorem rec15766 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 464 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨464,(2),[3,7,15],[10],1195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[845]? = some (⟨464,(2),[3,7,15],[10],1195⟩) from rfl))
private theorem rec15768 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 464 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨464,(3),[3,7,15],[10],1196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[847]? = some (⟨464,(3),[3,7,15],[10],1196⟩) from rfl))
private theorem rec15770 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 465 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨465,(0),[3,7,15],[10],1197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[849]? = some (⟨465,(0),[3,7,15],[10],1197⟩) from rfl))
private theorem rec15772 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 465 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨465,(1),[3,7,15],[10],1198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[851]? = some (⟨465,(1),[3,7,15],[10],1198⟩) from rfl))
private theorem rec15774 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 465 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨465,(2),[3,7,15],[10],1197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[853]? = some (⟨465,(2),[3,7,15],[10],1197⟩) from rfl))
private theorem rec15776 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 465 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨465,(3),[3,7,15],[10],1199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[855]? = some (⟨465,(3),[3,7,15],[10],1199⟩) from rfl))
private theorem rec15778 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 466 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨466,(0),[3,7,15],[10],1200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[857]? = some (⟨466,(0),[3,7,15],[10],1200⟩) from rfl))
private theorem rec15780 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 466 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨466,(1),[3,7,15],[10],1201⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[859]? = some (⟨466,(1),[3,7,15],[10],1201⟩) from rfl))
private theorem rec15782 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 466 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨466,(2),[3,7,15],[10],1202⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[861]? = some (⟨466,(2),[3,7,15],[10],1202⟩) from rfl))
private theorem rec15784 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 466 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨466,(3),[3,7,15],[10],1203⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[863]? = some (⟨466,(3),[3,7,15],[10],1203⟩) from rfl))
private theorem rec15786 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(0),[3,7,15],[10],1204⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[865]? = some (⟨468,(0),[3,7,15],[10],1204⟩) from rfl))
private theorem rec15788 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(1),[3,7,15],[10],1205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[867]? = some (⟨468,(1),[3,7,15],[10],1205⟩) from rfl))
private theorem rec15790 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(2),[3,7,15],[10],1206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[869]? = some (⟨468,(2),[3,7,15],[10],1206⟩) from rfl))
private theorem rec15792 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(3),[3,7,15],[10],1207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[871]? = some (⟨468,(3),[3,7,15],[10],1207⟩) from rfl))
private theorem rec15794 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(4),[3,7,15],[10],1208⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[873]? = some (⟨468,(4),[3,7,15],[10],1208⟩) from rfl))
private theorem rec15796 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(5),[3,7,15],[10],1205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[875]? = some (⟨468,(5),[3,7,15],[10],1205⟩) from rfl))
private theorem rec15798 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(6),[3,7,15],[10],1206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[877]? = some (⟨468,(6),[3,7,15],[10],1206⟩) from rfl))
private theorem rec15800 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(7),[3,7,15],[10],1207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[879]? = some (⟨468,(7),[3,7,15],[10],1207⟩) from rfl))
private theorem rec15802 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(8),[3,7,15],[10],1204⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[881]? = some (⟨468,(8),[3,7,15],[10],1204⟩) from rfl))
private theorem rec15804 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(9),[3,7,15],[10],1209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[883]? = some (⟨468,(9),[3,7,15],[10],1209⟩) from rfl))
private theorem rec15806 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(10),[3,7,15],[10],1206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[885]? = some (⟨468,(10),[3,7,15],[10],1206⟩) from rfl))
private theorem rec15808 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(11),[3,7,15],[10],1207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[887]? = some (⟨468,(11),[3,7,15],[10],1207⟩) from rfl))
private theorem rec15810 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(12),[3,7,15],[10],1210⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[889]? = some (⟨468,(12),[3,7,15],[10],1210⟩) from rfl))
private theorem rec15812 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(13),[3,7,15],[10],1205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[891]? = some (⟨468,(13),[3,7,15],[10],1205⟩) from rfl))
private theorem rec15814 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(14),[3,7,15],[10],1206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[893]? = some (⟨468,(14),[3,7,15],[10],1206⟩) from rfl))
private theorem rec15816 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 468 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨468,(15),[3,7,15],[10],1207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[895]? = some (⟨468,(15),[3,7,15],[10],1207⟩) from rfl))
private theorem rec15818 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(0),[3,7,15],[10],1211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[897]? = some (⟨470,(0),[3,7,15],[10],1211⟩) from rfl))
private theorem rec15820 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(1),[3,7,15],[10],1212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[899]? = some (⟨470,(1),[3,7,15],[10],1212⟩) from rfl))
private theorem rec15822 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(2),[3,7,15],[10],1213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[901]? = some (⟨470,(2),[3,7,15],[10],1213⟩) from rfl))
private theorem rec15824 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(3),[3,7,15],[10],1214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[903]? = some (⟨470,(3),[3,7,15],[10],1214⟩) from rfl))
private theorem rec15826 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(4),[3,7,15],[10],1215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[905]? = some (⟨470,(4),[3,7,15],[10],1215⟩) from rfl))
private theorem rec15828 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(5),[3,7,15],[10],1216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[907]? = some (⟨470,(5),[3,7,15],[10],1216⟩) from rfl))
private theorem rec15830 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(6),[3,7,15],[10],1217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[909]? = some (⟨470,(6),[3,7,15],[10],1217⟩) from rfl))
private theorem rec15832 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(7),[3,7,15],[10],1218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[911]? = some (⟨470,(7),[3,7,15],[10],1218⟩) from rfl))
private theorem rec15834 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(8),[3,7,15],[10],1219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[913]? = some (⟨470,(8),[3,7,15],[10],1219⟩) from rfl))
private theorem rec15836 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(9),[3,7,15],[10],1220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[915]? = some (⟨470,(9),[3,7,15],[10],1220⟩) from rfl))
private theorem rec15838 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(10),[3,7,15],[10],1221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[917]? = some (⟨470,(10),[3,7,15],[10],1221⟩) from rfl))
private theorem rec15840 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(11),[3,7,15],[10],1222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[919]? = some (⟨470,(11),[3,7,15],[10],1222⟩) from rfl))
private theorem rec15842 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(12),[3,7,15],[10],1223⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[921]? = some (⟨470,(12),[3,7,15],[10],1223⟩) from rfl))
private theorem rec15844 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(13),[3,7,15],[10],1220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[923]? = some (⟨470,(13),[3,7,15],[10],1220⟩) from rfl))
private theorem rec15846 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(14),[3,7,15],[10],1221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[925]? = some (⟨470,(14),[3,7,15],[10],1221⟩) from rfl))
private theorem rec15848 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 470 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨470,(15),[3,7,15],[10],1222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[927]? = some (⟨470,(15),[3,7,15],[10],1222⟩) from rfl))
private theorem rec15850 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 471 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(0),[3,7,15],[10],1224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[929]? = some (⟨471,(0),[3,7,15],[10],1224⟩) from rfl))
private theorem rec15852 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 471 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(1),[3,7,15],[10],1224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[931]? = some (⟨471,(1),[3,7,15],[10],1224⟩) from rfl))
private theorem rec15854 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 471 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(2),[3,7,15],[10],1225⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[933]? = some (⟨471,(2),[3,7,15],[10],1225⟩) from rfl))
private theorem rec15856 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 471 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(3),[3,7,15],[10],1225⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[935]? = some (⟨471,(3),[3,7,15],[10],1225⟩) from rfl))
private theorem rec15858 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 471 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(4),[3,7,15],[10],1226⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[937]? = some (⟨471,(4),[3,7,15],[10],1226⟩) from rfl))
private theorem rec15860 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 471 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(5),[3,7,15],[10],1226⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[939]? = some (⟨471,(5),[3,7,15],[10],1226⟩) from rfl))
private theorem rec15862 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 471 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(6),[3,7,15],[10],1227⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[941]? = some (⟨471,(6),[3,7,15],[10],1227⟩) from rfl))
private theorem rec15864 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 471 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨471,(7),[3,7,15],[10],1227⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[943]? = some (⟨471,(7),[3,7,15],[10],1227⟩) from rfl))
private theorem rec15866 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(0),[3,7,15],[10],1228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[945]? = some (⟨472,(0),[3,7,15],[10],1228⟩) from rfl))
private theorem rec15868 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(1),[3,7,15],[10],1229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[947]? = some (⟨472,(1),[3,7,15],[10],1229⟩) from rfl))
private theorem rec15870 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(2),[3,7,15],[10],1228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[949]? = some (⟨472,(2),[3,7,15],[10],1228⟩) from rfl))
private theorem rec15872 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(3),[3,7,15],[10],1230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[951]? = some (⟨472,(3),[3,7,15],[10],1230⟩) from rfl))
private theorem rec15874 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(4),[3,7,15],[10],1231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[953]? = some (⟨472,(4),[3,7,15],[10],1231⟩) from rfl))
private theorem rec15876 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(5),[3,7,15],[10],1232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[955]? = some (⟨472,(5),[3,7,15],[10],1232⟩) from rfl))
private theorem rec15878 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(6),[3,7,15],[10],1233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[957]? = some (⟨472,(6),[3,7,15],[10],1233⟩) from rfl))
private theorem rec15880 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(7),[3,7,15],[10],1234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[959]? = some (⟨472,(7),[3,7,15],[10],1234⟩) from rfl))
private theorem rec15882 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(8),[3,7,15],[10],1235⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[961]? = some (⟨472,(8),[3,7,15],[10],1235⟩) from rfl))
private theorem rec15884 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(9),[3,7,15],[10],1236⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[963]? = some (⟨472,(9),[3,7,15],[10],1236⟩) from rfl))
private theorem rec15886 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(10),[3,7,15],[10],1237⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[965]? = some (⟨472,(10),[3,7,15],[10],1237⟩) from rfl))
private theorem rec15888 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(11),[3,7,15],[10],1238⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[967]? = some (⟨472,(11),[3,7,15],[10],1238⟩) from rfl))
private theorem rec15890 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(12),[3,7,15],[10],1239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[969]? = some (⟨472,(12),[3,7,15],[10],1239⟩) from rfl))
private theorem rec15892 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(13),[3,7,15],[10],1240⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[971]? = some (⟨472,(13),[3,7,15],[10],1240⟩) from rfl))
private theorem rec15894 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(14),[3,7,15],[10],1241⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[973]? = some (⟨472,(14),[3,7,15],[10],1241⟩) from rfl))
private theorem rec15896 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(15),[3,7,15],[10],1241⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[975]? = some (⟨472,(15),[3,7,15],[10],1241⟩) from rfl))
private theorem rec15898 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(16),[3,7,15],[10],1242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[977]? = some (⟨472,(16),[3,7,15],[10],1242⟩) from rfl))
private theorem rec15900 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(17),[3,7,15],[10],1243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[979]? = some (⟨472,(17),[3,7,15],[10],1243⟩) from rfl))
private theorem rec15902 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(18),[3,7,15],[10],1244⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[981]? = some (⟨472,(18),[3,7,15],[10],1244⟩) from rfl))
private theorem rec15904 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 472 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨472,(19),[3,7,15],[10],1244⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[983]? = some (⟨472,(19),[3,7,15],[10],1244⟩) from rfl))
private theorem rec15927 (si parent : ℕ) (hs : si ∈ ([7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 475 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨475,(5),[7,15],[10],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1006]? = some (⟨475,(5),[7,15],[10],105⟩) from rfl))
private theorem rec15928 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 475 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨475,(7),[3,7,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1007]? = some (⟨475,(7),[3,7,15],[10],3⟩) from rfl))
private theorem rec15929 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 475 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨475,(8),[3,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1008]? = some (⟨475,(8),[3,15],[10],3⟩) from rfl))
private theorem rec15932 (si parent : ℕ) (hs : si ∈ ([7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 475 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨475,(9),[7,15],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1011]? = some (⟨475,(9),[7,15],[10],143⟩) from rfl))
private theorem rec15933 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 475 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨475,(15),[3,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1012]? = some (⟨475,(15),[3,15],[10],3⟩) from rfl))
private theorem rec15935 (si parent : ℕ) (hs : si ∈ ([3, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 475 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨475,(16),[3,15],[10],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1014]? = some (⟨475,(16),[3,15],[10],3⟩) from rfl))
private theorem rec15937 (si parent : ℕ) (hs : si ∈ ([3, 7, 15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 475 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨475,(17),[3,7,15],[10],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1016]? = some (⟨475,(17),[3,7,15],[10],48⟩) from rfl))
private theorem rec15939 (si parent : ℕ) (hs : si ∈ ([15] : List ℕ)) (hp : parent ∈ ([10] : List ℕ)) : section14Recorded section14Catalog si parent 475 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨475,(19),[15],[10],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part14 (List.mem_of_getElem? (show section14DataRecords4Part3[1018]? = some (⟨475,(19),[15],[10],143⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 15).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 15)).drop 0).take 16, section14Recorded section14Catalog 15 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 15 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 15).plans.drop 6).take 1 = [⟨9,413,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1])],false,[(414,⟨([1],[]),true,([1],[]),false,false,[]⟩),(415,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(416,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(417,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(418,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(419,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(420,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(421,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(422,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(423,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(424,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(425,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(426,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(427,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(428,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(429,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(430,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(431,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(432,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(433,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(434,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(435,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(436,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(437,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(438,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(439,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(440,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(441,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(442,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(443,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(444,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(445,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(446,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(447,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(448,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(449,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(450,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(451,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(452,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(453,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(459,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(460,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(461,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(462,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(463,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(464,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(465,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(466,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(467,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(468,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(469,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(470,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(471,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(472,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(475,⟨([1],[]),true,([],[]),true,false,[]⟩),(652,⟨([],[]),false,([2],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 15)).drop 0).take 16 = [⟨2,0,[⟨true,false,12⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨2,1,[⟨true,false,12⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨2,2,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,3,[⟨true,false,12⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨2,4,[⟨true,false,16⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,5,[⟨true,false,16⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,6,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨2,7,[⟨true,false,16⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,8,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,9,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,10,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨2,11,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨2,12,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨2,13,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨2,14,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨2,15,[⟨true,true,1⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec15178 15 0 (by decide) (by decide)
  · left
    exact rec15179 15 1 (by decide) (by decide)
  · left
    exact rec15179 15 2 (by decide) (by decide)
  · left
    exact rec15179 15 3 (by decide) (by decide)
  · left
    exact rec15180 15 4 (by decide) (by decide)
  · left
    exact rec15180 15 5 (by decide) (by decide)
  · left
    exact rec15180 15 6 (by decide) (by decide)
  · left
    exact rec15180 15 7 (by decide) (by decide)
  · left
    exact rec15181 15 8 (by decide) (by decide)
  · left
    exact rec15182 15 9 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(414,⟨([1],[]),true,([1],[]),false,false,[]⟩),(415,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(416,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(417,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(418,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(419,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(420,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(421,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(422,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(423,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(424,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(425,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(426,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(427,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(428,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(429,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(430,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(431,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(432,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(433,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(434,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(435,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(436,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(437,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(438,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(439,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(440,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(441,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(442,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(443,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(444,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(445,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(446,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(447,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(448,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(449,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(450,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(451,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(452,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(453,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(459,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(460,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(461,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(462,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(463,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(464,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(465,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(466,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(467,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(468,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(469,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(470,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(471,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(472,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(475,⟨([1],[]),true,([],[]),true,false,[]⟩),(652,⟨([],[]),false,([2],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 414)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 415)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15187 15 10 (by decide) (by decide)
      · right
        exact rec15189 15 10 (by decide) (by decide)
      · right
        exact rec15191 15 10 (by decide) (by decide)
      · right
        exact rec15193 15 10 (by decide) (by decide)
      · right
        exact rec15195 15 10 (by decide) (by decide)
      · right
        exact rec15197 15 10 (by decide) (by decide)
      · right
        exact rec15199 15 10 (by decide) (by decide)
      · right
        exact rec15201 15 10 (by decide) (by decide)
      · right
        exact rec15203 15 10 (by decide) (by decide)
      · right
        exact rec15205 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 416)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 417)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15207 15 10 (by decide) (by decide)
      · right
        exact rec15208 15 10 (by decide) (by decide)
      · right
        exact rec15209 15 10 (by decide) (by decide)
      · right
        exact rec15210 15 10 (by decide) (by decide)
      · right
        exact rec15211 15 10 (by decide) (by decide)
      · right
        exact rec15212 15 10 (by decide) (by decide)
      · right
        exact rec15213 15 10 (by decide) (by decide)
      · right
        exact rec15214 15 10 (by decide) (by decide)
      · right
        exact rec15215 15 10 (by decide) (by decide)
      · right
        exact rec15216 15 10 (by decide) (by decide)
      · right
        exact rec15217 15 10 (by decide) (by decide)
      · right
        exact rec15218 15 10 (by decide) (by decide)
      · right
        exact rec15219 15 10 (by decide) (by decide)
      · right
        exact rec15220 15 10 (by decide) (by decide)
      · right
        exact rec15221 15 10 (by decide) (by decide)
      · right
        exact rec15222 15 10 (by decide) (by decide)
      · right
        exact rec15223 15 10 (by decide) (by decide)
      · right
        exact rec15224 15 10 (by decide) (by decide)
      · right
        exact rec15225 15 10 (by decide) (by decide)
      · right
        exact rec15226 15 10 (by decide) (by decide)
      · right
        exact rec15227 15 10 (by decide) (by decide)
      · right
        exact rec15228 15 10 (by decide) (by decide)
      · right
        exact rec15229 15 10 (by decide) (by decide)
      · right
        exact rec15230 15 10 (by decide) (by decide)
      · right
        exact rec15231 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 418)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 419)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 420)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15232 15 10 (by decide) (by decide)
      · right
        exact rec15234 15 10 (by decide) (by decide)
      · right
        exact rec15236 15 10 (by decide) (by decide)
      · right
        exact rec15238 15 10 (by decide) (by decide)
      · right
        exact rec15240 15 10 (by decide) (by decide)
      · right
        exact rec15242 15 10 (by decide) (by decide)
      · right
        exact rec15244 15 10 (by decide) (by decide)
      · right
        exact rec15246 15 10 (by decide) (by decide)
      · right
        exact rec15248 15 10 (by decide) (by decide)
      · right
        exact rec15250 15 10 (by decide) (by decide)
      · right
        exact rec15252 15 10 (by decide) (by decide)
      · right
        exact rec15254 15 10 (by decide) (by decide)
      · right
        exact rec15256 15 10 (by decide) (by decide)
      · right
        exact rec15258 15 10 (by decide) (by decide)
      · right
        exact rec15260 15 10 (by decide) (by decide)
      · right
        exact rec15262 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 421)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 422)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 423)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15264 15 10 (by decide) (by decide)
      · right
        exact rec15266 15 10 (by decide) (by decide)
      · right
        exact rec15268 15 10 (by decide) (by decide)
      · right
        exact rec15270 15 10 (by decide) (by decide)
      · right
        exact rec15272 15 10 (by decide) (by decide)
      · right
        exact rec15274 15 10 (by decide) (by decide)
      · right
        exact rec15276 15 10 (by decide) (by decide)
      · right
        exact rec15278 15 10 (by decide) (by decide)
      · right
        exact rec15280 15 10 (by decide) (by decide)
      · right
        exact rec15282 15 10 (by decide) (by decide)
      · right
        exact rec15284 15 10 (by decide) (by decide)
      · right
        exact rec15286 15 10 (by decide) (by decide)
      · right
        exact rec15288 15 10 (by decide) (by decide)
      · right
        exact rec15290 15 10 (by decide) (by decide)
      · right
        exact rec15292 15 10 (by decide) (by decide)
      · right
        exact rec15294 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 424)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 425)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 426)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15296 15 10 (by decide) (by decide)
      · right
        exact rec15298 15 10 (by decide) (by decide)
      · right
        exact rec15300 15 10 (by decide) (by decide)
      · right
        exact rec15302 15 10 (by decide) (by decide)
      · right
        exact rec15304 15 10 (by decide) (by decide)
      · right
        exact rec15306 15 10 (by decide) (by decide)
      · right
        exact rec15308 15 10 (by decide) (by decide)
      · right
        exact rec15310 15 10 (by decide) (by decide)
      · right
        exact rec15312 15 10 (by decide) (by decide)
      · right
        exact rec15314 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 427)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 428)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15316 15 10 (by decide) (by decide)
      · right
        exact rec15318 15 10 (by decide) (by decide)
      · right
        exact rec15320 15 10 (by decide) (by decide)
      · right
        exact rec15322 15 10 (by decide) (by decide)
      · right
        exact rec15324 15 10 (by decide) (by decide)
      · right
        exact rec15326 15 10 (by decide) (by decide)
      · right
        exact rec15328 15 10 (by decide) (by decide)
      · right
        exact rec15330 15 10 (by decide) (by decide)
      · right
        exact rec15332 15 10 (by decide) (by decide)
      · right
        exact rec15334 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 429)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 430)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 431)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15336 15 10 (by decide) (by decide)
      · right
        exact rec15338 15 10 (by decide) (by decide)
      · right
        exact rec15340 15 10 (by decide) (by decide)
      · right
        exact rec15342 15 10 (by decide) (by decide)
      · right
        exact rec15344 15 10 (by decide) (by decide)
      · right
        exact rec15346 15 10 (by decide) (by decide)
      · right
        exact rec15348 15 10 (by decide) (by decide)
      · right
        exact rec15350 15 10 (by decide) (by decide)
      · right
        exact rec15352 15 10 (by decide) (by decide)
      · right
        exact rec15354 15 10 (by decide) (by decide)
      · right
        exact rec15356 15 10 (by decide) (by decide)
      · right
        exact rec15358 15 10 (by decide) (by decide)
      · right
        exact rec15360 15 10 (by decide) (by decide)
      · right
        exact rec15362 15 10 (by decide) (by decide)
      · right
        exact rec15364 15 10 (by decide) (by decide)
      · right
        exact rec15366 15 10 (by decide) (by decide)
      · right
        exact rec15368 15 10 (by decide) (by decide)
      · right
        exact rec15370 15 10 (by decide) (by decide)
      · right
        exact rec15372 15 10 (by decide) (by decide)
      · right
        exact rec15374 15 10 (by decide) (by decide)
      · right
        exact rec15376 15 10 (by decide) (by decide)
      · right
        exact rec15378 15 10 (by decide) (by decide)
      · right
        exact rec15380 15 10 (by decide) (by decide)
      · right
        exact rec15382 15 10 (by decide) (by decide)
      · right
        exact rec15384 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 432)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 433)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15386 15 10 (by decide) (by decide)
      · right
        exact rec15388 15 10 (by decide) (by decide)
      · right
        exact rec15390 15 10 (by decide) (by decide)
      · right
        exact rec15392 15 10 (by decide) (by decide)
      · right
        exact rec15394 15 10 (by decide) (by decide)
      · right
        exact rec15396 15 10 (by decide) (by decide)
      · right
        exact rec15398 15 10 (by decide) (by decide)
      · right
        exact rec15400 15 10 (by decide) (by decide)
      · right
        exact rec15402 15 10 (by decide) (by decide)
      · right
        exact rec15404 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 434)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 435)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 436)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15406 15 10 (by decide) (by decide)
      · right
        exact rec15408 15 10 (by decide) (by decide)
      · right
        exact rec15410 15 10 (by decide) (by decide)
      · right
        exact rec15412 15 10 (by decide) (by decide)
      · right
        exact rec15414 15 10 (by decide) (by decide)
      · right
        exact rec15416 15 10 (by decide) (by decide)
      · right
        exact rec15418 15 10 (by decide) (by decide)
      · right
        exact rec15420 15 10 (by decide) (by decide)
      · right
        exact rec15422 15 10 (by decide) (by decide)
      · right
        exact rec15424 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 437)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 438)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15426 15 10 (by decide) (by decide)
      · right
        exact rec15428 15 10 (by decide) (by decide)
      · right
        exact rec15430 15 10 (by decide) (by decide)
      · right
        exact rec15432 15 10 (by decide) (by decide)
      · right
        exact rec15434 15 10 (by decide) (by decide)
      · right
        exact rec15436 15 10 (by decide) (by decide)
      · right
        exact rec15438 15 10 (by decide) (by decide)
      · right
        exact rec15440 15 10 (by decide) (by decide)
      · right
        exact rec15442 15 10 (by decide) (by decide)
      · right
        exact rec15444 15 10 (by decide) (by decide)
      · right
        exact rec15446 15 10 (by decide) (by decide)
      · right
        exact rec15448 15 10 (by decide) (by decide)
      · right
        exact rec15450 15 10 (by decide) (by decide)
      · right
        exact rec15452 15 10 (by decide) (by decide)
      · right
        exact rec15454 15 10 (by decide) (by decide)
      · right
        exact rec15456 15 10 (by decide) (by decide)
      · right
        exact rec15458 15 10 (by decide) (by decide)
      · right
        exact rec15460 15 10 (by decide) (by decide)
      · right
        exact rec15462 15 10 (by decide) (by decide)
      · right
        exact rec15464 15 10 (by decide) (by decide)
      · right
        exact rec15466 15 10 (by decide) (by decide)
      · right
        exact rec15468 15 10 (by decide) (by decide)
      · right
        exact rec15470 15 10 (by decide) (by decide)
      · right
        exact rec15472 15 10 (by decide) (by decide)
      · right
        exact rec15474 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 439)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 440)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 441)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15476 15 10 (by decide) (by decide)
      · right
        exact rec15478 15 10 (by decide) (by decide)
      · right
        exact rec15480 15 10 (by decide) (by decide)
      · right
        exact rec15482 15 10 (by decide) (by decide)
      · right
        exact rec15484 15 10 (by decide) (by decide)
      · right
        exact rec15486 15 10 (by decide) (by decide)
      · right
        exact rec15488 15 10 (by decide) (by decide)
      · right
        exact rec15490 15 10 (by decide) (by decide)
      · right
        exact rec15492 15 10 (by decide) (by decide)
      · right
        exact rec15494 15 10 (by decide) (by decide)
      · right
        exact rec15496 15 10 (by decide) (by decide)
      · right
        exact rec15498 15 10 (by decide) (by decide)
      · right
        exact rec15500 15 10 (by decide) (by decide)
      · right
        exact rec15502 15 10 (by decide) (by decide)
      · right
        exact rec15504 15 10 (by decide) (by decide)
      · right
        exact rec15506 15 10 (by decide) (by decide)
      · right
        exact rec15508 15 10 (by decide) (by decide)
      · right
        exact rec15510 15 10 (by decide) (by decide)
      · right
        exact rec15512 15 10 (by decide) (by decide)
      · right
        exact rec15514 15 10 (by decide) (by decide)
      · right
        exact rec15516 15 10 (by decide) (by decide)
      · right
        exact rec15518 15 10 (by decide) (by decide)
      · right
        exact rec15520 15 10 (by decide) (by decide)
      · right
        exact rec15522 15 10 (by decide) (by decide)
      · right
        exact rec15524 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 442)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 443)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15526 15 10 (by decide) (by decide)
      · right
        exact rec15528 15 10 (by decide) (by decide)
      · right
        exact rec15530 15 10 (by decide) (by decide)
      · right
        exact rec15532 15 10 (by decide) (by decide)
      · right
        exact rec15534 15 10 (by decide) (by decide)
      · right
        exact rec15536 15 10 (by decide) (by decide)
      · right
        exact rec15538 15 10 (by decide) (by decide)
      · right
        exact rec15540 15 10 (by decide) (by decide)
      · right
        exact rec15542 15 10 (by decide) (by decide)
      · right
        exact rec15544 15 10 (by decide) (by decide)
      · right
        exact rec15546 15 10 (by decide) (by decide)
      · right
        exact rec15548 15 10 (by decide) (by decide)
      · right
        exact rec15550 15 10 (by decide) (by decide)
      · right
        exact rec15552 15 10 (by decide) (by decide)
      · right
        exact rec15554 15 10 (by decide) (by decide)
      · right
        exact rec15556 15 10 (by decide) (by decide)
      · right
        exact rec15558 15 10 (by decide) (by decide)
      · right
        exact rec15560 15 10 (by decide) (by decide)
      · right
        exact rec15562 15 10 (by decide) (by decide)
      · right
        exact rec15564 15 10 (by decide) (by decide)
      · right
        exact rec15566 15 10 (by decide) (by decide)
      · right
        exact rec15568 15 10 (by decide) (by decide)
      · right
        exact rec15570 15 10 (by decide) (by decide)
      · right
        exact rec15572 15 10 (by decide) (by decide)
      · right
        exact rec15574 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 444)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 445)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 446)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15576 15 10 (by decide) (by decide)
      · right
        exact rec15578 15 10 (by decide) (by decide)
      · right
        exact rec15580 15 10 (by decide) (by decide)
      · right
        exact rec15582 15 10 (by decide) (by decide)
      · right
        exact rec15584 15 10 (by decide) (by decide)
      · right
        exact rec15586 15 10 (by decide) (by decide)
      · right
        exact rec15588 15 10 (by decide) (by decide)
      · right
        exact rec15590 15 10 (by decide) (by decide)
      · right
        exact rec15592 15 10 (by decide) (by decide)
      · right
        exact rec15594 15 10 (by decide) (by decide)
      · right
        exact rec15596 15 10 (by decide) (by decide)
      · right
        exact rec15598 15 10 (by decide) (by decide)
      · right
        exact rec15600 15 10 (by decide) (by decide)
      · right
        exact rec15602 15 10 (by decide) (by decide)
      · right
        exact rec15604 15 10 (by decide) (by decide)
      · right
        exact rec15606 15 10 (by decide) (by decide)
      · right
        exact rec15608 15 10 (by decide) (by decide)
      · right
        exact rec15610 15 10 (by decide) (by decide)
      · right
        exact rec15612 15 10 (by decide) (by decide)
      · right
        exact rec15614 15 10 (by decide) (by decide)
      · right
        exact rec15616 15 10 (by decide) (by decide)
      · right
        exact rec15618 15 10 (by decide) (by decide)
      · right
        exact rec15620 15 10 (by decide) (by decide)
      · right
        exact rec15622 15 10 (by decide) (by decide)
      · right
        exact rec15624 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 447)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 448)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15626 15 10 (by decide) (by decide)
      · right
        exact rec15628 15 10 (by decide) (by decide)
      · right
        exact rec15630 15 10 (by decide) (by decide)
      · right
        exact rec15632 15 10 (by decide) (by decide)
      · right
        exact rec15634 15 10 (by decide) (by decide)
      · right
        exact rec15636 15 10 (by decide) (by decide)
      · right
        exact rec15638 15 10 (by decide) (by decide)
      · right
        exact rec15640 15 10 (by decide) (by decide)
      · right
        exact rec15642 15 10 (by decide) (by decide)
      · right
        exact rec15644 15 10 (by decide) (by decide)
      · right
        exact rec15646 15 10 (by decide) (by decide)
      · right
        exact rec15648 15 10 (by decide) (by decide)
      · right
        exact rec15650 15 10 (by decide) (by decide)
      · right
        exact rec15652 15 10 (by decide) (by decide)
      · right
        exact rec15654 15 10 (by decide) (by decide)
      · right
        exact rec15656 15 10 (by decide) (by decide)
      · right
        exact rec15658 15 10 (by decide) (by decide)
      · right
        exact rec15660 15 10 (by decide) (by decide)
      · right
        exact rec15662 15 10 (by decide) (by decide)
      · right
        exact rec15664 15 10 (by decide) (by decide)
      · right
        exact rec15666 15 10 (by decide) (by decide)
      · right
        exact rec15668 15 10 (by decide) (by decide)
      · right
        exact rec15670 15 10 (by decide) (by decide)
      · right
        exact rec15672 15 10 (by decide) (by decide)
      · right
        exact rec15674 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 449)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 450)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15676 15 10 (by decide) (by decide)
      · right
        exact rec15678 15 10 (by decide) (by decide)
      · right
        exact rec15680 15 10 (by decide) (by decide)
      · right
        exact rec15682 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 451)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 452)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 453)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15684 15 10 (by decide) (by decide)
      · right
        exact rec15686 15 10 (by decide) (by decide)
      · right
        exact rec15688 15 10 (by decide) (by decide)
      · right
        exact rec15690 15 10 (by decide) (by decide)
      · right
        exact rec15692 15 10 (by decide) (by decide)
      · right
        exact rec15694 15 10 (by decide) (by decide)
      · right
        exact rec15696 15 10 (by decide) (by decide)
      · right
        exact rec15699 15 10 (by decide) (by decide)
      · right
        exact rec15701 15 10 (by decide) (by decide)
      · right
        exact rec15703 15 10 (by decide) (by decide)
      · right
        exact rec15705 15 10 (by decide) (by decide)
      · right
        exact rec15707 15 10 (by decide) (by decide)
      · right
        exact rec15709 15 10 (by decide) (by decide)
      · right
        exact rec15711 15 10 (by decide) (by decide)
      · right
        exact rec15713 15 10 (by decide) (by decide)
      · right
        exact rec15715 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 459)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 460)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15734 15 10 (by decide) (by decide)
      · right
        exact rec15736 15 10 (by decide) (by decide)
      · right
        exact rec15738 15 10 (by decide) (by decide)
      · right
        exact rec15740 15 10 (by decide) (by decide)
      · right
        exact rec15742 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 461)).length = 20 := by decide +kernel
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
      · right
        exact rec15744 15 10 (by decide) (by decide)
      · right
        exact rec15746 15 10 (by decide) (by decide)
      · right
        exact rec15748 15 10 (by decide) (by decide)
      · right
        exact rec15750 15 10 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · left
        decide +kernel
      · left
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 462)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15752 15 10 (by decide) (by decide)
      · right
        exact rec15754 15 10 (by decide) (by decide)
      · right
        exact rec15756 15 10 (by decide) (by decide)
      · right
        exact rec15758 15 10 (by decide) (by decide)
      · right
        exact rec15760 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 463)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 464)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15762 15 10 (by decide) (by decide)
      · right
        exact rec15764 15 10 (by decide) (by decide)
      · right
        exact rec15766 15 10 (by decide) (by decide)
      · right
        exact rec15768 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 465)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15770 15 10 (by decide) (by decide)
      · right
        exact rec15772 15 10 (by decide) (by decide)
      · right
        exact rec15774 15 10 (by decide) (by decide)
      · right
        exact rec15776 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 466)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15778 15 10 (by decide) (by decide)
      · right
        exact rec15780 15 10 (by decide) (by decide)
      · right
        exact rec15782 15 10 (by decide) (by decide)
      · right
        exact rec15784 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 467)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 468)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15786 15 10 (by decide) (by decide)
      · right
        exact rec15788 15 10 (by decide) (by decide)
      · right
        exact rec15790 15 10 (by decide) (by decide)
      · right
        exact rec15792 15 10 (by decide) (by decide)
      · right
        exact rec15794 15 10 (by decide) (by decide)
      · right
        exact rec15796 15 10 (by decide) (by decide)
      · right
        exact rec15798 15 10 (by decide) (by decide)
      · right
        exact rec15800 15 10 (by decide) (by decide)
      · right
        exact rec15802 15 10 (by decide) (by decide)
      · right
        exact rec15804 15 10 (by decide) (by decide)
      · right
        exact rec15806 15 10 (by decide) (by decide)
      · right
        exact rec15808 15 10 (by decide) (by decide)
      · right
        exact rec15810 15 10 (by decide) (by decide)
      · right
        exact rec15812 15 10 (by decide) (by decide)
      · right
        exact rec15814 15 10 (by decide) (by decide)
      · right
        exact rec15816 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 469)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 470)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15818 15 10 (by decide) (by decide)
      · right
        exact rec15820 15 10 (by decide) (by decide)
      · right
        exact rec15822 15 10 (by decide) (by decide)
      · right
        exact rec15824 15 10 (by decide) (by decide)
      · right
        exact rec15826 15 10 (by decide) (by decide)
      · right
        exact rec15828 15 10 (by decide) (by decide)
      · right
        exact rec15830 15 10 (by decide) (by decide)
      · right
        exact rec15832 15 10 (by decide) (by decide)
      · right
        exact rec15834 15 10 (by decide) (by decide)
      · right
        exact rec15836 15 10 (by decide) (by decide)
      · right
        exact rec15838 15 10 (by decide) (by decide)
      · right
        exact rec15840 15 10 (by decide) (by decide)
      · right
        exact rec15842 15 10 (by decide) (by decide)
      · right
        exact rec15844 15 10 (by decide) (by decide)
      · right
        exact rec15846 15 10 (by decide) (by decide)
      · right
        exact rec15848 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 471)).length = 8 := by decide +kernel
      have hjj : j < 8 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15850 15 10 (by decide) (by decide)
      · right
        exact rec15852 15 10 (by decide) (by decide)
      · right
        exact rec15854 15 10 (by decide) (by decide)
      · right
        exact rec15856 15 10 (by decide) (by decide)
      · right
        exact rec15858 15 10 (by decide) (by decide)
      · right
        exact rec15860 15 10 (by decide) (by decide)
      · right
        exact rec15862 15 10 (by decide) (by decide)
      · right
        exact rec15864 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 472)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec15866 15 10 (by decide) (by decide)
      · right
        exact rec15868 15 10 (by decide) (by decide)
      · right
        exact rec15870 15 10 (by decide) (by decide)
      · right
        exact rec15872 15 10 (by decide) (by decide)
      · right
        exact rec15874 15 10 (by decide) (by decide)
      · right
        exact rec15876 15 10 (by decide) (by decide)
      · right
        exact rec15878 15 10 (by decide) (by decide)
      · right
        exact rec15880 15 10 (by decide) (by decide)
      · right
        exact rec15882 15 10 (by decide) (by decide)
      · right
        exact rec15884 15 10 (by decide) (by decide)
      · right
        exact rec15886 15 10 (by decide) (by decide)
      · right
        exact rec15888 15 10 (by decide) (by decide)
      · right
        exact rec15890 15 10 (by decide) (by decide)
      · right
        exact rec15892 15 10 (by decide) (by decide)
      · right
        exact rec15894 15 10 (by decide) (by decide)
      · right
        exact rec15896 15 10 (by decide) (by decide)
      · right
        exact rec15898 15 10 (by decide) (by decide)
      · right
        exact rec15900 15 10 (by decide) (by decide)
      · right
        exact rec15902 15 10 (by decide) (by decide)
      · right
        exact rec15904 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 475)).length = 20 := by decide +kernel
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
        exact rec15927 15 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec15928 15 10 (by decide) (by decide)
      · right
        exact rec15929 15 10 (by decide) (by decide)
      · right
        exact rec15932 15 10 (by decide) (by decide)
      · left
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
        exact rec15933 15 10 (by decide) (by decide)
      · right
        exact rec15935 15 10 (by decide) (by decide)
      · right
        exact rec15937 15 10 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec15939 15 10 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 652)).length = 4 := by decide +kernel
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
  · left
    exact rec15183 15 11 (by decide) (by decide)
  · left
    exact rec15184 15 12 (by decide) (by decide)
  · left
    exact rec15184 15 13 (by decide) (by decide)
  · left
    exact rec15184 15 14 (by decide) (by decide)
  · left
    exact rec15184 15 15 (by decide) (by decide)
end Section14Coverage_15_6_p0_16

#print axioms solution
