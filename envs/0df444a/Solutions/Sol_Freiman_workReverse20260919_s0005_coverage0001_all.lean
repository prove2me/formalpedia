-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_coverage0001_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:37:30.11298+00:00
-- url     : https://prove2.me/submissions/0a96460f-351f-44be-ba55-2f8d847e3631

import Definitions.Def_Freiman_section14Data
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0000_0016
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p0_16
private theorem rec359 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 9, 10, 13, 14] : List ℕ)) (hp : parent ∈ ([2, 3, 6, 7, 18, 19, 22, 23] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[359]? = some (⟨16,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) from rfl))
private theorem rec360 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 9, 10, 13, 14] : List ℕ)) (hp : parent ∈ ([1] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,9,10,13,14],[1],57⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[360]? = some (⟨16,(-1),[1,2,5,6,9,10,13,14],[1],57⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec363 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([5, 21] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[5,21],58⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[363]? = some (⟨16,(-1),[1,2,5,6,13,14],[5,21],58⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec389 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([4, 20] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,13,14],[4,20],58⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[389]? = some (⟨16,(-1),[1,2,5,13,14],[4,20],58⟩) from rfl))
private theorem rec395 (si parent : ℕ) (hs : si ∈ ([1, 5, 9, 13] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,5,9,13],[0],57⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[395]? = some (⟨16,(-1),[1,5,9,13],[0],57⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0000_0016 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 0).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 0).take 16 = [⟨1,0,[⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,1,[⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,2,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,3,[⟨true,true,1⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,4,[⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,5,[⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,6,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,7,[⟨true,true,1⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,8,[⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,9,[⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,10,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,11,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,12,[⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,13,[⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,14,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,15,[⟨true,true,1⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec395 5 0 (by decide) (by decide)
  · left
    exact rec360 5 1 (by decide) (by decide)
  · left
    exact rec359 5 2 (by decide) (by decide)
  · left
    exact rec359 5 3 (by decide) (by decide)
  · left
    exact rec389 5 4 (by decide) (by decide)
  · left
    exact rec363 5 5 (by decide) (by decide)
  · left
    exact rec359 5 6 (by decide) (by decide)
  · left
    exact rec359 5 7 (by decide) (by decide)
  · left
    exact rec362 5 8 (by decide) (by decide)
  · left
    exact rec362 5 9 (by decide) (by decide)
  · left
    exact rec388 5 10 (by decide) (by decide)
  · left
    exact rec388 5 11 (by decide) (by decide)
  · left
    exact rec362 5 12 (by decide) (by decide)
  · left
    exact rec362 5 13 (by decide) (by decide)
  · left
    exact rec388 5 14 (by decide) (by decide)
  · left
    exact rec388 5 15 (by decide) (by decide)
end Section14Coverage_5_1_p0_16

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0000_0016


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0016_0032
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p16_32
private theorem rec359 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 9, 10, 13, 14] : List ℕ)) (hp : parent ∈ ([2, 3, 6, 7, 18, 19, 22, 23] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[359]? = some (⟨16,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec363 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([5, 21] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[5,21],58⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[363]? = some (⟨16,(-1),[1,2,5,6,13,14],[5,21],58⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec389 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([4, 20] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,13,14],[4,20],58⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[389]? = some (⟨16,(-1),[1,2,5,13,14],[4,20],58⟩) from rfl))
private theorem rec396 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([16, 17] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,5,13],[16,17],59⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[396]? = some (⟨16,(-1),[1,5,13],[16,17],59⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0016_0032 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 16).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 16).take 16 = [⟨1,16,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,17,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,18,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,19,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,20,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,21,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,22,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,23,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,24,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,25,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,26,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,27,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,28,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,29,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,30,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,31,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec396 5 16 (by decide) (by decide)
  · left
    exact rec396 5 17 (by decide) (by decide)
  · left
    exact rec359 5 18 (by decide) (by decide)
  · left
    exact rec359 5 19 (by decide) (by decide)
  · left
    exact rec389 5 20 (by decide) (by decide)
  · left
    exact rec363 5 21 (by decide) (by decide)
  · left
    exact rec359 5 22 (by decide) (by decide)
  · left
    exact rec359 5 23 (by decide) (by decide)
  · left
    exact rec362 5 24 (by decide) (by decide)
  · left
    exact rec362 5 25 (by decide) (by decide)
  · left
    exact rec388 5 26 (by decide) (by decide)
  · left
    exact rec388 5 27 (by decide) (by decide)
  · left
    exact rec362 5 28 (by decide) (by decide)
  · left
    exact rec362 5 29 (by decide) (by decide)
  · left
    exact rec388 5 30 (by decide) (by decide)
  · left
    exact rec388 5 31 (by decide) (by decide)
end Section14Coverage_5_1_p16_32

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0016_0032


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0032_0048
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p32_48
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec364 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([41, 57] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[41,57],60⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[364]? = some (⟨16,(-1),[1,2,5,6,13,14],[41,57],60⟩) from rfl))
private theorem rec365 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([45] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[45],61⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[365]? = some (⟨16,(-1),[1,2,5,6,13,14],[45],61⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec397 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([40, 56] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,5,13],[40,56],60⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[397]? = some (⟨16,(-1),[1,5,13],[40,56],60⟩) from rfl))
private theorem rec398 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([44] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,5,13],[44],61⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[398]? = some (⟨16,(-1),[1,5,13],[44],61⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0032_0048 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 32).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 32).take 16 = [⟨1,32,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,33,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,34,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,35,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,36,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,37,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,38,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,39,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,40,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,41,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,42,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,43,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,44,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,45,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,46,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,47,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec362 5 32 (by decide) (by decide)
  · left
    exact rec362 5 33 (by decide) (by decide)
  · left
    exact rec388 5 34 (by decide) (by decide)
  · left
    exact rec388 5 35 (by decide) (by decide)
  · left
    exact rec362 5 36 (by decide) (by decide)
  · left
    exact rec362 5 37 (by decide) (by decide)
  · left
    exact rec388 5 38 (by decide) (by decide)
  · left
    exact rec388 5 39 (by decide) (by decide)
  · left
    exact rec397 5 40 (by decide) (by decide)
  · left
    exact rec364 5 41 (by decide) (by decide)
  · left
    exact rec361 5 42 (by decide) (by decide)
  · left
    exact rec361 5 43 (by decide) (by decide)
  · left
    exact rec398 5 44 (by decide) (by decide)
  · left
    exact rec365 5 45 (by decide) (by decide)
  · left
    exact rec361 5 46 (by decide) (by decide)
  · left
    exact rec361 5 47 (by decide) (by decide)
end Section14Coverage_5_1_p32_48

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0032_0048


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0048_0064
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p48_64
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec364 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([41, 57] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[41,57],60⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[364]? = some (⟨16,(-1),[1,2,5,6,13,14],[41,57],60⟩) from rfl))
private theorem rec366 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([61] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[61],62⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[366]? = some (⟨16,(-1),[1,2,5,6,13,14],[61],62⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec397 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([40, 56] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,5,13],[40,56],60⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[397]? = some (⟨16,(-1),[1,5,13],[40,56],60⟩) from rfl))
private theorem rec399 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([60] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,5,13],[60],62⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[399]? = some (⟨16,(-1),[1,5,13],[60],62⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0048_0064 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 48).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 48).take 16 = [⟨1,48,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,49,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,50,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,51,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,52,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,53,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,54,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,55,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,56,[⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,57,[⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,58,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,59,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,60,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,61,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,62,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,63,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec362 5 48 (by decide) (by decide)
  · left
    exact rec362 5 49 (by decide) (by decide)
  · left
    exact rec388 5 50 (by decide) (by decide)
  · left
    exact rec388 5 51 (by decide) (by decide)
  · left
    exact rec362 5 52 (by decide) (by decide)
  · left
    exact rec362 5 53 (by decide) (by decide)
  · left
    exact rec388 5 54 (by decide) (by decide)
  · left
    exact rec388 5 55 (by decide) (by decide)
  · left
    exact rec397 5 56 (by decide) (by decide)
  · left
    exact rec364 5 57 (by decide) (by decide)
  · left
    exact rec361 5 58 (by decide) (by decide)
  · left
    exact rec361 5 59 (by decide) (by decide)
  · left
    exact rec399 5 60 (by decide) (by decide)
  · left
    exact rec366 5 61 (by decide) (by decide)
  · left
    exact rec361 5 62 (by decide) (by decide)
  · left
    exact rec361 5 63 (by decide) (by decide)
end Section14Coverage_5_1_p48_64

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0048_0064


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0064_0080
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p64_80
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec367 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([64] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[64],63⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[367]? = some (⟨16,(-1),[1,2,5,6,13,14],[64],63⟩) from rfl))
private theorem rec368 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([65] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[65],64⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[368]? = some (⟨16,(-1),[1,2,5,6,13,14],[65],64⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec443 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([68] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[5,6],[68],1394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[443]? = some (⟨16,(-1),[5,6],[68],1394⟩) from rfl))
private theorem rec444 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([69] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[5,6],[69],1395⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[444]? = some (⟨16,(-1),[5,6],[69],1395⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0064_0080 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 64).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 64).take 16 = [⟨1,64,[⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,65,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,66,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,67,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,68,[⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,69,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,70,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,71,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,72,[⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,73,[⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,74,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,75,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,76,[⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,77,[⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,78,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,79,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec367 5 64 (by decide) (by decide)
  · left
    exact rec368 5 65 (by decide) (by decide)
  · left
    exact rec361 5 66 (by decide) (by decide)
  · left
    exact rec361 5 67 (by decide) (by decide)
  · left
    exact rec443 5 68 (by decide) (by decide)
  · left
    exact rec444 5 69 (by decide) (by decide)
  · left
    exact rec361 5 70 (by decide) (by decide)
  · left
    exact rec361 5 71 (by decide) (by decide)
  · left
    exact rec362 5 72 (by decide) (by decide)
  · left
    exact rec362 5 73 (by decide) (by decide)
  · left
    exact rec388 5 74 (by decide) (by decide)
  · left
    exact rec388 5 75 (by decide) (by decide)
  · left
    exact rec362 5 76 (by decide) (by decide)
  · left
    exact rec362 5 77 (by decide) (by decide)
  · left
    exact rec388 5 78 (by decide) (by decide)
  · left
    exact rec388 5 79 (by decide) (by decide)
end Section14Coverage_5_1_p64_80

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0064_0080


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0080_0096
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p80_96
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec369 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([80, 84] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[80,84],65⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[369]? = some (⟨16,(-1),[1,2,5,6,13,14],[80,84],65⟩) from rfl))
private theorem rec370 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([81, 85] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[81,85],66⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[370]? = some (⟨16,(-1),[1,2,5,6,13,14],[81,85],66⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0080_0096 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 80).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 80).take 16 = [⟨1,80,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,81,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,82,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,83,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,84,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,85,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,86,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,87,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,88,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,89,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,90,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,91,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,92,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,93,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,94,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,95,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec369 5 80 (by decide) (by decide)
  · left
    exact rec370 5 81 (by decide) (by decide)
  · left
    exact rec361 5 82 (by decide) (by decide)
  · left
    exact rec361 5 83 (by decide) (by decide)
  · left
    exact rec369 5 84 (by decide) (by decide)
  · left
    exact rec370 5 85 (by decide) (by decide)
  · left
    exact rec361 5 86 (by decide) (by decide)
  · left
    exact rec361 5 87 (by decide) (by decide)
  · left
    exact rec362 5 88 (by decide) (by decide)
  · left
    exact rec362 5 89 (by decide) (by decide)
  · left
    exact rec388 5 90 (by decide) (by decide)
  · left
    exact rec388 5 91 (by decide) (by decide)
  · left
    exact rec362 5 92 (by decide) (by decide)
  · left
    exact rec362 5 93 (by decide) (by decide)
  · left
    exact rec388 5 94 (by decide) (by decide)
  · left
    exact rec388 5 95 (by decide) (by decide)
end Section14Coverage_5_1_p80_96

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0080_0096


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0096_0112
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p96_112
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec371 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([104, 120] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[104,120],67⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[371]? = some (⟨16,(-1),[1,2,5,6,13,14],[104,120],67⟩) from rfl))
private theorem rec372 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([105, 121] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[105,121],68⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[372]? = some (⟨16,(-1),[1,2,5,6,13,14],[105,121],68⟩) from rfl))
private theorem rec373 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([108] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[108],69⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[373]? = some (⟨16,(-1),[1,2,5,6,13,14],[108],69⟩) from rfl))
private theorem rec374 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([109] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[109],70⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[374]? = some (⟨16,(-1),[1,2,5,6,13,14],[109],70⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0096_0112 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 96).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 96).take 16 = [⟨1,96,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,97,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,98,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,99,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,100,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,101,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,102,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,103,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,104,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,105,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,106,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,107,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,108,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,109,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,110,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,111,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec362 5 96 (by decide) (by decide)
  · left
    exact rec362 5 97 (by decide) (by decide)
  · left
    exact rec388 5 98 (by decide) (by decide)
  · left
    exact rec388 5 99 (by decide) (by decide)
  · left
    exact rec362 5 100 (by decide) (by decide)
  · left
    exact rec362 5 101 (by decide) (by decide)
  · left
    exact rec388 5 102 (by decide) (by decide)
  · left
    exact rec388 5 103 (by decide) (by decide)
  · left
    exact rec371 5 104 (by decide) (by decide)
  · left
    exact rec372 5 105 (by decide) (by decide)
  · left
    exact rec361 5 106 (by decide) (by decide)
  · left
    exact rec361 5 107 (by decide) (by decide)
  · left
    exact rec373 5 108 (by decide) (by decide)
  · left
    exact rec374 5 109 (by decide) (by decide)
  · left
    exact rec361 5 110 (by decide) (by decide)
  · left
    exact rec361 5 111 (by decide) (by decide)
end Section14Coverage_5_1_p96_112

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0096_0112


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0112_0128
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p112_128
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec371 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([104, 120] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[104,120],67⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[371]? = some (⟨16,(-1),[1,2,5,6,13,14],[104,120],67⟩) from rfl))
private theorem rec372 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([105, 121] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[105,121],68⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[372]? = some (⟨16,(-1),[1,2,5,6,13,14],[105,121],68⟩) from rfl))
private theorem rec375 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([124] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[124],71⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[375]? = some (⟨16,(-1),[1,2,5,6,13,14],[124],71⟩) from rfl))
private theorem rec376 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([125] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[125],72⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[376]? = some (⟨16,(-1),[1,2,5,6,13,14],[125],72⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0112_0128 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 112).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 112).take 16 = [⟨1,112,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,113,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,114,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,115,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,116,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,117,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,118,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,119,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,120,[⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,121,[⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,122,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,123,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,124,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,125,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,126,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,127,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec362 5 112 (by decide) (by decide)
  · left
    exact rec362 5 113 (by decide) (by decide)
  · left
    exact rec388 5 114 (by decide) (by decide)
  · left
    exact rec388 5 115 (by decide) (by decide)
  · left
    exact rec362 5 116 (by decide) (by decide)
  · left
    exact rec362 5 117 (by decide) (by decide)
  · left
    exact rec388 5 118 (by decide) (by decide)
  · left
    exact rec388 5 119 (by decide) (by decide)
  · left
    exact rec371 5 120 (by decide) (by decide)
  · left
    exact rec372 5 121 (by decide) (by decide)
  · left
    exact rec361 5 122 (by decide) (by decide)
  · left
    exact rec361 5 123 (by decide) (by decide)
  · left
    exact rec375 5 124 (by decide) (by decide)
  · left
    exact rec376 5 125 (by decide) (by decide)
  · left
    exact rec361 5 126 (by decide) (by decide)
  · left
    exact rec361 5 127 (by decide) (by decide)
end Section14Coverage_5_1_p112_128

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0112_0128


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0128_0144
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p128_144
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec493 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[493]? = some (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec496 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[496]? = some (⟨18,(0),[1,5],[130],73⟩) from rfl))
private theorem rec497 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[497]? = some (⟨18,(0),[1,5],[134],125⟩) from rfl))
private theorem rec498 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[498]? = some (⟨18,(0),[1,5,13],[135],125⟩) from rfl))
private theorem rec510 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[510]? = some (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec513 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[513]? = some (⟨18,(1),[1,5],[130],73⟩) from rfl))
private theorem rec514 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[514]? = some (⟨18,(1),[1,5],[134],125⟩) from rfl))
private theorem rec515 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[515]? = some (⟨18,(1),[1,5,13],[135],125⟩) from rfl))
private theorem rec527 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[527]? = some (⟨18,(2),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec530 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[530]? = some (⟨18,(2),[1,5],[130],73⟩) from rfl))
private theorem rec531 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[531]? = some (⟨18,(2),[1,5],[134],125⟩) from rfl))
private theorem rec532 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[532]? = some (⟨18,(2),[1,5,13],[135],125⟩) from rfl))
private theorem rec544 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[544]? = some (⟨18,(3),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec547 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[547]? = some (⟨18,(3),[1,5],[130],73⟩) from rfl))
private theorem rec548 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[548]? = some (⟨18,(3),[1,5],[134],125⟩) from rfl))
private theorem rec549 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[549]? = some (⟨18,(3),[1,5,13],[135],125⟩) from rfl))
private theorem rec561 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[561]? = some (⟨18,(4),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec564 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,5],[130],73⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[564]? = some (⟨18,(4),[1,5],[130],73⟩) from rfl))
private theorem rec565 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,5],[134],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[565]? = some (⟨18,(4),[1,5],[134],125⟩) from rfl))
private theorem rec566 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,5,13],[135],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[566]? = some (⟨18,(4),[1,5,13],[135],125⟩) from rfl))
private theorem rec578 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[578]? = some (⟨18,(5),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec581 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[581]? = some (⟨18,(5),[1,5],[130],74⟩) from rfl))
private theorem rec582 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[582]? = some (⟨18,(5),[1,5],[134],126⟩) from rfl))
private theorem rec583 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[583]? = some (⟨18,(5),[1,5,13],[135],126⟩) from rfl))
private theorem rec595 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[595]? = some (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec598 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[598]? = some (⟨18,(6),[1,5],[130],74⟩) from rfl))
private theorem rec599 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[599]? = some (⟨18,(6),[1,5],[134],126⟩) from rfl))
private theorem rec600 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[600]? = some (⟨18,(6),[1,5,13],[135],126⟩) from rfl))
private theorem rec612 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[612]? = some (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec615 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[615]? = some (⟨18,(7),[1,5],[130],74⟩) from rfl))
private theorem rec616 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[616]? = some (⟨18,(7),[1,5],[134],126⟩) from rfl))
private theorem rec617 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[617]? = some (⟨18,(7),[1,5,13],[135],126⟩) from rfl))
private theorem rec629 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[629]? = some (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec632 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[632]? = some (⟨18,(8),[1,5],[130],74⟩) from rfl))
private theorem rec633 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[633]? = some (⟨18,(8),[1,5],[134],126⟩) from rfl))
private theorem rec634 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[634]? = some (⟨18,(8),[1,5,13],[135],126⟩) from rfl))
private theorem rec646 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[646]? = some (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec649 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,5],[130],74⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[649]? = some (⟨18,(9),[1,5],[130],74⟩) from rfl))
private theorem rec650 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,5],[134],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[650]? = some (⟨18,(9),[1,5],[134],126⟩) from rfl))
private theorem rec651 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,5,13],[135],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[651]? = some (⟨18,(9),[1,5,13],[135],126⟩) from rfl))
private theorem rec663 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[663]? = some (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec666 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,5],[130],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[666]? = some (⟨18,(10),[1,5],[130],75⟩) from rfl))
private theorem rec667 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,5],[134],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[667]? = some (⟨18,(10),[1,5],[134],127⟩) from rfl))
private theorem rec668 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,5,13],[135],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[668]? = some (⟨18,(10),[1,5,13],[135],127⟩) from rfl))
private theorem rec680 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[680]? = some (⟨18,(11),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec683 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,5],[130],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[683]? = some (⟨18,(11),[1,5],[130],76⟩) from rfl))
private theorem rec684 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,5],[134],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[684]? = some (⟨18,(11),[1,5],[134],128⟩) from rfl))
private theorem rec685 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,5,13],[135],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[685]? = some (⟨18,(11),[1,5,13],[135],128⟩) from rfl))
private theorem rec697 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,2,5,6,13,14],[131],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[697]? = some (⟨18,(12),[1,2,5,6,13,14],[131],110⟩) from rfl))
private theorem rec700 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,5],[130],77⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[700]? = some (⟨18,(12),[1,5],[130],77⟩) from rfl))
private theorem rec701 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,5],[134],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[701]? = some (⟨18,(12),[1,5],[134],129⟩) from rfl))
private theorem rec702 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,5,13],[135],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[702]? = some (⟨18,(12),[1,5,13],[135],129⟩) from rfl))
private theorem rec714 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[714]? = some (⟨18,(13),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec717 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,5],[130],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[717]? = some (⟨18,(13),[1,5],[130],76⟩) from rfl))
private theorem rec718 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,5],[134],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[718]? = some (⟨18,(13),[1,5],[134],128⟩) from rfl))
private theorem rec719 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,5,13],[135],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[719]? = some (⟨18,(13),[1,5,13],[135],128⟩) from rfl))
private theorem rec731 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,2,5,6,13,14],[131],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[731]? = some (⟨18,(14),[1,2,5,6,13,14],[131],111⟩) from rfl))
private theorem rec734 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,5],[130],78⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[734]? = some (⟨18,(14),[1,5],[130],78⟩) from rfl))
private theorem rec735 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,5],[134],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[735]? = some (⟨18,(14),[1,5],[134],130⟩) from rfl))
private theorem rec736 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,5,13],[135],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[736]? = some (⟨18,(14),[1,5,13],[135],130⟩) from rfl))
private theorem rec748 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[748]? = some (⟨18,(15),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec751 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,5],[130],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[751]? = some (⟨18,(15),[1,5],[130],75⟩) from rfl))
private theorem rec752 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,5],[134],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[752]? = some (⟨18,(15),[1,5],[134],127⟩) from rfl))
private theorem rec753 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,5,13],[135],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[753]? = some (⟨18,(15),[1,5,13],[135],127⟩) from rfl))
private theorem rec765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[765]? = some (⟨18,(16),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec768 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,5],[130],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[768]? = some (⟨18,(16),[1,5],[130],79⟩) from rfl))
private theorem rec769 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,5],[134],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[769]? = some (⟨18,(16),[1,5],[134],131⟩) from rfl))
private theorem rec770 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,5,13],[135],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[770]? = some (⟨18,(16),[1,5,13],[135],131⟩) from rfl))
private theorem rec782 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[782]? = some (⟨18,(17),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec785 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,5],[130],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[785]? = some (⟨18,(17),[1,5],[130],79⟩) from rfl))
private theorem rec786 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,5],[134],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[786]? = some (⟨18,(17),[1,5],[134],131⟩) from rfl))
private theorem rec787 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,5,13],[135],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[787]? = some (⟨18,(17),[1,5,13],[135],131⟩) from rfl))
private theorem rec799 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[799]? = some (⟨18,(18),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec802 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,5],[130],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[802]? = some (⟨18,(18),[1,5],[130],79⟩) from rfl))
private theorem rec803 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,5],[134],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[803]? = some (⟨18,(18),[1,5],[134],131⟩) from rfl))
private theorem rec804 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,5,13],[135],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[804]? = some (⟨18,(18),[1,5,13],[135],131⟩) from rfl))
private theorem rec816 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[816]? = some (⟨18,(19),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec819 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,5],[130],79⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[819]? = some (⟨18,(19),[1,5],[130],79⟩) from rfl))
private theorem rec820 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,5],[134],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[820]? = some (⟨18,(19),[1,5],[134],131⟩) from rfl))
private theorem rec821 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,5,13],[135],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[821]? = some (⟨18,(19),[1,5,13],[135],131⟩) from rfl))
private theorem rec833 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[833]? = some (⟨18,(20),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec836 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,5],[130],75⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[836]? = some (⟨18,(20),[1,5],[130],75⟩) from rfl))
private theorem rec837 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,5],[134],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[837]? = some (⟨18,(20),[1,5],[134],127⟩) from rfl))
private theorem rec838 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,5,13],[135],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[838]? = some (⟨18,(20),[1,5,13],[135],127⟩) from rfl))
private theorem rec850 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[850]? = some (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec853 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,5],[130],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[853]? = some (⟨18,(21),[1,5],[130],76⟩) from rfl))
private theorem rec854 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,5],[134],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[854]? = some (⟨18,(21),[1,5],[134],128⟩) from rfl))
private theorem rec855 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,5,13],[135],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[855]? = some (⟨18,(21),[1,5,13],[135],128⟩) from rfl))
private theorem rec867 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[867]? = some (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) from rfl))
private theorem rec870 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,5],[130],77⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[870]? = some (⟨18,(22),[1,5],[130],77⟩) from rfl))
private theorem rec871 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,5],[134],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[871]? = some (⟨18,(22),[1,5],[134],129⟩) from rfl))
private theorem rec872 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,5,13],[135],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[872]? = some (⟨18,(22),[1,5,13],[135],129⟩) from rfl))
private theorem rec884 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[884]? = some (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec887 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,5],[130],76⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[887]? = some (⟨18,(23),[1,5],[130],76⟩) from rfl))
private theorem rec888 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,5],[134],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[888]? = some (⟨18,(23),[1,5],[134],128⟩) from rfl))
private theorem rec889 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,5,13],[135],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[889]? = some (⟨18,(23),[1,5,13],[135],128⟩) from rfl))
private theorem rec901 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,2,5,6,13,14],[131],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[901]? = some (⟨18,(24),[1,2,5,6,13,14],[131],111⟩) from rfl))
private theorem rec904 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,5],[130],78⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[904]? = some (⟨18,(24),[1,5],[130],78⟩) from rfl))
private theorem rec905 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,5],[134],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[905]? = some (⟨18,(24),[1,5],[134],130⟩) from rfl))
private theorem rec906 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,5,13],[135],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[906]? = some (⟨18,(24),[1,5,13],[135],130⟩) from rfl))
private theorem rec918 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[918]? = some (⟨20,(0),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[919]? = some (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec922 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[922]? = some (⟨20,(0),[1,5],[134],3⟩) from rfl))
private theorem rec923 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[923]? = some (⟨20,(0),[1,5,13],[135],3⟩) from rfl))
private theorem rec929 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[929]? = some (⟨20,(1),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[930]? = some (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec933 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[933]? = some (⟨20,(1),[1,5],[134],3⟩) from rfl))
private theorem rec934 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[934]? = some (⟨20,(1),[1,5,13],[135],3⟩) from rfl))
private theorem rec940 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[940]? = some (⟨20,(2),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec941 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[941]? = some (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec944 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[944]? = some (⟨20,(2),[1,5],[134],3⟩) from rfl))
private theorem rec945 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[945]? = some (⟨20,(2),[1,5,13],[135],3⟩) from rfl))
private theorem rec951 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[951]? = some (⟨20,(3),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec952 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[952]? = some (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec955 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[955]? = some (⟨20,(3),[1,5],[134],3⟩) from rfl))
private theorem rec956 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[956]? = some (⟨20,(3),[1,5,13],[135],3⟩) from rfl))
private theorem rec962 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[962]? = some (⟨20,(4),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec963 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[963]? = some (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec966 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[966]? = some (⟨20,(4),[1,5],[134],3⟩) from rfl))
private theorem rec967 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[967]? = some (⟨20,(4),[1,5,13],[135],3⟩) from rfl))
private theorem rec973 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[973]? = some (⟨20,(5),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[974]? = some (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec977 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[977]? = some (⟨20,(5),[1,5],[134],3⟩) from rfl))
private theorem rec978 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[978]? = some (⟨20,(5),[1,5,13],[135],3⟩) from rfl))
private theorem rec984 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[984]? = some (⟨20,(6),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec985 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[985]? = some (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec988 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[988]? = some (⟨20,(6),[1,5],[134],3⟩) from rfl))
private theorem rec989 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[989]? = some (⟨20,(6),[1,5,13],[135],3⟩) from rfl))
private theorem rec995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[995]? = some (⟨20,(7),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec996 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[996]? = some (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec999 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[999]? = some (⟨20,(7),[1,5],[134],3⟩) from rfl))
private theorem rec1000 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1000]? = some (⟨20,(7),[1,5,13],[135],3⟩) from rfl))
private theorem rec1006 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1006]? = some (⟨20,(8),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1007 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1007]? = some (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1010 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1010]? = some (⟨20,(8),[1,5],[134],3⟩) from rfl))
private theorem rec1011 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1011]? = some (⟨20,(8),[1,5,13],[135],3⟩) from rfl))
private theorem rec1017 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1017]? = some (⟨20,(9),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1018 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1018]? = some (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1021 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1021]? = some (⟨20,(9),[1,5],[134],3⟩) from rfl))
private theorem rec1022 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1022]? = some (⟨20,(9),[1,5,13],[135],3⟩) from rfl))
private theorem rec1028 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1028]? = some (⟨20,(10),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1029 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1029]? = some (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1032 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1032]? = some (⟨20,(10),[1,5],[134],3⟩) from rfl))
private theorem rec1033 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1033]? = some (⟨20,(10),[1,5,13],[135],3⟩) from rfl))
private theorem rec1039 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1039]? = some (⟨20,(11),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1040 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1040]? = some (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1043 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1043]? = some (⟨20,(11),[1,5],[134],3⟩) from rfl))
private theorem rec1044 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1044]? = some (⟨20,(11),[1,5,13],[135],3⟩) from rfl))
private theorem rec1050 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1050]? = some (⟨20,(12),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1051]? = some (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1054 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1054]? = some (⟨20,(12),[1,5],[134],3⟩) from rfl))
private theorem rec1055 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1055]? = some (⟨20,(12),[1,5,13],[135],3⟩) from rfl))
private theorem rec1061 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1061]? = some (⟨20,(13),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1062 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1062]? = some (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1065 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1065]? = some (⟨20,(13),[1,5],[134],3⟩) from rfl))
private theorem rec1066 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1066]? = some (⟨20,(13),[1,5,13],[135],3⟩) from rfl))
private theorem rec1072 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1072]? = some (⟨20,(14),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1073 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1073]? = some (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1076 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1076]? = some (⟨20,(14),[1,5],[134],3⟩) from rfl))
private theorem rec1077 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1077]? = some (⟨20,(14),[1,5,13],[135],3⟩) from rfl))
private theorem rec1083 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1083]? = some (⟨20,(15),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1084 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1084]? = some (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1087 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1087]? = some (⟨20,(15),[1,5],[134],3⟩) from rfl))
private theorem rec1088 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1088]? = some (⟨20,(15),[1,5,13],[135],3⟩) from rfl))
private theorem rec1094 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1094]? = some (⟨20,(16),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1095 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1095]? = some (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1098 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1098]? = some (⟨20,(16),[1,5],[134],3⟩) from rfl))
private theorem rec1099 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1099]? = some (⟨20,(16),[1,5,13],[135],3⟩) from rfl))
private theorem rec1105 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1105]? = some (⟨20,(17),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1106 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1106]? = some (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1109 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1109]? = some (⟨20,(17),[1,5],[134],3⟩) from rfl))
private theorem rec1110 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1110]? = some (⟨20,(17),[1,5,13],[135],3⟩) from rfl))
private theorem rec1116 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1116]? = some (⟨20,(18),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1117]? = some (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1120 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1120]? = some (⟨20,(18),[1,5],[134],3⟩) from rfl))
private theorem rec1121 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1121]? = some (⟨20,(18),[1,5,13],[135],3⟩) from rfl))
private theorem rec1127 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1127]? = some (⟨20,(19),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1128 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1128]? = some (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1131 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1131]? = some (⟨20,(19),[1,5],[134],3⟩) from rfl))
private theorem rec1132 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1132]? = some (⟨20,(19),[1,5,13],[135],3⟩) from rfl))
private theorem rec1138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1138]? = some (⟨20,(20),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1139 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1139]? = some (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1142 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1142]? = some (⟨20,(20),[1,5],[134],3⟩) from rfl))
private theorem rec1143 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1143]? = some (⟨20,(20),[1,5,13],[135],3⟩) from rfl))
private theorem rec1149 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1149]? = some (⟨20,(21),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1150]? = some (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1153 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1153]? = some (⟨20,(21),[1,5],[134],3⟩) from rfl))
private theorem rec1154 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1154]? = some (⟨20,(21),[1,5,13],[135],3⟩) from rfl))
private theorem rec1160 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1160]? = some (⟨20,(22),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1161 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1161]? = some (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1164 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1164]? = some (⟨20,(22),[1,5],[134],3⟩) from rfl))
private theorem rec1165 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1165]? = some (⟨20,(22),[1,5,13],[135],3⟩) from rfl))
private theorem rec1171 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[2]? = some (⟨20,(23),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1172 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[3]? = some (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1175 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[6]? = some (⟨20,(23),[1,5],[134],3⟩) from rfl))
private theorem rec1176 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[7]? = some (⟨20,(23),[1,5,13],[135],3⟩) from rfl))
private theorem rec1182 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[13]? = some (⟨20,(24),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1183 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[14]? = some (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1186 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[17]? = some (⟨20,(24),[1,5],[134],3⟩) from rfl))
private theorem rec1187 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[18]? = some (⟨20,(24),[1,5,13],[135],3⟩) from rfl))
private theorem rec1193 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[24]? = some (⟨23,(0),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1194 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[25]? = some (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1196 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[27]? = some (⟨23,(0),[1,5],[134],2⟩) from rfl))
private theorem rec1197 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[28]? = some (⟨23,(0),[1,5,13],[135],2⟩) from rfl))
private theorem rec1200 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[31]? = some (⟨23,(1),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1201 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[32]? = some (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1203 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[34]? = some (⟨23,(1),[1,5],[134],2⟩) from rfl))
private theorem rec1204 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[35]? = some (⟨23,(1),[1,5,13],[135],2⟩) from rfl))
private theorem rec1207 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[38]? = some (⟨23,(2),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1208 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[39]? = some (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1210 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[41]? = some (⟨23,(2),[1,5],[134],2⟩) from rfl))
private theorem rec1211 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[42]? = some (⟨23,(2),[1,5,13],[135],2⟩) from rfl))
private theorem rec1214 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[45]? = some (⟨23,(3),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1215 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[46]? = some (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1217 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[48]? = some (⟨23,(3),[1,5],[134],2⟩) from rfl))
private theorem rec1218 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[49]? = some (⟨23,(3),[1,5,13],[135],2⟩) from rfl))
private theorem rec1221 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[52]? = some (⟨23,(4),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1222 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[53]? = some (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1224 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[55]? = some (⟨23,(4),[1,5],[134],2⟩) from rfl))
private theorem rec1225 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[56]? = some (⟨23,(4),[1,5,13],[135],2⟩) from rfl))
private theorem rec1228 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[59]? = some (⟨23,(5),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[60]? = some (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1231 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[62]? = some (⟨23,(5),[1,5],[134],2⟩) from rfl))
private theorem rec1232 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[63]? = some (⟨23,(5),[1,5,13],[135],2⟩) from rfl))
private theorem rec1235 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[66]? = some (⟨23,(6),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1236 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[67]? = some (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1238 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[69]? = some (⟨23,(6),[1,5],[134],2⟩) from rfl))
private theorem rec1239 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[70]? = some (⟨23,(6),[1,5,13],[135],2⟩) from rfl))
private theorem rec1242 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[73]? = some (⟨23,(7),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1243 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[74]? = some (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1245 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[76]? = some (⟨23,(7),[1,5],[134],2⟩) from rfl))
private theorem rec1246 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[77]? = some (⟨23,(7),[1,5,13],[135],2⟩) from rfl))
private theorem rec1249 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[80]? = some (⟨23,(8),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1250 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[81]? = some (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1252 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[83]? = some (⟨23,(8),[1,5],[134],2⟩) from rfl))
private theorem rec1253 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[84]? = some (⟨23,(8),[1,5,13],[135],2⟩) from rfl))
private theorem rec1256 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[87]? = some (⟨23,(9),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1257 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[88]? = some (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1259 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[90]? = some (⟨23,(9),[1,5],[134],2⟩) from rfl))
private theorem rec1260 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[91]? = some (⟨23,(9),[1,5,13],[135],2⟩) from rfl))
private theorem rec1263 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[94]? = some (⟨23,(10),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[95]? = some (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1266 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[97]? = some (⟨23,(10),[1,5],[134],2⟩) from rfl))
private theorem rec1267 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[98]? = some (⟨23,(10),[1,5,13],[135],2⟩) from rfl))
private theorem rec1270 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[101]? = some (⟨23,(11),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[102]? = some (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1273 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[104]? = some (⟨23,(11),[1,5],[134],2⟩) from rfl))
private theorem rec1274 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[105]? = some (⟨23,(11),[1,5,13],[135],2⟩) from rfl))
private theorem rec1277 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[108]? = some (⟨23,(12),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[109]? = some (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1280 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[111]? = some (⟨23,(12),[1,5],[134],2⟩) from rfl))
private theorem rec1281 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[112]? = some (⟨23,(12),[1,5,13],[135],2⟩) from rfl))
private theorem rec1284 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[115]? = some (⟨23,(13),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[116]? = some (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1287 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[118]? = some (⟨23,(13),[1,5],[134],2⟩) from rfl))
private theorem rec1288 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[119]? = some (⟨23,(13),[1,5,13],[135],2⟩) from rfl))
private theorem rec1291 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[122]? = some (⟨23,(14),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[123]? = some (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1294 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[125]? = some (⟨23,(14),[1,5],[134],2⟩) from rfl))
private theorem rec1295 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[126]? = some (⟨23,(14),[1,5,13],[135],2⟩) from rfl))
private theorem rec1298 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[129]? = some (⟨23,(15),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1299 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[130]? = some (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1301 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[132]? = some (⟨23,(15),[1,5],[134],2⟩) from rfl))
private theorem rec1302 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[133]? = some (⟨23,(15),[1,5,13],[135],2⟩) from rfl))
private theorem rec1305 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[136]? = some (⟨23,(16),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1306 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[137]? = some (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1308 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[139]? = some (⟨23,(16),[1,5],[134],2⟩) from rfl))
private theorem rec1309 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[140]? = some (⟨23,(16),[1,5,13],[135],2⟩) from rfl))
private theorem rec1312 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[143]? = some (⟨23,(17),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[144]? = some (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1315 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[146]? = some (⟨23,(17),[1,5],[134],2⟩) from rfl))
private theorem rec1316 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[147]? = some (⟨23,(17),[1,5,13],[135],2⟩) from rfl))
private theorem rec1319 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[150]? = some (⟨23,(18),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[151]? = some (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1322 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[153]? = some (⟨23,(18),[1,5],[134],2⟩) from rfl))
private theorem rec1323 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[154]? = some (⟨23,(18),[1,5,13],[135],2⟩) from rfl))
private theorem rec1326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[157]? = some (⟨23,(19),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1327 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[158]? = some (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1329 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[160]? = some (⟨23,(19),[1,5],[134],2⟩) from rfl))
private theorem rec1330 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[161]? = some (⟨23,(19),[1,5,13],[135],2⟩) from rfl))
private theorem rec1333 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[164]? = some (⟨23,(20),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[165]? = some (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1336 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[167]? = some (⟨23,(20),[1,5],[134],2⟩) from rfl))
private theorem rec1337 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[168]? = some (⟨23,(20),[1,5,13],[135],2⟩) from rfl))
private theorem rec1340 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[171]? = some (⟨23,(21),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[172]? = some (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1343 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[174]? = some (⟨23,(21),[1,5],[134],2⟩) from rfl))
private theorem rec1344 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[175]? = some (⟨23,(21),[1,5,13],[135],2⟩) from rfl))
private theorem rec1347 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[178]? = some (⟨23,(22),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1348 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[179]? = some (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1350 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[181]? = some (⟨23,(22),[1,5],[134],2⟩) from rfl))
private theorem rec1351 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[182]? = some (⟨23,(22),[1,5,13],[135],2⟩) from rfl))
private theorem rec1354 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[185]? = some (⟨23,(23),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[186]? = some (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1357 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[188]? = some (⟨23,(23),[1,5],[134],2⟩) from rfl))
private theorem rec1358 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[189]? = some (⟨23,(23),[1,5,13],[135],2⟩) from rfl))
private theorem rec1361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[192]? = some (⟨23,(24),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[193]? = some (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1364 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[195]? = some (⟨23,(24),[1,5],[134],2⟩) from rfl))
private theorem rec1365 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[196]? = some (⟨23,(24),[1,5,13],[135],2⟩) from rfl))
private theorem rec1368 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[199]? = some (⟨25,(0),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1374 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,5],[134],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[205]? = some (⟨25,(0),[1,5],[134],80⟩) from rfl))
private theorem rec1382 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[5],[135],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[213]? = some (⟨25,(0),[5],[135],167⟩) from rfl))
private theorem rec1383 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[5,6],[131],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[214]? = some (⟨25,(0),[5,6],[131],167⟩) from rfl))
private theorem rec1389 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,5,6],[130],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[220]? = some (⟨25,(1),[1,2,5,6],[130],81⟩) from rfl))
private theorem rec1395 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,5],[134],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[226]? = some (⟨25,(1),[1,5],[134],81⟩) from rfl))
private theorem rec1403 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[5],[135],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[234]? = some (⟨25,(1),[5],[135],168⟩) from rfl))
private theorem rec1404 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[5,6],[131],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[235]? = some (⟨25,(1),[5,6],[131],168⟩) from rfl))
private theorem rec1413 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[244]? = some (⟨25,(2),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1419 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,5],[134],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[250]? = some (⟨25,(2),[1,5],[134],80⟩) from rfl))
private theorem rec1427 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[5],[135],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[258]? = some (⟨25,(2),[5],[135],167⟩) from rfl))
private theorem rec1428 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[5,6],[131],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[259]? = some (⟨25,(2),[5,6],[131],167⟩) from rfl))
private theorem rec1437 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,5,6],[130],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[268]? = some (⟨25,(3),[1,2,5,6],[130],82⟩) from rfl))
private theorem rec1443 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,5],[134],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[274]? = some (⟨25,(3),[1,5],[134],82⟩) from rfl))
private theorem rec1451 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[5],[135],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[282]? = some (⟨25,(3),[5],[135],169⟩) from rfl))
private theorem rec1452 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[5,6],[131],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[283]? = some (⟨25,(3),[5,6],[131],169⟩) from rfl))
private theorem rec1461 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[292]? = some (⟨25,(4),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1467 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,5],[134],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[298]? = some (⟨25,(4),[1,5],[134],83⟩) from rfl))
private theorem rec1475 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[5],[135],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[306]? = some (⟨25,(4),[5],[135],170⟩) from rfl))
private theorem rec1476 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[5,6],[131],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[307]? = some (⟨25,(4),[5,6],[131],170⟩) from rfl))
private theorem rec1485 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[316]? = some (⟨25,(5),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1491 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,5],[134],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[322]? = some (⟨25,(5),[1,5],[134],80⟩) from rfl))
private theorem rec1499 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[5],[135],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[330]? = some (⟨25,(5),[5],[135],167⟩) from rfl))
private theorem rec1500 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[5,6],[131],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[331]? = some (⟨25,(5),[5,6],[131],167⟩) from rfl))
private theorem rec1506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,5,6],[130],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[337]? = some (⟨25,(6),[1,2,5,6],[130],81⟩) from rfl))
private theorem rec1512 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,5],[134],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[343]? = some (⟨25,(6),[1,5],[134],81⟩) from rfl))
private theorem rec1520 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[5],[135],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[351]? = some (⟨25,(6),[5],[135],168⟩) from rfl))
private theorem rec1521 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[5,6],[131],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[352]? = some (⟨25,(6),[5,6],[131],168⟩) from rfl))
private theorem rec1530 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[361]? = some (⟨25,(7),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1536 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,5],[134],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[367]? = some (⟨25,(7),[1,5],[134],80⟩) from rfl))
private theorem rec1544 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[5],[135],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[375]? = some (⟨25,(7),[5],[135],167⟩) from rfl))
private theorem rec1545 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[5,6],[131],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[376]? = some (⟨25,(7),[5,6],[131],167⟩) from rfl))
private theorem rec1554 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,5,6],[130],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[385]? = some (⟨25,(8),[1,2,5,6],[130],82⟩) from rfl))
private theorem rec1560 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,5],[134],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[391]? = some (⟨25,(8),[1,5],[134],82⟩) from rfl))
private theorem rec1568 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[5],[135],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[399]? = some (⟨25,(8),[5],[135],169⟩) from rfl))
private theorem rec1569 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[5,6],[131],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[400]? = some (⟨25,(8),[5,6],[131],169⟩) from rfl))
private theorem rec1578 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[409]? = some (⟨25,(9),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1584 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,5],[134],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[415]? = some (⟨25,(9),[1,5],[134],83⟩) from rfl))
private theorem rec1592 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[5],[135],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[423]? = some (⟨25,(9),[5],[135],170⟩) from rfl))
private theorem rec1593 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[5,6],[131],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[424]? = some (⟨25,(9),[5,6],[131],170⟩) from rfl))
private theorem rec1602 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[433]? = some (⟨25,(10),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1608 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,5],[134],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[439]? = some (⟨25,(10),[1,5],[134],84⟩) from rfl))
private theorem rec1616 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[5],[135],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[447]? = some (⟨25,(10),[5],[135],171⟩) from rfl))
private theorem rec1617 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[5,6],[131],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[448]? = some (⟨25,(10),[5,6],[131],171⟩) from rfl))
private theorem rec1623 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[454]? = some (⟨25,(11),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1629 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,5],[134],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[460]? = some (⟨25,(11),[1,5],[134],84⟩) from rfl))
private theorem rec1637 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[5],[135],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[468]? = some (⟨25,(11),[5],[135],171⟩) from rfl))
private theorem rec1638 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[5,6],[131],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[469]? = some (⟨25,(11),[5,6],[131],171⟩) from rfl))
private theorem rec1647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[478]? = some (⟨25,(12),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1653 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,5],[134],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[484]? = some (⟨25,(12),[1,5],[134],84⟩) from rfl))
private theorem rec1661 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[5],[135],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[492]? = some (⟨25,(12),[5],[135],171⟩) from rfl))
private theorem rec1662 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[5,6],[131],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[493]? = some (⟨25,(12),[5,6],[131],171⟩) from rfl))
private theorem rec1671 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[502]? = some (⟨25,(13),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1677 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,5],[134],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[508]? = some (⟨25,(13),[1,5],[134],84⟩) from rfl))
private theorem rec1685 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[5],[135],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[516]? = some (⟨25,(13),[5],[135],171⟩) from rfl))
private theorem rec1686 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[5,6],[131],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[517]? = some (⟨25,(13),[5,6],[131],171⟩) from rfl))
private theorem rec1695 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[526]? = some (⟨25,(14),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1701 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,5],[134],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[532]? = some (⟨25,(14),[1,5],[134],83⟩) from rfl))
private theorem rec1709 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[5],[135],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[540]? = some (⟨25,(14),[5],[135],170⟩) from rfl))
private theorem rec1710 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[5,6],[131],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[541]? = some (⟨25,(14),[5,6],[131],170⟩) from rfl))
private theorem rec1719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[550]? = some (⟨25,(15),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1725 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[556]? = some (⟨25,(15),[1,5],[134],35⟩) from rfl))
private theorem rec1733 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[5],[135],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[564]? = some (⟨25,(15),[5],[135],172⟩) from rfl))
private theorem rec1734 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[565]? = some (⟨25,(15),[5,6],[131],172⟩) from rfl))
private theorem rec1740 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[571]? = some (⟨25,(16),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1746 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[577]? = some (⟨25,(16),[1,5],[134],35⟩) from rfl))
private theorem rec1754 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[5],[135],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[585]? = some (⟨25,(16),[5],[135],172⟩) from rfl))
private theorem rec1755 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[586]? = some (⟨25,(16),[5,6],[131],172⟩) from rfl))
private theorem rec1764 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[595]? = some (⟨25,(17),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1770 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[601]? = some (⟨25,(17),[1,5],[134],35⟩) from rfl))
private theorem rec1778 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[5],[135],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[609]? = some (⟨25,(17),[5],[135],172⟩) from rfl))
private theorem rec1779 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[610]? = some (⟨25,(17),[5,6],[131],172⟩) from rfl))
private theorem rec1788 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[619]? = some (⟨25,(18),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1794 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[625]? = some (⟨25,(18),[1,5],[134],35⟩) from rfl))
private theorem rec1802 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[5],[135],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[633]? = some (⟨25,(18),[5],[135],172⟩) from rfl))
private theorem rec1803 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[634]? = some (⟨25,(18),[5,6],[131],172⟩) from rfl))
private theorem rec1812 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[643]? = some (⟨25,(19),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1818 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,5],[134],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[649]? = some (⟨25,(19),[1,5],[134],35⟩) from rfl))
private theorem rec1826 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[5],[135],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[657]? = some (⟨25,(19),[5],[135],172⟩) from rfl))
private theorem rec1827 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[658]? = some (⟨25,(19),[5,6],[131],172⟩) from rfl))
private theorem rec1836 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[667]? = some (⟨25,(20),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1842 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[673]? = some (⟨25,(20),[1,5],[134],38⟩) from rfl))
private theorem rec1850 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[5],[135],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[681]? = some (⟨25,(20),[5],[135],173⟩) from rfl))
private theorem rec1851 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[682]? = some (⟨25,(20),[5,6],[131],173⟩) from rfl))
private theorem rec1857 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[688]? = some (⟨25,(21),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1863 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[694]? = some (⟨25,(21),[1,5],[134],38⟩) from rfl))
private theorem rec1871 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[5],[135],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[702]? = some (⟨25,(21),[5],[135],173⟩) from rfl))
private theorem rec1872 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[703]? = some (⟨25,(21),[5,6],[131],173⟩) from rfl))
private theorem rec1881 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[712]? = some (⟨25,(22),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1887 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[718]? = some (⟨25,(22),[1,5],[134],38⟩) from rfl))
private theorem rec1895 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[5],[135],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[726]? = some (⟨25,(22),[5],[135],173⟩) from rfl))
private theorem rec1896 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[727]? = some (⟨25,(22),[5,6],[131],173⟩) from rfl))
private theorem rec1905 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[736]? = some (⟨25,(23),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1911 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[742]? = some (⟨25,(23),[1,5],[134],38⟩) from rfl))
private theorem rec1919 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[5],[135],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[750]? = some (⟨25,(23),[5],[135],173⟩) from rfl))
private theorem rec1920 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[751]? = some (⟨25,(23),[5,6],[131],173⟩) from rfl))
private theorem rec1929 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[760]? = some (⟨25,(24),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1935 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,5],[134],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[766]? = some (⟨25,(24),[1,5],[134],38⟩) from rfl))
private theorem rec1943 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[5],[135],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[774]? = some (⟨25,(24),[5],[135],173⟩) from rfl))
private theorem rec1944 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[775]? = some (⟨25,(24),[5,6],[131],173⟩) from rfl))
private theorem rec1957 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[788]? = some (⟨28,(0),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1959 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[790]? = some (⟨28,(0),[1,5],[130],85⟩) from rfl))
private theorem rec1960 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[791]? = some (⟨28,(0),[1,5],[134,135],132⟩) from rfl))
private theorem rec1973 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[804]? = some (⟨28,(1),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1975 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[806]? = some (⟨28,(1),[1,5],[130],85⟩) from rfl))
private theorem rec1976 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[807]? = some (⟨28,(1),[1,5],[134,135],132⟩) from rfl))
private theorem rec1989 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[820]? = some (⟨28,(2),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1991 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[822]? = some (⟨28,(2),[1,5],[130],85⟩) from rfl))
private theorem rec1992 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[823]? = some (⟨28,(2),[1,5],[134,135],132⟩) from rfl))
private theorem rec2005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[836]? = some (⟨28,(3),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec2007 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[838]? = some (⟨28,(3),[1,5],[130],85⟩) from rfl))
private theorem rec2008 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[839]? = some (⟨28,(3),[1,5],[134,135],132⟩) from rfl))
private theorem rec2021 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[852]? = some (⟨28,(4),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec2023 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,5],[130],85⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[854]? = some (⟨28,(4),[1,5],[130],85⟩) from rfl))
private theorem rec2024 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,5],[134,135],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[855]? = some (⟨28,(4),[1,5],[134,135],132⟩) from rfl))
private theorem rec2037 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[868]? = some (⟨28,(5),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2039 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[870]? = some (⟨28,(5),[1,5],[130],86⟩) from rfl))
private theorem rec2040 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[871]? = some (⟨28,(5),[1,5],[134,135],133⟩) from rfl))
private theorem rec2053 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[884]? = some (⟨28,(6),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2055 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[886]? = some (⟨28,(6),[1,5],[130],86⟩) from rfl))
private theorem rec2056 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[887]? = some (⟨28,(6),[1,5],[134,135],133⟩) from rfl))
private theorem rec2069 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[900]? = some (⟨28,(7),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2071 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[902]? = some (⟨28,(7),[1,5],[130],86⟩) from rfl))
private theorem rec2072 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[903]? = some (⟨28,(7),[1,5],[134,135],133⟩) from rfl))
private theorem rec2085 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[916]? = some (⟨28,(8),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2087 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[918]? = some (⟨28,(8),[1,5],[130],86⟩) from rfl))
private theorem rec2088 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[919]? = some (⟨28,(8),[1,5],[134,135],133⟩) from rfl))
private theorem rec2101 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[932]? = some (⟨28,(9),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2103 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,5],[130],86⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[934]? = some (⟨28,(9),[1,5],[130],86⟩) from rfl))
private theorem rec2104 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,5],[134,135],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[935]? = some (⟨28,(9),[1,5],[134,135],133⟩) from rfl))
private theorem rec2117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[948]? = some (⟨28,(10),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2119 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,5],[130],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[950]? = some (⟨28,(10),[1,5],[130],87⟩) from rfl))
private theorem rec2120 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,5],[134,135],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[951]? = some (⟨28,(10),[1,5],[134,135],134⟩) from rfl))
private theorem rec2133 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[964]? = some (⟨28,(11),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2135 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,5],[130],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[966]? = some (⟨28,(11),[1,5],[130],88⟩) from rfl))
private theorem rec2136 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,5],[134,135],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[967]? = some (⟨28,(11),[1,5],[134,135],135⟩) from rfl))
private theorem rec2149 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,2,5,6],[131],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[980]? = some (⟨28,(12),[1,2,5,6],[131],117⟩) from rfl))
private theorem rec2151 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,5],[130],89⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[982]? = some (⟨28,(12),[1,5],[130],89⟩) from rfl))
private theorem rec2152 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,5],[134,135],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[983]? = some (⟨28,(12),[1,5],[134,135],136⟩) from rfl))
private theorem rec2165 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[996]? = some (⟨28,(13),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2167 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,5],[130],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[998]? = some (⟨28,(13),[1,5],[130],88⟩) from rfl))
private theorem rec2168 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,5],[134,135],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[999]? = some (⟨28,(13),[1,5],[134,135],135⟩) from rfl))
private theorem rec2181 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,2,5,6],[131],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1012]? = some (⟨28,(14),[1,2,5,6],[131],118⟩) from rfl))
private theorem rec2183 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,5],[130],90⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1014]? = some (⟨28,(14),[1,5],[130],90⟩) from rfl))
private theorem rec2184 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,5],[134,135],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1015]? = some (⟨28,(14),[1,5],[134,135],137⟩) from rfl))
private theorem rec2197 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1028]? = some (⟨28,(15),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2199 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,5],[130],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1030]? = some (⟨28,(15),[1,5],[130],87⟩) from rfl))
private theorem rec2200 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,5],[134,135],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1031]? = some (⟨28,(15),[1,5],[134,135],134⟩) from rfl))
private theorem rec2213 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1044]? = some (⟨28,(16),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2215 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,5],[130],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1046]? = some (⟨28,(16),[1,5],[130],91⟩) from rfl))
private theorem rec2216 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,5],[134,135],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1047]? = some (⟨28,(16),[1,5],[134,135],138⟩) from rfl))
private theorem rec2229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1060]? = some (⟨28,(17),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2231 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,5],[130],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1062]? = some (⟨28,(17),[1,5],[130],91⟩) from rfl))
private theorem rec2232 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,5],[134,135],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1063]? = some (⟨28,(17),[1,5],[134,135],138⟩) from rfl))
private theorem rec2245 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1076]? = some (⟨28,(18),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2247 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,5],[130],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1078]? = some (⟨28,(18),[1,5],[130],91⟩) from rfl))
private theorem rec2248 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,5],[134,135],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1079]? = some (⟨28,(18),[1,5],[134,135],138⟩) from rfl))
private theorem rec2261 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1092]? = some (⟨28,(19),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2263 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,5],[130],91⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1094]? = some (⟨28,(19),[1,5],[130],91⟩) from rfl))
private theorem rec2264 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,5],[134,135],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1095]? = some (⟨28,(19),[1,5],[134,135],138⟩) from rfl))
private theorem rec2277 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1108]? = some (⟨28,(20),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2279 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,5],[130],87⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1110]? = some (⟨28,(20),[1,5],[130],87⟩) from rfl))
private theorem rec2280 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,5],[134,135],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1111]? = some (⟨28,(20),[1,5],[134,135],134⟩) from rfl))
private theorem rec2293 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1124]? = some (⟨28,(21),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2295 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,5],[130],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1126]? = some (⟨28,(21),[1,5],[130],88⟩) from rfl))
private theorem rec2296 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,5],[134,135],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1127]? = some (⟨28,(21),[1,5],[134,135],135⟩) from rfl))
private theorem rec2309 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,2,5,6],[131],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1140]? = some (⟨28,(22),[1,2,5,6],[131],117⟩) from rfl))
private theorem rec2311 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,5],[130],89⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1142]? = some (⟨28,(22),[1,5],[130],89⟩) from rfl))
private theorem rec2312 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,5],[134,135],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1143]? = some (⟨28,(22),[1,5],[134,135],136⟩) from rfl))
private theorem rec2325 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1156]? = some (⟨28,(23),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2327 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,5],[130],88⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1158]? = some (⟨28,(23),[1,5],[130],88⟩) from rfl))
private theorem rec2328 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,5],[134,135],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1159]? = some (⟨28,(23),[1,5],[134,135],135⟩) from rfl))
private theorem rec2341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,2,5,6],[131],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1172]? = some (⟨28,(24),[1,2,5,6],[131],118⟩) from rfl))
private theorem rec2343 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,5],[130],90⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1174]? = some (⟨28,(24),[1,5],[130],90⟩) from rfl))
private theorem rec2344 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,5],[134,135],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1175]? = some (⟨28,(24),[1,5],[134,135],137⟩) from rfl))
private theorem rec2365 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([131, 134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[5],[131,134,135],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1196]? = some (⟨30,(0),[5],[131,134,135],152⟩) from rfl))
private theorem rec2366 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[5,6],[130],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1197]? = some (⟨30,(0),[5,6],[130],152⟩) from rfl))
private theorem rec2379 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([131, 134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[5],[131,134,135],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1210]? = some (⟨30,(1),[5],[131,134,135],153⟩) from rfl))
private theorem rec2380 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[5,6],[130],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1211]? = some (⟨30,(1),[5,6],[130],153⟩) from rfl))
private theorem rec2387 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2,5,6],[130],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1218]? = some (⟨30,(2),[1,2,5,6],[130],92⟩) from rfl))
private theorem rec2390 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,5],[134],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1221]? = some (⟨30,(2),[1,5],[134],92⟩) from rfl))
private theorem rec2391 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,5],[135],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1222]? = some (⟨30,(2),[1,5],[135],120⟩) from rfl))
private theorem rec2392 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,5,6],[131],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1223]? = some (⟨30,(2),[1,5,6],[131],120⟩) from rfl))
private theorem rec2410 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2,5,6],[130],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1241]? = some (⟨30,(3),[1,2,5,6],[130],93⟩) from rfl))
private theorem rec2412 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,5],[134],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1243]? = some (⟨30,(3),[1,5],[134],93⟩) from rfl))
private theorem rec2418 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[5],[135],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1249]? = some (⟨30,(3),[5],[135],181⟩) from rfl))
private theorem rec2419 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[5,6],[131],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1250]? = some (⟨30,(3),[5,6],[131],181⟩) from rfl))
private theorem rec2434 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2,5,6],[130],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1265]? = some (⟨30,(4),[1,2,5,6],[130],94⟩) from rfl))
private theorem rec2436 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,5],[134],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1267]? = some (⟨30,(4),[1,5],[134],94⟩) from rfl))
private theorem rec2442 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[5],[135],182⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1273]? = some (⟨30,(4),[5],[135],182⟩) from rfl))
private theorem rec2443 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[5,6],[131],182⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[0]? = some (⟨30,(4),[5,6],[131],182⟩) from rfl))
private theorem rec2458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2,5,6],[130],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[15]? = some (⟨30,(5),[1,2,5,6],[130],93⟩) from rfl))
private theorem rec2460 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,5],[134],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[17]? = some (⟨30,(5),[1,5],[134],93⟩) from rfl))
private theorem rec2466 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[5],[135],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[23]? = some (⟨30,(5),[5],[135],181⟩) from rfl))
private theorem rec2467 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[5,6],[131],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[24]? = some (⟨30,(5),[5,6],[131],181⟩) from rfl))
private theorem rec2482 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2,5,6],[130],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[39]? = some (⟨30,(6),[1,2,5,6],[130],95⟩) from rfl))
private theorem rec2484 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,5],[134],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[41]? = some (⟨30,(6),[1,5],[134],95⟩) from rfl))
private theorem rec2490 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[5],[135],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[47]? = some (⟨30,(6),[5],[135],183⟩) from rfl))
private theorem rec2491 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[5,6],[131],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[48]? = some (⟨30,(6),[5,6],[131],183⟩) from rfl))
private theorem rec2506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2,5,6],[130],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[63]? = some (⟨30,(7),[1,2,5,6],[130],95⟩) from rfl))
private theorem rec2508 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,5],[134],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[65]? = some (⟨30,(7),[1,5],[134],95⟩) from rfl))
private theorem rec2514 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[5],[135],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[71]? = some (⟨30,(7),[5],[135],183⟩) from rfl))
private theorem rec2515 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[5,6],[131],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[72]? = some (⟨30,(7),[5,6],[131],183⟩) from rfl))
private theorem rec2530 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2,5,6],[130],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[87]? = some (⟨30,(8),[1,2,5,6],[130],96⟩) from rfl))
private theorem rec2532 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,5],[134],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[89]? = some (⟨30,(8),[1,5],[134],96⟩) from rfl))
private theorem rec2538 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[5],[135],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[95]? = some (⟨30,(8),[5],[135],184⟩) from rfl))
private theorem rec2539 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[5,6],[131],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[96]? = some (⟨30,(8),[5,6],[131],184⟩) from rfl))
private theorem rec2554 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2,5,6],[130],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[111]? = some (⟨30,(9),[1,2,5,6],[130],96⟩) from rfl))
private theorem rec2556 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,5],[134],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[113]? = some (⟨30,(9),[1,5],[134],96⟩) from rfl))
private theorem rec2562 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[5],[135],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[119]? = some (⟨30,(9),[5],[135],184⟩) from rfl))
private theorem rec2563 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[5,6],[131],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[120]? = some (⟨30,(9),[5,6],[131],184⟩) from rfl))
private theorem rec2573 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,2,5,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[130]? = some (⟨33,(0),[1,2,5,6],[130],97⟩) from rfl))
private theorem rec2574 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,2,5,6,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[131]? = some (⟨33,(0),[1,2,5,6,14],[131],97⟩) from rfl))
private theorem rec2575 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,5],[134,135],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[132]? = some (⟨33,(0),[1,5],[134,135],97⟩) from rfl))
private theorem rec2584 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[1,5],[134,135],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[141]? = some (⟨33,(1),[1,5],[134,135],98⟩) from rfl))
private theorem rec2585 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[1,5,6],[130,131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[142]? = some (⟨33,(1),[1,5,6],[130,131],98⟩) from rfl))
private theorem rec2597 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130, 131, 134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[1,5],[130,131,134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[154]? = some (⟨33,(2),[1,5],[130,131,134,135],3⟩) from rfl))
private theorem rec2610 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[167]? = some (⟨33,(3),[1,5],[134],3⟩) from rfl))
private theorem rec2611 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[168]? = some (⟨33,(3),[1,5,6],[130],3⟩) from rfl))
private theorem rec2612 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[169]? = some (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2613 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[170]? = some (⟨33,(3),[1,5,13],[135],3⟩) from rfl))
private theorem rec2621 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[178]? = some (⟨33,(4),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec2622 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[179]? = some (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) from rfl))
private theorem rec2623 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,5],[134],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[180]? = some (⟨33,(4),[1,5],[134],2⟩) from rfl))
private theorem rec2625 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,5,13],[135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[182]? = some (⟨33,(4),[1,5,13],[135],2⟩) from rfl))
private theorem rec2635 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,5],[134,135],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[192]? = some (⟨33,(5),[1,5],[134,135],98⟩) from rfl))
private theorem rec2636 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,5,6],[130,131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[193]? = some (⟨33,(5),[1,5,6],[130,131],98⟩) from rfl))
private theorem rec2646 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[203]? = some (⟨33,(6),[1,5],[134],3⟩) from rfl))
private theorem rec2647 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[204]? = some (⟨33,(6),[1,5,6],[130],3⟩) from rfl))
private theorem rec2648 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[205]? = some (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2649 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[206]? = some (⟨33,(6),[1,5,13],[135],3⟩) from rfl))
private theorem rec2657 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[214]? = some (⟨33,(7),[1,5],[134],3⟩) from rfl))
private theorem rec2658 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[215]? = some (⟨33,(7),[1,5,6],[130],3⟩) from rfl))
private theorem rec2659 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[216]? = some (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2660 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[217]? = some (⟨33,(7),[1,5,13],[135],3⟩) from rfl))
private theorem rec2666 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,5,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[223]? = some (⟨33,(8),[1,2,5,6],[130],97⟩) from rfl))
private theorem rec2667 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[224]? = some (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) from rfl))
private theorem rec2671 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,5],[134],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[228]? = some (⟨33,(8),[1,5],[134],97⟩) from rfl))
private theorem rec2672 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,5,13],[135],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[229]? = some (⟨33,(8),[1,5,13],[135],97⟩) from rfl))
private theorem rec2676 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,5,6],[130],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[233]? = some (⟨33,(9),[1,2,5,6],[130],98⟩) from rfl))
private theorem rec2677 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,5,6,13,14],[131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[234]? = some (⟨33,(9),[1,2,5,6,13,14],[131],98⟩) from rfl))
private theorem rec2681 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,5],[134],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[238]? = some (⟨33,(9),[1,5],[134],98⟩) from rfl))
private theorem rec2682 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,5,13],[135],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[239]? = some (⟨33,(9),[1,5,13],[135],98⟩) from rfl))
private theorem rec2692 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[5],[134],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[249]? = some (⟨33,(10),[5],[134],97⟩) from rfl))
private theorem rec2693 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[5,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[250]? = some (⟨33,(10),[5,6],[130],97⟩) from rfl))
private theorem rec2694 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[5,6,13,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[251]? = some (⟨33,(10),[5,6,13,14],[131],97⟩) from rfl))
private theorem rec2695 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[5,13],[135],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[252]? = some (⟨33,(10),[5,13],[135],97⟩) from rfl))
private theorem rec2697 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[254]? = some (⟨33,(11),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec2698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[255]? = some (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2701 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[258]? = some (⟨33,(11),[1,5],[134],3⟩) from rfl))
private theorem rec2702 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[259]? = some (⟨33,(11),[1,5,13],[135],3⟩) from rfl))
private theorem rec2707 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[264]? = some (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) from rfl))
private theorem rec2708 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,5,6,13,14],[131],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[265]? = some (⟨33,(12),[1,2,5,6,13,14],[131],99⟩) from rfl))
private theorem rec2710 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,5],[134],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[267]? = some (⟨33,(12),[1,5],[134],99⟩) from rfl))
private theorem rec2711 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,5,13],[135],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[268]? = some (⟨33,(12),[1,5,13],[135],99⟩) from rfl))
private theorem rec2718 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,2,5,6],[130,131],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[275]? = some (⟨33,(13),[1,2,5,6],[130,131],99⟩) from rfl))
private theorem rec2722 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,5],[134,135],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[279]? = some (⟨33,(13),[1,5],[134,135],99⟩) from rfl))
private theorem rec2731 (si parent : ℕ) (hs : si ∈ ([1, 2, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,2,5],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[288]? = some (⟨33,(14),[1,2,5],[130],3⟩) from rfl))
private theorem rec2732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[289]? = some (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) from rfl))
private theorem rec2735 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,5],[134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[292]? = some (⟨33,(14),[1,5],[134,135],3⟩) from rfl))
private theorem rec2742 (si parent : ℕ) (hs : si ∈ ([1, 2, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,2,5],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[299]? = some (⟨33,(15),[1,2,5],[130],3⟩) from rfl))
private theorem rec2743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[300]? = some (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) from rfl))
private theorem rec2746 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,5],[134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[303]? = some (⟨33,(15),[1,5],[134,135],3⟩) from rfl))
private theorem rec2753 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[310]? = some (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2754 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[311]? = some (⟨35,(0),[1,5],[134,135],2⟩) from rfl))
private theorem rec2758 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[315]? = some (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2759 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[316]? = some (⟨35,(1),[1,5],[134,135],2⟩) from rfl))
private theorem rec2765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[322]? = some (⟨35,(2),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2767 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,5],[130],100⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[324]? = some (⟨35,(2),[1,5],[130],100⟩) from rfl))
private theorem rec2768 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,5],[135],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[325]? = some (⟨35,(2),[1,5],[135],101⟩) from rfl))
private theorem rec2769 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,5],[134],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[326]? = some (⟨35,(2),[1,5],[134],139⟩) from rfl))
private theorem rec2781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[338]? = some (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2782 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2,5,6],[131],121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[339]? = some (⟨35,(3),[1,2,5,6],[131],121⟩) from rfl))
private theorem rec2783 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,5],[134],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[340]? = some (⟨35,(3),[1,5],[134],101⟩) from rfl))
private theorem rec2784 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,5],[135],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[341]? = some (⟨35,(3),[1,5],[135],139⟩) from rfl))
private theorem rec2790 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[347]? = some (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2791 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[348]? = some (⟨35,(4),[1,5],[134,135],2⟩) from rfl))
private theorem rec2795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[352]? = some (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2796 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[353]? = some (⟨35,(5),[1,5],[134,135],2⟩) from rfl))
private theorem rec2802 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[359]? = some (⟨35,(6),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2804 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,5],[135],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[361]? = some (⟨35,(6),[1,5],[135],101⟩) from rfl))
private theorem rec2805 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,5],[130],102⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[362]? = some (⟨35,(6),[1,5],[130],102⟩) from rfl))
private theorem rec2806 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,5],[134],140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[363]? = some (⟨35,(6),[1,5],[134],140⟩) from rfl))
private theorem rec2818 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[375]? = some (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2819 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2,5,6],[131],122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[376]? = some (⟨35,(7),[1,2,5,6],[131],122⟩) from rfl))
private theorem rec2820 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,5],[134],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[377]? = some (⟨35,(7),[1,5],[134],101⟩) from rfl))
private theorem rec2821 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,5],[135],140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[378]? = some (⟨35,(7),[1,5],[135],140⟩) from rfl))
private theorem rec2827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[384]? = some (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2828 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[385]? = some (⟨35,(8),[1,5],[134,135],2⟩) from rfl))
private theorem rec2832 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[389]? = some (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2833 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[390]? = some (⟨35,(9),[1,5],[134,135],2⟩) from rfl))
private theorem rec2839 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[396]? = some (⟨35,(10),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2841 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,5],[135],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[398]? = some (⟨35,(10),[1,5],[135],101⟩) from rfl))
private theorem rec2842 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,5],[130],103⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[399]? = some (⟨35,(10),[1,5],[130],103⟩) from rfl))
private theorem rec2843 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,5],[134],141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[400]? = some (⟨35,(10),[1,5],[134],141⟩) from rfl))
private theorem rec2855 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[412]? = some (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2856 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2,5,6],[131],123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[413]? = some (⟨35,(11),[1,2,5,6],[131],123⟩) from rfl))
private theorem rec2857 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,5],[134],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[414]? = some (⟨35,(11),[1,5],[134],101⟩) from rfl))
private theorem rec2858 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,5],[135],144⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[415]? = some (⟨35,(11),[1,5],[135],144⟩) from rfl))
private theorem rec2864 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[421]? = some (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2865 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[422]? = some (⟨35,(12),[1,5],[134,135],2⟩) from rfl))
private theorem rec2869 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[426]? = some (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2870 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,5],[134,135],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[427]? = some (⟨35,(13),[1,5],[134,135],2⟩) from rfl))
private theorem rec2876 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[433]? = some (⟨35,(14),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2878 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,5],[135],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[435]? = some (⟨35,(14),[1,5],[135],101⟩) from rfl))
private theorem rec2879 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,5],[130],104⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[436]? = some (⟨35,(14),[1,5],[130],104⟩) from rfl))
private theorem rec2880 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,5],[134],142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[437]? = some (⟨35,(14),[1,5],[134],142⟩) from rfl))
private theorem rec2892 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[449]? = some (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2893 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2,5,6],[131],124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[450]? = some (⟨35,(15),[1,2,5,6],[131],124⟩) from rfl))
private theorem rec2894 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,5],[134],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[451]? = some (⟨35,(15),[1,5],[134],101⟩) from rfl))
private theorem rec2895 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,5],[135],142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[452]? = some (⟨35,(15),[1,5],[135],142⟩) from rfl))
private theorem rec2899 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,5,6],[130],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[456]? = some (⟨36,(5),[1,2,5,6],[130],105⟩) from rfl))
private theorem rec2900 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[457]? = some (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) from rfl))
private theorem rec2903 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,5],[134],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[460]? = some (⟨36,(5),[1,5],[134],105⟩) from rfl))
private theorem rec2904 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,5,13],[135],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[461]? = some (⟨36,(5),[1,5,13],[135],105⟩) from rfl))
private theorem rec2909 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[466]? = some (⟨36,(7),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec2911 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[468]? = some (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) from rfl))
private theorem rec2913 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[470]? = some (⟨36,(7),[1,5],[134],3⟩) from rfl))
private theorem rec2914 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[471]? = some (⟨36,(7),[1,5,13],[135],3⟩) from rfl))
private theorem rec2923 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[480]? = some (⟨36,(8),[1,5],[134],3⟩) from rfl))
private theorem rec2924 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[481]? = some (⟨36,(8),[1,5,6],[130],3⟩) from rfl))
private theorem rec2925 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[482]? = some (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2926 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[483]? = some (⟨36,(8),[1,5,13],[135],3⟩) from rfl))
private theorem rec2936 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,5],[134],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[493]? = some (⟨36,(9),[1,5],[134],143⟩) from rfl))
private theorem rec2937 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,5,13],[135],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[494]? = some (⟨36,(9),[1,5,13],[135],143⟩) from rfl))
private theorem rec2940 (si parent : ℕ) (hs : si ∈ ([2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[2,5,6],[130],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[497]? = some (⟨36,(9),[2,5,6],[130],143⟩) from rfl))
private theorem rec2941 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[2,5,6,14],[131,146],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[498]? = some (⟨36,(9),[2,5,6,14],[131,146],143⟩) from rfl))
private theorem rec2949 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[506]? = some (⟨36,(15),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec2950 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[507]? = some (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2953 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134, 135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,5],[134,135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[510]? = some (⟨36,(15),[1,5],[134,135],3⟩) from rfl))
private theorem rec2960 (si parent : ℕ) (hs : si ∈ ([1, 5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5],[134],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[517]? = some (⟨36,(16),[1,5],[134],3⟩) from rfl))
private theorem rec2961 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[518]? = some (⟨36,(16),[1,5,6],[130],3⟩) from rfl))
private theorem rec2962 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[519]? = some (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2963 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,13],[135],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[520]? = some (⟨36,(16),[1,5,13],[135],3⟩) from rfl))
private theorem rec2977 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([130, 134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[5],[130,134],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[534]? = some (⟨36,(17),[5],[130,134],48⟩) from rfl))
private theorem rec2978 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([131, 135, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[5,13],[131,135,146,150],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[535]? = some (⟨36,(17),[5,13],[131,135,146,150],48⟩) from rfl))
private theorem rec2986 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[5],[134],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[543]? = some (⟨36,(19),[5],[134],143⟩) from rfl))
private theorem rec2987 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[5,6],[130],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[544]? = some (⟨36,(19),[5,6],[130],143⟩) from rfl))
private theorem rec2988 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[545]? = some (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) from rfl))
private theorem rec2989 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[5,13],[135],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[546]? = some (⟨36,(19),[5,13],[135],143⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0128_0144 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 128).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 128).take 16 = [⟨1,128,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,129,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,130,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,131,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,132,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,133,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,134,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,135,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,136,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,137,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,138,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,139,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,140,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,141,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,142,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,143,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 5 128 (by decide) (by decide)
  · left
    exact rec361 5 129 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 17)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec496 5 130 (by decide) (by decide)
      · right
        exact rec513 5 130 (by decide) (by decide)
      · right
        exact rec530 5 130 (by decide) (by decide)
      · right
        exact rec547 5 130 (by decide) (by decide)
      · right
        exact rec564 5 130 (by decide) (by decide)
      · right
        exact rec581 5 130 (by decide) (by decide)
      · right
        exact rec598 5 130 (by decide) (by decide)
      · right
        exact rec615 5 130 (by decide) (by decide)
      · right
        exact rec632 5 130 (by decide) (by decide)
      · right
        exact rec649 5 130 (by decide) (by decide)
      · right
        exact rec666 5 130 (by decide) (by decide)
      · right
        exact rec683 5 130 (by decide) (by decide)
      · right
        exact rec700 5 130 (by decide) (by decide)
      · right
        exact rec717 5 130 (by decide) (by decide)
      · right
        exact rec734 5 130 (by decide) (by decide)
      · right
        exact rec751 5 130 (by decide) (by decide)
      · right
        exact rec768 5 130 (by decide) (by decide)
      · right
        exact rec785 5 130 (by decide) (by decide)
      · right
        exact rec802 5 130 (by decide) (by decide)
      · right
        exact rec819 5 130 (by decide) (by decide)
      · right
        exact rec836 5 130 (by decide) (by decide)
      · right
        exact rec853 5 130 (by decide) (by decide)
      · right
        exact rec870 5 130 (by decide) (by decide)
      · right
        exact rec887 5 130 (by decide) (by decide)
      · right
        exact rec904 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec918 5 130 (by decide) (by decide)
      · right
        exact rec929 5 130 (by decide) (by decide)
      · right
        exact rec940 5 130 (by decide) (by decide)
      · right
        exact rec951 5 130 (by decide) (by decide)
      · right
        exact rec962 5 130 (by decide) (by decide)
      · right
        exact rec973 5 130 (by decide) (by decide)
      · right
        exact rec984 5 130 (by decide) (by decide)
      · right
        exact rec995 5 130 (by decide) (by decide)
      · right
        exact rec1006 5 130 (by decide) (by decide)
      · right
        exact rec1017 5 130 (by decide) (by decide)
      · right
        exact rec1028 5 130 (by decide) (by decide)
      · right
        exact rec1039 5 130 (by decide) (by decide)
      · right
        exact rec1050 5 130 (by decide) (by decide)
      · right
        exact rec1061 5 130 (by decide) (by decide)
      · right
        exact rec1072 5 130 (by decide) (by decide)
      · right
        exact rec1083 5 130 (by decide) (by decide)
      · right
        exact rec1094 5 130 (by decide) (by decide)
      · right
        exact rec1105 5 130 (by decide) (by decide)
      · right
        exact rec1116 5 130 (by decide) (by decide)
      · right
        exact rec1127 5 130 (by decide) (by decide)
      · right
        exact rec1138 5 130 (by decide) (by decide)
      · right
        exact rec1149 5 130 (by decide) (by decide)
      · right
        exact rec1160 5 130 (by decide) (by decide)
      · right
        exact rec1171 5 130 (by decide) (by decide)
      · right
        exact rec1182 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 21)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1193 5 130 (by decide) (by decide)
      · right
        exact rec1200 5 130 (by decide) (by decide)
      · right
        exact rec1207 5 130 (by decide) (by decide)
      · right
        exact rec1214 5 130 (by decide) (by decide)
      · right
        exact rec1221 5 130 (by decide) (by decide)
      · right
        exact rec1228 5 130 (by decide) (by decide)
      · right
        exact rec1235 5 130 (by decide) (by decide)
      · right
        exact rec1242 5 130 (by decide) (by decide)
      · right
        exact rec1249 5 130 (by decide) (by decide)
      · right
        exact rec1256 5 130 (by decide) (by decide)
      · right
        exact rec1263 5 130 (by decide) (by decide)
      · right
        exact rec1270 5 130 (by decide) (by decide)
      · right
        exact rec1277 5 130 (by decide) (by decide)
      · right
        exact rec1284 5 130 (by decide) (by decide)
      · right
        exact rec1291 5 130 (by decide) (by decide)
      · right
        exact rec1298 5 130 (by decide) (by decide)
      · right
        exact rec1305 5 130 (by decide) (by decide)
      · right
        exact rec1312 5 130 (by decide) (by decide)
      · right
        exact rec1319 5 130 (by decide) (by decide)
      · right
        exact rec1326 5 130 (by decide) (by decide)
      · right
        exact rec1333 5 130 (by decide) (by decide)
      · right
        exact rec1340 5 130 (by decide) (by decide)
      · right
        exact rec1347 5 130 (by decide) (by decide)
      · right
        exact rec1354 5 130 (by decide) (by decide)
      · right
        exact rec1361 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1368 5 130 (by decide) (by decide)
      · right
        exact rec1389 5 130 (by decide) (by decide)
      · right
        exact rec1413 5 130 (by decide) (by decide)
      · right
        exact rec1437 5 130 (by decide) (by decide)
      · right
        exact rec1461 5 130 (by decide) (by decide)
      · right
        exact rec1485 5 130 (by decide) (by decide)
      · right
        exact rec1506 5 130 (by decide) (by decide)
      · right
        exact rec1530 5 130 (by decide) (by decide)
      · right
        exact rec1554 5 130 (by decide) (by decide)
      · right
        exact rec1578 5 130 (by decide) (by decide)
      · right
        exact rec1602 5 130 (by decide) (by decide)
      · right
        exact rec1623 5 130 (by decide) (by decide)
      · right
        exact rec1647 5 130 (by decide) (by decide)
      · right
        exact rec1671 5 130 (by decide) (by decide)
      · right
        exact rec1695 5 130 (by decide) (by decide)
      · right
        exact rec1719 5 130 (by decide) (by decide)
      · right
        exact rec1740 5 130 (by decide) (by decide)
      · right
        exact rec1764 5 130 (by decide) (by decide)
      · right
        exact rec1788 5 130 (by decide) (by decide)
      · right
        exact rec1812 5 130 (by decide) (by decide)
      · right
        exact rec1836 5 130 (by decide) (by decide)
      · right
        exact rec1857 5 130 (by decide) (by decide)
      · right
        exact rec1881 5 130 (by decide) (by decide)
      · right
        exact rec1905 5 130 (by decide) (by decide)
      · right
        exact rec1929 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 26)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1959 5 130 (by decide) (by decide)
      · right
        exact rec1975 5 130 (by decide) (by decide)
      · right
        exact rec1991 5 130 (by decide) (by decide)
      · right
        exact rec2007 5 130 (by decide) (by decide)
      · right
        exact rec2023 5 130 (by decide) (by decide)
      · right
        exact rec2039 5 130 (by decide) (by decide)
      · right
        exact rec2055 5 130 (by decide) (by decide)
      · right
        exact rec2071 5 130 (by decide) (by decide)
      · right
        exact rec2087 5 130 (by decide) (by decide)
      · right
        exact rec2103 5 130 (by decide) (by decide)
      · right
        exact rec2119 5 130 (by decide) (by decide)
      · right
        exact rec2135 5 130 (by decide) (by decide)
      · right
        exact rec2151 5 130 (by decide) (by decide)
      · right
        exact rec2167 5 130 (by decide) (by decide)
      · right
        exact rec2183 5 130 (by decide) (by decide)
      · right
        exact rec2199 5 130 (by decide) (by decide)
      · right
        exact rec2215 5 130 (by decide) (by decide)
      · right
        exact rec2231 5 130 (by decide) (by decide)
      · right
        exact rec2247 5 130 (by decide) (by decide)
      · right
        exact rec2263 5 130 (by decide) (by decide)
      · right
        exact rec2279 5 130 (by decide) (by decide)
      · right
        exact rec2295 5 130 (by decide) (by decide)
      · right
        exact rec2311 5 130 (by decide) (by decide)
      · right
        exact rec2327 5 130 (by decide) (by decide)
      · right
        exact rec2343 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
        exact rec2366 5 130 (by decide) (by decide)
      · right
        exact rec2380 5 130 (by decide) (by decide)
      · right
        exact rec2387 5 130 (by decide) (by decide)
      · right
        exact rec2410 5 130 (by decide) (by decide)
      · right
        exact rec2434 5 130 (by decide) (by decide)
      · right
        exact rec2458 5 130 (by decide) (by decide)
      · right
        exact rec2482 5 130 (by decide) (by decide)
      · right
        exact rec2506 5 130 (by decide) (by decide)
      · right
        exact rec2530 5 130 (by decide) (by decide)
      · right
        exact rec2554 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 31)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 32)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2573 5 130 (by decide) (by decide)
      · right
        exact rec2585 5 130 (by decide) (by decide)
      · right
        exact rec2597 5 130 (by decide) (by decide)
      · right
        exact rec2611 5 130 (by decide) (by decide)
      · right
        exact rec2621 5 130 (by decide) (by decide)
      · right
        exact rec2636 5 130 (by decide) (by decide)
      · right
        exact rec2647 5 130 (by decide) (by decide)
      · right
        exact rec2658 5 130 (by decide) (by decide)
      · right
        exact rec2666 5 130 (by decide) (by decide)
      · right
        exact rec2676 5 130 (by decide) (by decide)
      · right
        exact rec2693 5 130 (by decide) (by decide)
      · right
        exact rec2697 5 130 (by decide) (by decide)
      · right
        exact rec2707 5 130 (by decide) (by decide)
      · right
        exact rec2718 5 130 (by decide) (by decide)
      · right
        exact rec2731 5 130 (by decide) (by decide)
      · right
        exact rec2742 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2753 5 130 (by decide) (by decide)
      · right
        exact rec2758 5 130 (by decide) (by decide)
      · right
        exact rec2767 5 130 (by decide) (by decide)
      · right
        exact rec2781 5 130 (by decide) (by decide)
      · right
        exact rec2790 5 130 (by decide) (by decide)
      · right
        exact rec2795 5 130 (by decide) (by decide)
      · right
        exact rec2805 5 130 (by decide) (by decide)
      · right
        exact rec2818 5 130 (by decide) (by decide)
      · right
        exact rec2827 5 130 (by decide) (by decide)
      · right
        exact rec2832 5 130 (by decide) (by decide)
      · right
        exact rec2842 5 130 (by decide) (by decide)
      · right
        exact rec2855 5 130 (by decide) (by decide)
      · right
        exact rec2864 5 130 (by decide) (by decide)
      · right
        exact rec2869 5 130 (by decide) (by decide)
      · right
        exact rec2879 5 130 (by decide) (by decide)
      · right
        exact rec2892 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2899 5 130 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2909 5 130 (by decide) (by decide)
      · right
        exact rec2924 5 130 (by decide) (by decide)
      · right
        exact rec2940 5 130 (by decide) (by decide)
      · left
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
        exact rec2949 5 130 (by decide) (by decide)
      · right
        exact rec2961 5 130 (by decide) (by decide)
      · right
        exact rec2977 5 130 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2987 5 130 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 37)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
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
    intro gs hgs
    change gs ∈ [(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 17)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec493 5 131 (by decide) (by decide)
      · right
        exact rec510 5 131 (by decide) (by decide)
      · right
        exact rec527 5 131 (by decide) (by decide)
      · right
        exact rec544 5 131 (by decide) (by decide)
      · right
        exact rec561 5 131 (by decide) (by decide)
      · right
        exact rec578 5 131 (by decide) (by decide)
      · right
        exact rec595 5 131 (by decide) (by decide)
      · right
        exact rec612 5 131 (by decide) (by decide)
      · right
        exact rec629 5 131 (by decide) (by decide)
      · right
        exact rec646 5 131 (by decide) (by decide)
      · right
        exact rec663 5 131 (by decide) (by decide)
      · right
        exact rec680 5 131 (by decide) (by decide)
      · right
        exact rec697 5 131 (by decide) (by decide)
      · right
        exact rec714 5 131 (by decide) (by decide)
      · right
        exact rec731 5 131 (by decide) (by decide)
      · right
        exact rec748 5 131 (by decide) (by decide)
      · right
        exact rec765 5 131 (by decide) (by decide)
      · right
        exact rec782 5 131 (by decide) (by decide)
      · right
        exact rec799 5 131 (by decide) (by decide)
      · right
        exact rec816 5 131 (by decide) (by decide)
      · right
        exact rec833 5 131 (by decide) (by decide)
      · right
        exact rec850 5 131 (by decide) (by decide)
      · right
        exact rec867 5 131 (by decide) (by decide)
      · right
        exact rec884 5 131 (by decide) (by decide)
      · right
        exact rec901 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec919 5 131 (by decide) (by decide)
      · right
        exact rec930 5 131 (by decide) (by decide)
      · right
        exact rec941 5 131 (by decide) (by decide)
      · right
        exact rec952 5 131 (by decide) (by decide)
      · right
        exact rec963 5 131 (by decide) (by decide)
      · right
        exact rec974 5 131 (by decide) (by decide)
      · right
        exact rec985 5 131 (by decide) (by decide)
      · right
        exact rec996 5 131 (by decide) (by decide)
      · right
        exact rec1007 5 131 (by decide) (by decide)
      · right
        exact rec1018 5 131 (by decide) (by decide)
      · right
        exact rec1029 5 131 (by decide) (by decide)
      · right
        exact rec1040 5 131 (by decide) (by decide)
      · right
        exact rec1051 5 131 (by decide) (by decide)
      · right
        exact rec1062 5 131 (by decide) (by decide)
      · right
        exact rec1073 5 131 (by decide) (by decide)
      · right
        exact rec1084 5 131 (by decide) (by decide)
      · right
        exact rec1095 5 131 (by decide) (by decide)
      · right
        exact rec1106 5 131 (by decide) (by decide)
      · right
        exact rec1117 5 131 (by decide) (by decide)
      · right
        exact rec1128 5 131 (by decide) (by decide)
      · right
        exact rec1139 5 131 (by decide) (by decide)
      · right
        exact rec1150 5 131 (by decide) (by decide)
      · right
        exact rec1161 5 131 (by decide) (by decide)
      · right
        exact rec1172 5 131 (by decide) (by decide)
      · right
        exact rec1183 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 21)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1194 5 131 (by decide) (by decide)
      · right
        exact rec1201 5 131 (by decide) (by decide)
      · right
        exact rec1208 5 131 (by decide) (by decide)
      · right
        exact rec1215 5 131 (by decide) (by decide)
      · right
        exact rec1222 5 131 (by decide) (by decide)
      · right
        exact rec1229 5 131 (by decide) (by decide)
      · right
        exact rec1236 5 131 (by decide) (by decide)
      · right
        exact rec1243 5 131 (by decide) (by decide)
      · right
        exact rec1250 5 131 (by decide) (by decide)
      · right
        exact rec1257 5 131 (by decide) (by decide)
      · right
        exact rec1264 5 131 (by decide) (by decide)
      · right
        exact rec1271 5 131 (by decide) (by decide)
      · right
        exact rec1278 5 131 (by decide) (by decide)
      · right
        exact rec1285 5 131 (by decide) (by decide)
      · right
        exact rec1292 5 131 (by decide) (by decide)
      · right
        exact rec1299 5 131 (by decide) (by decide)
      · right
        exact rec1306 5 131 (by decide) (by decide)
      · right
        exact rec1313 5 131 (by decide) (by decide)
      · right
        exact rec1320 5 131 (by decide) (by decide)
      · right
        exact rec1327 5 131 (by decide) (by decide)
      · right
        exact rec1334 5 131 (by decide) (by decide)
      · right
        exact rec1341 5 131 (by decide) (by decide)
      · right
        exact rec1348 5 131 (by decide) (by decide)
      · right
        exact rec1355 5 131 (by decide) (by decide)
      · right
        exact rec1362 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1383 5 131 (by decide) (by decide)
      · right
        exact rec1404 5 131 (by decide) (by decide)
      · right
        exact rec1428 5 131 (by decide) (by decide)
      · right
        exact rec1452 5 131 (by decide) (by decide)
      · right
        exact rec1476 5 131 (by decide) (by decide)
      · right
        exact rec1500 5 131 (by decide) (by decide)
      · right
        exact rec1521 5 131 (by decide) (by decide)
      · right
        exact rec1545 5 131 (by decide) (by decide)
      · right
        exact rec1569 5 131 (by decide) (by decide)
      · right
        exact rec1593 5 131 (by decide) (by decide)
      · right
        exact rec1617 5 131 (by decide) (by decide)
      · right
        exact rec1638 5 131 (by decide) (by decide)
      · right
        exact rec1662 5 131 (by decide) (by decide)
      · right
        exact rec1686 5 131 (by decide) (by decide)
      · right
        exact rec1710 5 131 (by decide) (by decide)
      · right
        exact rec1734 5 131 (by decide) (by decide)
      · right
        exact rec1755 5 131 (by decide) (by decide)
      · right
        exact rec1779 5 131 (by decide) (by decide)
      · right
        exact rec1803 5 131 (by decide) (by decide)
      · right
        exact rec1827 5 131 (by decide) (by decide)
      · right
        exact rec1851 5 131 (by decide) (by decide)
      · right
        exact rec1872 5 131 (by decide) (by decide)
      · right
        exact rec1896 5 131 (by decide) (by decide)
      · right
        exact rec1920 5 131 (by decide) (by decide)
      · right
        exact rec1944 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 26)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1957 5 131 (by decide) (by decide)
      · right
        exact rec1973 5 131 (by decide) (by decide)
      · right
        exact rec1989 5 131 (by decide) (by decide)
      · right
        exact rec2005 5 131 (by decide) (by decide)
      · right
        exact rec2021 5 131 (by decide) (by decide)
      · right
        exact rec2037 5 131 (by decide) (by decide)
      · right
        exact rec2053 5 131 (by decide) (by decide)
      · right
        exact rec2069 5 131 (by decide) (by decide)
      · right
        exact rec2085 5 131 (by decide) (by decide)
      · right
        exact rec2101 5 131 (by decide) (by decide)
      · right
        exact rec2117 5 131 (by decide) (by decide)
      · right
        exact rec2133 5 131 (by decide) (by decide)
      · right
        exact rec2149 5 131 (by decide) (by decide)
      · right
        exact rec2165 5 131 (by decide) (by decide)
      · right
        exact rec2181 5 131 (by decide) (by decide)
      · right
        exact rec2197 5 131 (by decide) (by decide)
      · right
        exact rec2213 5 131 (by decide) (by decide)
      · right
        exact rec2229 5 131 (by decide) (by decide)
      · right
        exact rec2245 5 131 (by decide) (by decide)
      · right
        exact rec2261 5 131 (by decide) (by decide)
      · right
        exact rec2277 5 131 (by decide) (by decide)
      · right
        exact rec2293 5 131 (by decide) (by decide)
      · right
        exact rec2309 5 131 (by decide) (by decide)
      · right
        exact rec2325 5 131 (by decide) (by decide)
      · right
        exact rec2341 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
        exact rec2365 5 131 (by decide) (by decide)
      · right
        exact rec2379 5 131 (by decide) (by decide)
      · right
        exact rec2392 5 131 (by decide) (by decide)
      · right
        exact rec2419 5 131 (by decide) (by decide)
      · right
        exact rec2443 5 131 (by decide) (by decide)
      · right
        exact rec2467 5 131 (by decide) (by decide)
      · right
        exact rec2491 5 131 (by decide) (by decide)
      · right
        exact rec2515 5 131 (by decide) (by decide)
      · right
        exact rec2539 5 131 (by decide) (by decide)
      · right
        exact rec2563 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 31)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 32)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2574 5 131 (by decide) (by decide)
      · right
        exact rec2585 5 131 (by decide) (by decide)
      · right
        exact rec2597 5 131 (by decide) (by decide)
      · right
        exact rec2612 5 131 (by decide) (by decide)
      · right
        exact rec2622 5 131 (by decide) (by decide)
      · right
        exact rec2636 5 131 (by decide) (by decide)
      · right
        exact rec2648 5 131 (by decide) (by decide)
      · right
        exact rec2659 5 131 (by decide) (by decide)
      · right
        exact rec2667 5 131 (by decide) (by decide)
      · right
        exact rec2677 5 131 (by decide) (by decide)
      · right
        exact rec2694 5 131 (by decide) (by decide)
      · right
        exact rec2698 5 131 (by decide) (by decide)
      · right
        exact rec2708 5 131 (by decide) (by decide)
      · right
        exact rec2718 5 131 (by decide) (by decide)
      · right
        exact rec2732 5 131 (by decide) (by decide)
      · right
        exact rec2743 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2753 5 131 (by decide) (by decide)
      · right
        exact rec2758 5 131 (by decide) (by decide)
      · right
        exact rec2765 5 131 (by decide) (by decide)
      · right
        exact rec2782 5 131 (by decide) (by decide)
      · right
        exact rec2790 5 131 (by decide) (by decide)
      · right
        exact rec2795 5 131 (by decide) (by decide)
      · right
        exact rec2802 5 131 (by decide) (by decide)
      · right
        exact rec2819 5 131 (by decide) (by decide)
      · right
        exact rec2827 5 131 (by decide) (by decide)
      · right
        exact rec2832 5 131 (by decide) (by decide)
      · right
        exact rec2839 5 131 (by decide) (by decide)
      · right
        exact rec2856 5 131 (by decide) (by decide)
      · right
        exact rec2864 5 131 (by decide) (by decide)
      · right
        exact rec2869 5 131 (by decide) (by decide)
      · right
        exact rec2876 5 131 (by decide) (by decide)
      · right
        exact rec2893 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2900 5 131 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2911 5 131 (by decide) (by decide)
      · right
        exact rec2925 5 131 (by decide) (by decide)
      · right
        exact rec2941 5 131 (by decide) (by decide)
      · left
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
        exact rec2950 5 131 (by decide) (by decide)
      · right
        exact rec2962 5 131 (by decide) (by decide)
      · right
        exact rec2978 5 131 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2988 5 131 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 37)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
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
    exact rec361 5 132 (by decide) (by decide)
  · left
    exact rec361 5 133 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 17)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec497 5 134 (by decide) (by decide)
      · right
        exact rec514 5 134 (by decide) (by decide)
      · right
        exact rec531 5 134 (by decide) (by decide)
      · right
        exact rec548 5 134 (by decide) (by decide)
      · right
        exact rec565 5 134 (by decide) (by decide)
      · right
        exact rec582 5 134 (by decide) (by decide)
      · right
        exact rec599 5 134 (by decide) (by decide)
      · right
        exact rec616 5 134 (by decide) (by decide)
      · right
        exact rec633 5 134 (by decide) (by decide)
      · right
        exact rec650 5 134 (by decide) (by decide)
      · right
        exact rec667 5 134 (by decide) (by decide)
      · right
        exact rec684 5 134 (by decide) (by decide)
      · right
        exact rec701 5 134 (by decide) (by decide)
      · right
        exact rec718 5 134 (by decide) (by decide)
      · right
        exact rec735 5 134 (by decide) (by decide)
      · right
        exact rec752 5 134 (by decide) (by decide)
      · right
        exact rec769 5 134 (by decide) (by decide)
      · right
        exact rec786 5 134 (by decide) (by decide)
      · right
        exact rec803 5 134 (by decide) (by decide)
      · right
        exact rec820 5 134 (by decide) (by decide)
      · right
        exact rec837 5 134 (by decide) (by decide)
      · right
        exact rec854 5 134 (by decide) (by decide)
      · right
        exact rec871 5 134 (by decide) (by decide)
      · right
        exact rec888 5 134 (by decide) (by decide)
      · right
        exact rec905 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec922 5 134 (by decide) (by decide)
      · right
        exact rec933 5 134 (by decide) (by decide)
      · right
        exact rec944 5 134 (by decide) (by decide)
      · right
        exact rec955 5 134 (by decide) (by decide)
      · right
        exact rec966 5 134 (by decide) (by decide)
      · right
        exact rec977 5 134 (by decide) (by decide)
      · right
        exact rec988 5 134 (by decide) (by decide)
      · right
        exact rec999 5 134 (by decide) (by decide)
      · right
        exact rec1010 5 134 (by decide) (by decide)
      · right
        exact rec1021 5 134 (by decide) (by decide)
      · right
        exact rec1032 5 134 (by decide) (by decide)
      · right
        exact rec1043 5 134 (by decide) (by decide)
      · right
        exact rec1054 5 134 (by decide) (by decide)
      · right
        exact rec1065 5 134 (by decide) (by decide)
      · right
        exact rec1076 5 134 (by decide) (by decide)
      · right
        exact rec1087 5 134 (by decide) (by decide)
      · right
        exact rec1098 5 134 (by decide) (by decide)
      · right
        exact rec1109 5 134 (by decide) (by decide)
      · right
        exact rec1120 5 134 (by decide) (by decide)
      · right
        exact rec1131 5 134 (by decide) (by decide)
      · right
        exact rec1142 5 134 (by decide) (by decide)
      · right
        exact rec1153 5 134 (by decide) (by decide)
      · right
        exact rec1164 5 134 (by decide) (by decide)
      · right
        exact rec1175 5 134 (by decide) (by decide)
      · right
        exact rec1186 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 21)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1196 5 134 (by decide) (by decide)
      · right
        exact rec1203 5 134 (by decide) (by decide)
      · right
        exact rec1210 5 134 (by decide) (by decide)
      · right
        exact rec1217 5 134 (by decide) (by decide)
      · right
        exact rec1224 5 134 (by decide) (by decide)
      · right
        exact rec1231 5 134 (by decide) (by decide)
      · right
        exact rec1238 5 134 (by decide) (by decide)
      · right
        exact rec1245 5 134 (by decide) (by decide)
      · right
        exact rec1252 5 134 (by decide) (by decide)
      · right
        exact rec1259 5 134 (by decide) (by decide)
      · right
        exact rec1266 5 134 (by decide) (by decide)
      · right
        exact rec1273 5 134 (by decide) (by decide)
      · right
        exact rec1280 5 134 (by decide) (by decide)
      · right
        exact rec1287 5 134 (by decide) (by decide)
      · right
        exact rec1294 5 134 (by decide) (by decide)
      · right
        exact rec1301 5 134 (by decide) (by decide)
      · right
        exact rec1308 5 134 (by decide) (by decide)
      · right
        exact rec1315 5 134 (by decide) (by decide)
      · right
        exact rec1322 5 134 (by decide) (by decide)
      · right
        exact rec1329 5 134 (by decide) (by decide)
      · right
        exact rec1336 5 134 (by decide) (by decide)
      · right
        exact rec1343 5 134 (by decide) (by decide)
      · right
        exact rec1350 5 134 (by decide) (by decide)
      · right
        exact rec1357 5 134 (by decide) (by decide)
      · right
        exact rec1364 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1374 5 134 (by decide) (by decide)
      · right
        exact rec1395 5 134 (by decide) (by decide)
      · right
        exact rec1419 5 134 (by decide) (by decide)
      · right
        exact rec1443 5 134 (by decide) (by decide)
      · right
        exact rec1467 5 134 (by decide) (by decide)
      · right
        exact rec1491 5 134 (by decide) (by decide)
      · right
        exact rec1512 5 134 (by decide) (by decide)
      · right
        exact rec1536 5 134 (by decide) (by decide)
      · right
        exact rec1560 5 134 (by decide) (by decide)
      · right
        exact rec1584 5 134 (by decide) (by decide)
      · right
        exact rec1608 5 134 (by decide) (by decide)
      · right
        exact rec1629 5 134 (by decide) (by decide)
      · right
        exact rec1653 5 134 (by decide) (by decide)
      · right
        exact rec1677 5 134 (by decide) (by decide)
      · right
        exact rec1701 5 134 (by decide) (by decide)
      · right
        exact rec1725 5 134 (by decide) (by decide)
      · right
        exact rec1746 5 134 (by decide) (by decide)
      · right
        exact rec1770 5 134 (by decide) (by decide)
      · right
        exact rec1794 5 134 (by decide) (by decide)
      · right
        exact rec1818 5 134 (by decide) (by decide)
      · right
        exact rec1842 5 134 (by decide) (by decide)
      · right
        exact rec1863 5 134 (by decide) (by decide)
      · right
        exact rec1887 5 134 (by decide) (by decide)
      · right
        exact rec1911 5 134 (by decide) (by decide)
      · right
        exact rec1935 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 26)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1960 5 134 (by decide) (by decide)
      · right
        exact rec1976 5 134 (by decide) (by decide)
      · right
        exact rec1992 5 134 (by decide) (by decide)
      · right
        exact rec2008 5 134 (by decide) (by decide)
      · right
        exact rec2024 5 134 (by decide) (by decide)
      · right
        exact rec2040 5 134 (by decide) (by decide)
      · right
        exact rec2056 5 134 (by decide) (by decide)
      · right
        exact rec2072 5 134 (by decide) (by decide)
      · right
        exact rec2088 5 134 (by decide) (by decide)
      · right
        exact rec2104 5 134 (by decide) (by decide)
      · right
        exact rec2120 5 134 (by decide) (by decide)
      · right
        exact rec2136 5 134 (by decide) (by decide)
      · right
        exact rec2152 5 134 (by decide) (by decide)
      · right
        exact rec2168 5 134 (by decide) (by decide)
      · right
        exact rec2184 5 134 (by decide) (by decide)
      · right
        exact rec2200 5 134 (by decide) (by decide)
      · right
        exact rec2216 5 134 (by decide) (by decide)
      · right
        exact rec2232 5 134 (by decide) (by decide)
      · right
        exact rec2248 5 134 (by decide) (by decide)
      · right
        exact rec2264 5 134 (by decide) (by decide)
      · right
        exact rec2280 5 134 (by decide) (by decide)
      · right
        exact rec2296 5 134 (by decide) (by decide)
      · right
        exact rec2312 5 134 (by decide) (by decide)
      · right
        exact rec2328 5 134 (by decide) (by decide)
      · right
        exact rec2344 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
        exact rec2365 5 134 (by decide) (by decide)
      · right
        exact rec2379 5 134 (by decide) (by decide)
      · right
        exact rec2390 5 134 (by decide) (by decide)
      · right
        exact rec2412 5 134 (by decide) (by decide)
      · right
        exact rec2436 5 134 (by decide) (by decide)
      · right
        exact rec2460 5 134 (by decide) (by decide)
      · right
        exact rec2484 5 134 (by decide) (by decide)
      · right
        exact rec2508 5 134 (by decide) (by decide)
      · right
        exact rec2532 5 134 (by decide) (by decide)
      · right
        exact rec2556 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 31)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 32)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2575 5 134 (by decide) (by decide)
      · right
        exact rec2584 5 134 (by decide) (by decide)
      · right
        exact rec2597 5 134 (by decide) (by decide)
      · right
        exact rec2610 5 134 (by decide) (by decide)
      · right
        exact rec2623 5 134 (by decide) (by decide)
      · right
        exact rec2635 5 134 (by decide) (by decide)
      · right
        exact rec2646 5 134 (by decide) (by decide)
      · right
        exact rec2657 5 134 (by decide) (by decide)
      · right
        exact rec2671 5 134 (by decide) (by decide)
      · right
        exact rec2681 5 134 (by decide) (by decide)
      · right
        exact rec2692 5 134 (by decide) (by decide)
      · right
        exact rec2701 5 134 (by decide) (by decide)
      · right
        exact rec2710 5 134 (by decide) (by decide)
      · right
        exact rec2722 5 134 (by decide) (by decide)
      · right
        exact rec2735 5 134 (by decide) (by decide)
      · right
        exact rec2746 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2754 5 134 (by decide) (by decide)
      · right
        exact rec2759 5 134 (by decide) (by decide)
      · right
        exact rec2769 5 134 (by decide) (by decide)
      · right
        exact rec2783 5 134 (by decide) (by decide)
      · right
        exact rec2791 5 134 (by decide) (by decide)
      · right
        exact rec2796 5 134 (by decide) (by decide)
      · right
        exact rec2806 5 134 (by decide) (by decide)
      · right
        exact rec2820 5 134 (by decide) (by decide)
      · right
        exact rec2828 5 134 (by decide) (by decide)
      · right
        exact rec2833 5 134 (by decide) (by decide)
      · right
        exact rec2843 5 134 (by decide) (by decide)
      · right
        exact rec2857 5 134 (by decide) (by decide)
      · right
        exact rec2865 5 134 (by decide) (by decide)
      · right
        exact rec2870 5 134 (by decide) (by decide)
      · right
        exact rec2880 5 134 (by decide) (by decide)
      · right
        exact rec2894 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2903 5 134 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2913 5 134 (by decide) (by decide)
      · right
        exact rec2923 5 134 (by decide) (by decide)
      · right
        exact rec2936 5 134 (by decide) (by decide)
      · left
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
        exact rec2953 5 134 (by decide) (by decide)
      · right
        exact rec2960 5 134 (by decide) (by decide)
      · right
        exact rec2977 5 134 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2986 5 134 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 37)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
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
    intro gs hgs
    change gs ∈ [(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 17)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec498 5 135 (by decide) (by decide)
      · right
        exact rec515 5 135 (by decide) (by decide)
      · right
        exact rec532 5 135 (by decide) (by decide)
      · right
        exact rec549 5 135 (by decide) (by decide)
      · right
        exact rec566 5 135 (by decide) (by decide)
      · right
        exact rec583 5 135 (by decide) (by decide)
      · right
        exact rec600 5 135 (by decide) (by decide)
      · right
        exact rec617 5 135 (by decide) (by decide)
      · right
        exact rec634 5 135 (by decide) (by decide)
      · right
        exact rec651 5 135 (by decide) (by decide)
      · right
        exact rec668 5 135 (by decide) (by decide)
      · right
        exact rec685 5 135 (by decide) (by decide)
      · right
        exact rec702 5 135 (by decide) (by decide)
      · right
        exact rec719 5 135 (by decide) (by decide)
      · right
        exact rec736 5 135 (by decide) (by decide)
      · right
        exact rec753 5 135 (by decide) (by decide)
      · right
        exact rec770 5 135 (by decide) (by decide)
      · right
        exact rec787 5 135 (by decide) (by decide)
      · right
        exact rec804 5 135 (by decide) (by decide)
      · right
        exact rec821 5 135 (by decide) (by decide)
      · right
        exact rec838 5 135 (by decide) (by decide)
      · right
        exact rec855 5 135 (by decide) (by decide)
      · right
        exact rec872 5 135 (by decide) (by decide)
      · right
        exact rec889 5 135 (by decide) (by decide)
      · right
        exact rec906 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec923 5 135 (by decide) (by decide)
      · right
        exact rec934 5 135 (by decide) (by decide)
      · right
        exact rec945 5 135 (by decide) (by decide)
      · right
        exact rec956 5 135 (by decide) (by decide)
      · right
        exact rec967 5 135 (by decide) (by decide)
      · right
        exact rec978 5 135 (by decide) (by decide)
      · right
        exact rec989 5 135 (by decide) (by decide)
      · right
        exact rec1000 5 135 (by decide) (by decide)
      · right
        exact rec1011 5 135 (by decide) (by decide)
      · right
        exact rec1022 5 135 (by decide) (by decide)
      · right
        exact rec1033 5 135 (by decide) (by decide)
      · right
        exact rec1044 5 135 (by decide) (by decide)
      · right
        exact rec1055 5 135 (by decide) (by decide)
      · right
        exact rec1066 5 135 (by decide) (by decide)
      · right
        exact rec1077 5 135 (by decide) (by decide)
      · right
        exact rec1088 5 135 (by decide) (by decide)
      · right
        exact rec1099 5 135 (by decide) (by decide)
      · right
        exact rec1110 5 135 (by decide) (by decide)
      · right
        exact rec1121 5 135 (by decide) (by decide)
      · right
        exact rec1132 5 135 (by decide) (by decide)
      · right
        exact rec1143 5 135 (by decide) (by decide)
      · right
        exact rec1154 5 135 (by decide) (by decide)
      · right
        exact rec1165 5 135 (by decide) (by decide)
      · right
        exact rec1176 5 135 (by decide) (by decide)
      · right
        exact rec1187 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 21)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1197 5 135 (by decide) (by decide)
      · right
        exact rec1204 5 135 (by decide) (by decide)
      · right
        exact rec1211 5 135 (by decide) (by decide)
      · right
        exact rec1218 5 135 (by decide) (by decide)
      · right
        exact rec1225 5 135 (by decide) (by decide)
      · right
        exact rec1232 5 135 (by decide) (by decide)
      · right
        exact rec1239 5 135 (by decide) (by decide)
      · right
        exact rec1246 5 135 (by decide) (by decide)
      · right
        exact rec1253 5 135 (by decide) (by decide)
      · right
        exact rec1260 5 135 (by decide) (by decide)
      · right
        exact rec1267 5 135 (by decide) (by decide)
      · right
        exact rec1274 5 135 (by decide) (by decide)
      · right
        exact rec1281 5 135 (by decide) (by decide)
      · right
        exact rec1288 5 135 (by decide) (by decide)
      · right
        exact rec1295 5 135 (by decide) (by decide)
      · right
        exact rec1302 5 135 (by decide) (by decide)
      · right
        exact rec1309 5 135 (by decide) (by decide)
      · right
        exact rec1316 5 135 (by decide) (by decide)
      · right
        exact rec1323 5 135 (by decide) (by decide)
      · right
        exact rec1330 5 135 (by decide) (by decide)
      · right
        exact rec1337 5 135 (by decide) (by decide)
      · right
        exact rec1344 5 135 (by decide) (by decide)
      · right
        exact rec1351 5 135 (by decide) (by decide)
      · right
        exact rec1358 5 135 (by decide) (by decide)
      · right
        exact rec1365 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1382 5 135 (by decide) (by decide)
      · right
        exact rec1403 5 135 (by decide) (by decide)
      · right
        exact rec1427 5 135 (by decide) (by decide)
      · right
        exact rec1451 5 135 (by decide) (by decide)
      · right
        exact rec1475 5 135 (by decide) (by decide)
      · right
        exact rec1499 5 135 (by decide) (by decide)
      · right
        exact rec1520 5 135 (by decide) (by decide)
      · right
        exact rec1544 5 135 (by decide) (by decide)
      · right
        exact rec1568 5 135 (by decide) (by decide)
      · right
        exact rec1592 5 135 (by decide) (by decide)
      · right
        exact rec1616 5 135 (by decide) (by decide)
      · right
        exact rec1637 5 135 (by decide) (by decide)
      · right
        exact rec1661 5 135 (by decide) (by decide)
      · right
        exact rec1685 5 135 (by decide) (by decide)
      · right
        exact rec1709 5 135 (by decide) (by decide)
      · right
        exact rec1733 5 135 (by decide) (by decide)
      · right
        exact rec1754 5 135 (by decide) (by decide)
      · right
        exact rec1778 5 135 (by decide) (by decide)
      · right
        exact rec1802 5 135 (by decide) (by decide)
      · right
        exact rec1826 5 135 (by decide) (by decide)
      · right
        exact rec1850 5 135 (by decide) (by decide)
      · right
        exact rec1871 5 135 (by decide) (by decide)
      · right
        exact rec1895 5 135 (by decide) (by decide)
      · right
        exact rec1919 5 135 (by decide) (by decide)
      · right
        exact rec1943 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 26)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1960 5 135 (by decide) (by decide)
      · right
        exact rec1976 5 135 (by decide) (by decide)
      · right
        exact rec1992 5 135 (by decide) (by decide)
      · right
        exact rec2008 5 135 (by decide) (by decide)
      · right
        exact rec2024 5 135 (by decide) (by decide)
      · right
        exact rec2040 5 135 (by decide) (by decide)
      · right
        exact rec2056 5 135 (by decide) (by decide)
      · right
        exact rec2072 5 135 (by decide) (by decide)
      · right
        exact rec2088 5 135 (by decide) (by decide)
      · right
        exact rec2104 5 135 (by decide) (by decide)
      · right
        exact rec2120 5 135 (by decide) (by decide)
      · right
        exact rec2136 5 135 (by decide) (by decide)
      · right
        exact rec2152 5 135 (by decide) (by decide)
      · right
        exact rec2168 5 135 (by decide) (by decide)
      · right
        exact rec2184 5 135 (by decide) (by decide)
      · right
        exact rec2200 5 135 (by decide) (by decide)
      · right
        exact rec2216 5 135 (by decide) (by decide)
      · right
        exact rec2232 5 135 (by decide) (by decide)
      · right
        exact rec2248 5 135 (by decide) (by decide)
      · right
        exact rec2264 5 135 (by decide) (by decide)
      · right
        exact rec2280 5 135 (by decide) (by decide)
      · right
        exact rec2296 5 135 (by decide) (by decide)
      · right
        exact rec2312 5 135 (by decide) (by decide)
      · right
        exact rec2328 5 135 (by decide) (by decide)
      · right
        exact rec2344 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
        exact rec2365 5 135 (by decide) (by decide)
      · right
        exact rec2379 5 135 (by decide) (by decide)
      · right
        exact rec2391 5 135 (by decide) (by decide)
      · right
        exact rec2418 5 135 (by decide) (by decide)
      · right
        exact rec2442 5 135 (by decide) (by decide)
      · right
        exact rec2466 5 135 (by decide) (by decide)
      · right
        exact rec2490 5 135 (by decide) (by decide)
      · right
        exact rec2514 5 135 (by decide) (by decide)
      · right
        exact rec2538 5 135 (by decide) (by decide)
      · right
        exact rec2562 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 31)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 32)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2575 5 135 (by decide) (by decide)
      · right
        exact rec2584 5 135 (by decide) (by decide)
      · right
        exact rec2597 5 135 (by decide) (by decide)
      · right
        exact rec2613 5 135 (by decide) (by decide)
      · right
        exact rec2625 5 135 (by decide) (by decide)
      · right
        exact rec2635 5 135 (by decide) (by decide)
      · right
        exact rec2649 5 135 (by decide) (by decide)
      · right
        exact rec2660 5 135 (by decide) (by decide)
      · right
        exact rec2672 5 135 (by decide) (by decide)
      · right
        exact rec2682 5 135 (by decide) (by decide)
      · right
        exact rec2695 5 135 (by decide) (by decide)
      · right
        exact rec2702 5 135 (by decide) (by decide)
      · right
        exact rec2711 5 135 (by decide) (by decide)
      · right
        exact rec2722 5 135 (by decide) (by decide)
      · right
        exact rec2735 5 135 (by decide) (by decide)
      · right
        exact rec2746 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2754 5 135 (by decide) (by decide)
      · right
        exact rec2759 5 135 (by decide) (by decide)
      · right
        exact rec2768 5 135 (by decide) (by decide)
      · right
        exact rec2784 5 135 (by decide) (by decide)
      · right
        exact rec2791 5 135 (by decide) (by decide)
      · right
        exact rec2796 5 135 (by decide) (by decide)
      · right
        exact rec2804 5 135 (by decide) (by decide)
      · right
        exact rec2821 5 135 (by decide) (by decide)
      · right
        exact rec2828 5 135 (by decide) (by decide)
      · right
        exact rec2833 5 135 (by decide) (by decide)
      · right
        exact rec2841 5 135 (by decide) (by decide)
      · right
        exact rec2858 5 135 (by decide) (by decide)
      · right
        exact rec2865 5 135 (by decide) (by decide)
      · right
        exact rec2870 5 135 (by decide) (by decide)
      · right
        exact rec2878 5 135 (by decide) (by decide)
      · right
        exact rec2895 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2904 5 135 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2914 5 135 (by decide) (by decide)
      · right
        exact rec2926 5 135 (by decide) (by decide)
      · right
        exact rec2937 5 135 (by decide) (by decide)
      · left
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
        exact rec2953 5 135 (by decide) (by decide)
      · right
        exact rec2963 5 135 (by decide) (by decide)
      · right
        exact rec2978 5 135 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2989 5 135 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 37)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
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
    exact rec388 5 136 (by decide) (by decide)
  · left
    exact rec388 5 137 (by decide) (by decide)
  · left
    exact rec362 5 138 (by decide) (by decide)
  · left
    exact rec362 5 139 (by decide) (by decide)
  · left
    exact rec388 5 140 (by decide) (by decide)
  · left
    exact rec388 5 141 (by decide) (by decide)
  · left
    exact rec362 5 142 (by decide) (by decide)
  · left
    exact rec362 5 143 (by decide) (by decide)
end Section14Coverage_5_1_p128_144

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0128_0144


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0144_0160
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p144_160
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec441 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[5],[151],1397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[441]? = some (⟨16,(-1),[5],[151],1397⟩) from rfl))
private theorem rec445 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[5,6],[147],1397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[445]? = some (⟨16,(-1),[5,6],[147],1397⟩) from rfl))
private theorem rec494 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[494]? = some (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec504 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[5],[146],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[504]? = some (⟨18,(0),[5],[146],160⟩) from rfl))
private theorem rec511 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[511]? = some (⟨18,(1),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec521 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[5],[146],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[521]? = some (⟨18,(1),[5],[146],160⟩) from rfl))
private theorem rec528 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[528]? = some (⟨18,(2),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec538 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[5],[146],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[538]? = some (⟨18,(2),[5],[146],160⟩) from rfl))
private theorem rec545 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[545]? = some (⟨18,(3),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec555 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[5],[146],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[555]? = some (⟨18,(3),[5],[146],160⟩) from rfl))
private theorem rec562 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[562]? = some (⟨18,(4),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec572 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[5],[146],160⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[572]? = some (⟨18,(4),[5],[146],160⟩) from rfl))
private theorem rec579 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[579]? = some (⟨18,(5),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec589 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[5],[146],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[589]? = some (⟨18,(5),[5],[146],161⟩) from rfl))
private theorem rec596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[596]? = some (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec606 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[5],[146],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[606]? = some (⟨18,(6),[5],[146],161⟩) from rfl))
private theorem rec613 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[613]? = some (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec623 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[5],[146],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[623]? = some (⟨18,(7),[5],[146],161⟩) from rfl))
private theorem rec630 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[630]? = some (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec640 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[5],[146],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[640]? = some (⟨18,(8),[5],[146],161⟩) from rfl))
private theorem rec647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[647]? = some (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec657 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[5],[146],161⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[657]? = some (⟨18,(9),[5],[146],161⟩) from rfl))
private theorem rec664 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[664]? = some (⟨18,(10),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec674 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[5],[146],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[674]? = some (⟨18,(10),[5],[146],162⟩) from rfl))
private theorem rec681 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[681]? = some (⟨18,(11),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec691 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[5],[146],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[691]? = some (⟨18,(11),[5],[146],163⟩) from rfl))
private theorem rec698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,2,5,6,13,14],[150],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[698]? = some (⟨18,(12),[1,2,5,6,13,14],[150],129⟩) from rfl))
private theorem rec708 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[5],[146],164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[708]? = some (⟨18,(12),[5],[146],164⟩) from rfl))
private theorem rec715 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[715]? = some (⟨18,(13),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec725 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[5],[146],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[725]? = some (⟨18,(13),[5],[146],163⟩) from rfl))
private theorem rec732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,2,5,6,13,14],[150],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[732]? = some (⟨18,(14),[1,2,5,6,13,14],[150],130⟩) from rfl))
private theorem rec742 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[5],[146],165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[742]? = some (⟨18,(14),[5],[146],165⟩) from rfl))
private theorem rec749 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[749]? = some (⟨18,(15),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec759 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[5],[146],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[759]? = some (⟨18,(15),[5],[146],162⟩) from rfl))
private theorem rec766 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[766]? = some (⟨18,(16),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec776 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[5],[146],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[776]? = some (⟨18,(16),[5],[146],166⟩) from rfl))
private theorem rec783 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[783]? = some (⟨18,(17),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec793 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[5],[146],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[793]? = some (⟨18,(17),[5],[146],166⟩) from rfl))
private theorem rec800 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[800]? = some (⟨18,(18),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec810 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[5],[146],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[810]? = some (⟨18,(18),[5],[146],166⟩) from rfl))
private theorem rec817 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[817]? = some (⟨18,(19),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec827 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[5],[146],166⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[827]? = some (⟨18,(19),[5],[146],166⟩) from rfl))
private theorem rec834 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[834]? = some (⟨18,(20),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec844 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[5],[146],162⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[844]? = some (⟨18,(20),[5],[146],162⟩) from rfl))
private theorem rec851 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[851]? = some (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec861 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[5],[146],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[861]? = some (⟨18,(21),[5],[146],163⟩) from rfl))
private theorem rec868 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[868]? = some (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) from rfl))
private theorem rec878 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[5],[146],164⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[878]? = some (⟨18,(22),[5],[146],164⟩) from rfl))
private theorem rec885 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[885]? = some (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec895 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[5],[146],163⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[895]? = some (⟨18,(23),[5],[146],163⟩) from rfl))
private theorem rec902 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,2,5,6,13,14],[150],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[902]? = some (⟨18,(24),[1,2,5,6,13,14],[150],130⟩) from rfl))
private theorem rec912 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[5],[146],165⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[912]? = some (⟨18,(24),[5],[146],165⟩) from rfl))
private theorem rec919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[919]? = some (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[930]? = some (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec941 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[941]? = some (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec952 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[952]? = some (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec963 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[963]? = some (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[974]? = some (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec985 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[985]? = some (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec996 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[996]? = some (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1007 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1007]? = some (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1018 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1018]? = some (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1029 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1029]? = some (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1040 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1040]? = some (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1051]? = some (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1062 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1062]? = some (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1073 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1073]? = some (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1084 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1084]? = some (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1095 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1095]? = some (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1106 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1106]? = some (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1117]? = some (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1128 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1128]? = some (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1139 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1139]? = some (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1150]? = some (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1161 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1161]? = some (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1172 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[3]? = some (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1183 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[14]? = some (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1194 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[25]? = some (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1201 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[32]? = some (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1208 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[39]? = some (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1215 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[46]? = some (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1222 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[53]? = some (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[60]? = some (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1236 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[67]? = some (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1243 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[74]? = some (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1250 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[81]? = some (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1257 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[88]? = some (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[95]? = some (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[102]? = some (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[109]? = some (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[116]? = some (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[123]? = some (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1299 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[130]? = some (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1306 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[137]? = some (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[144]? = some (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[151]? = some (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1327 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[158]? = some (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[165]? = some (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[172]? = some (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1348 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[179]? = some (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[186]? = some (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[193]? = some (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1369 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,5,6,13,14],[146],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[200]? = some (⟨25,(0),[1,2,5,6,13,14],[146],145⟩) from rfl))
private theorem rec1370 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,5,6,13,14],[150],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[201]? = some (⟨25,(0),[1,2,5,6,13,14],[150],189⟩) from rfl))
private theorem rec1390 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,5,6,13,14],[146],146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[221]? = some (⟨25,(1),[1,2,5,6,13,14],[146],146⟩) from rfl))
private theorem rec1405 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[5,6],[150],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[236]? = some (⟨25,(1),[5,6],[150],216⟩) from rfl))
private theorem rec1414 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,5,6,13,14],[146],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[245]? = some (⟨25,(2),[1,2,5,6,13,14],[146],145⟩) from rfl))
private theorem rec1429 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[5,6],[150],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[260]? = some (⟨25,(2),[5,6],[150],217⟩) from rfl))
private theorem rec1438 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,5,6,13,14],[146],147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[269]? = some (⟨25,(3),[1,2,5,6,13,14],[146],147⟩) from rfl))
private theorem rec1453 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[5,6],[150],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[284]? = some (⟨25,(3),[5,6],[150],218⟩) from rfl))
private theorem rec1462 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,5,6,13,14],[146],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[293]? = some (⟨25,(4),[1,2,5,6,13,14],[146],148⟩) from rfl))
private theorem rec1477 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[5,6],[150],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[308]? = some (⟨25,(4),[5,6],[150],219⟩) from rfl))
private theorem rec1486 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,5,6,13,14],[146],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[317]? = some (⟨25,(5),[1,2,5,6,13,14],[146],145⟩) from rfl))
private theorem rec1487 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,5,6,13,14],[150],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[318]? = some (⟨25,(5),[1,2,5,6,13,14],[150],189⟩) from rfl))
private theorem rec1507 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,5,6,13,14],[146],146⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[338]? = some (⟨25,(6),[1,2,5,6,13,14],[146],146⟩) from rfl))
private theorem rec1522 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[5,6],[150],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[353]? = some (⟨25,(6),[5,6],[150],216⟩) from rfl))
private theorem rec1531 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,5,6,13,14],[146],145⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[362]? = some (⟨25,(7),[1,2,5,6,13,14],[146],145⟩) from rfl))
private theorem rec1546 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[5,6],[150],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[377]? = some (⟨25,(7),[5,6],[150],217⟩) from rfl))
private theorem rec1555 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,5,6,13,14],[146],147⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[386]? = some (⟨25,(8),[1,2,5,6,13,14],[146],147⟩) from rfl))
private theorem rec1570 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[5,6],[150],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[401]? = some (⟨25,(8),[5,6],[150],218⟩) from rfl))
private theorem rec1579 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,5,6,13,14],[146],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[410]? = some (⟨25,(9),[1,2,5,6,13,14],[146],148⟩) from rfl))
private theorem rec1594 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[5,6],[150],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[425]? = some (⟨25,(9),[5,6],[150],219⟩) from rfl))
private theorem rec1603 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,5,6,13,14],[146],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[434]? = some (⟨25,(10),[1,2,5,6,13,14],[146],149⟩) from rfl))
private theorem rec1604 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,5,6,13,14],[150],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[435]? = some (⟨25,(10),[1,2,5,6,13,14],[150],194⟩) from rfl))
private theorem rec1624 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,5,6,13,14],[146],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[455]? = some (⟨25,(11),[1,2,5,6,13,14],[146],149⟩) from rfl))
private theorem rec1639 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[5,6],[150],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[470]? = some (⟨25,(11),[5,6],[150],220⟩) from rfl))
private theorem rec1648 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,5,6,13,14],[146],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[479]? = some (⟨25,(12),[1,2,5,6,13,14],[146],149⟩) from rfl))
private theorem rec1663 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[5,6],[150],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[494]? = some (⟨25,(12),[5,6],[150],220⟩) from rfl))
private theorem rec1672 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,5,6,13,14],[146],149⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[503]? = some (⟨25,(13),[1,2,5,6,13,14],[146],149⟩) from rfl))
private theorem rec1687 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[5,6],[150],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[518]? = some (⟨25,(13),[5,6],[150],220⟩) from rfl))
private theorem rec1696 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,5,6,13,14],[146],148⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[527]? = some (⟨25,(14),[1,2,5,6,13,14],[146],148⟩) from rfl))
private theorem rec1711 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[5,6],[150],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[542]? = some (⟨25,(14),[5,6],[150],219⟩) from rfl))
private theorem rec1720 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[551]? = some (⟨25,(15),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1721 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,5,6,13,14],[150],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[552]? = some (⟨25,(15),[1,2,5,6,13,14],[150],196⟩) from rfl))
private theorem rec1741 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[572]? = some (⟨25,(16),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1756 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[5,6],[150],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[587]? = some (⟨25,(16),[5,6],[150],221⟩) from rfl))
private theorem rec1765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[596]? = some (⟨25,(17),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1780 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[5,6],[150],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[611]? = some (⟨25,(17),[5,6],[150],221⟩) from rfl))
private theorem rec1789 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[620]? = some (⟨25,(18),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1804 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[5,6],[150],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[635]? = some (⟨25,(18),[5,6],[150],221⟩) from rfl))
private theorem rec1813 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,5,6,13,14],[146],150⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[644]? = some (⟨25,(19),[1,2,5,6,13,14],[146],150⟩) from rfl))
private theorem rec1828 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[5,6],[150],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[659]? = some (⟨25,(19),[5,6],[150],221⟩) from rfl))
private theorem rec1837 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[668]? = some (⟨25,(20),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1838 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,5,6,13,14],[150],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[669]? = some (⟨25,(20),[1,2,5,6,13,14],[150],198⟩) from rfl))
private theorem rec1858 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[689]? = some (⟨25,(21),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1873 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[5,6],[150],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[704]? = some (⟨25,(21),[5,6],[150],222⟩) from rfl))
private theorem rec1882 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[713]? = some (⟨25,(22),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1897 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[5,6],[150],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[728]? = some (⟨25,(22),[5,6],[150],222⟩) from rfl))
private theorem rec1906 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[737]? = some (⟨25,(23),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1921 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[5,6],[150],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[752]? = some (⟨25,(23),[5,6],[150],222⟩) from rfl))
private theorem rec1930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,5,6,13,14],[146],151⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[761]? = some (⟨25,(24),[1,2,5,6,13,14],[146],151⟩) from rfl))
private theorem rec1945 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[5,6],[150],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[776]? = some (⟨25,(24),[5,6],[150],222⟩) from rfl))
private theorem rec1958 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[789]? = some (⟨28,(0),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec1963 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[5],[146],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[794]? = some (⟨28,(0),[5],[146],174⟩) from rfl))
private theorem rec1974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[805]? = some (⟨28,(1),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec1979 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[5],[146],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[810]? = some (⟨28,(1),[5],[146],174⟩) from rfl))
private theorem rec1990 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[821]? = some (⟨28,(2),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec1995 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[5],[146],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[826]? = some (⟨28,(2),[5],[146],174⟩) from rfl))
private theorem rec2006 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[837]? = some (⟨28,(3),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec2011 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[5],[146],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[842]? = some (⟨28,(3),[5],[146],174⟩) from rfl))
private theorem rec2022 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[853]? = some (⟨28,(4),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec2027 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[5],[146],174⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[858]? = some (⟨28,(4),[5],[146],174⟩) from rfl))
private theorem rec2038 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[869]? = some (⟨28,(5),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2043 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[5],[146],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[874]? = some (⟨28,(5),[5],[146],175⟩) from rfl))
private theorem rec2054 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[885]? = some (⟨28,(6),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2059 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[5],[146],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[890]? = some (⟨28,(6),[5],[146],175⟩) from rfl))
private theorem rec2070 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[901]? = some (⟨28,(7),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2075 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[5],[146],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[906]? = some (⟨28,(7),[5],[146],175⟩) from rfl))
private theorem rec2086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[917]? = some (⟨28,(8),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2091 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[5],[146],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[922]? = some (⟨28,(8),[5],[146],175⟩) from rfl))
private theorem rec2102 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[933]? = some (⟨28,(9),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2107 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[5],[146],175⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[938]? = some (⟨28,(9),[5],[146],175⟩) from rfl))
private theorem rec2118 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[949]? = some (⟨28,(10),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2123 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[5],[146],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[954]? = some (⟨28,(10),[5],[146],176⟩) from rfl))
private theorem rec2134 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[965]? = some (⟨28,(11),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2139 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[5],[146],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[970]? = some (⟨28,(11),[5],[146],177⟩) from rfl))
private theorem rec2150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,2,5,6],[150],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[981]? = some (⟨28,(12),[1,2,5,6],[150],136⟩) from rfl))
private theorem rec2155 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[5],[146],178⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[986]? = some (⟨28,(12),[5],[146],178⟩) from rfl))
private theorem rec2166 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[997]? = some (⟨28,(13),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2171 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[5],[146],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1002]? = some (⟨28,(13),[5],[146],177⟩) from rfl))
private theorem rec2182 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,2,5,6],[150],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1013]? = some (⟨28,(14),[1,2,5,6],[150],137⟩) from rfl))
private theorem rec2187 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[5],[146],179⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1018]? = some (⟨28,(14),[5],[146],179⟩) from rfl))
private theorem rec2198 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1029]? = some (⟨28,(15),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2203 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[5],[146],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1034]? = some (⟨28,(15),[5],[146],176⟩) from rfl))
private theorem rec2214 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1045]? = some (⟨28,(16),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2219 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[5],[146],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1050]? = some (⟨28,(16),[5],[146],180⟩) from rfl))
private theorem rec2230 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1061]? = some (⟨28,(17),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2235 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[5],[146],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1066]? = some (⟨28,(17),[5],[146],180⟩) from rfl))
private theorem rec2246 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1077]? = some (⟨28,(18),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2251 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[5],[146],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1082]? = some (⟨28,(18),[5],[146],180⟩) from rfl))
private theorem rec2262 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1093]? = some (⟨28,(19),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2267 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[5],[146],180⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1098]? = some (⟨28,(19),[5],[146],180⟩) from rfl))
private theorem rec2278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1109]? = some (⟨28,(20),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2283 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[5],[146],176⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1114]? = some (⟨28,(20),[5],[146],176⟩) from rfl))
private theorem rec2294 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1125]? = some (⟨28,(21),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2299 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[5],[146],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1130]? = some (⟨28,(21),[5],[146],177⟩) from rfl))
private theorem rec2310 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,2,5,6],[150],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1141]? = some (⟨28,(22),[1,2,5,6],[150],136⟩) from rfl))
private theorem rec2315 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[5],[146],178⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1146]? = some (⟨28,(22),[5],[146],178⟩) from rfl))
private theorem rec2326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1157]? = some (⟨28,(23),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2331 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[5],[146],177⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1162]? = some (⟨28,(23),[5],[146],177⟩) from rfl))
private theorem rec2342 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,2,5,6],[150],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1173]? = some (⟨28,(24),[1,2,5,6],[150],137⟩) from rfl))
private theorem rec2347 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[5],[146],179⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1178]? = some (⟨28,(24),[5],[146],179⟩) from rfl))
private theorem rec2358 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1,2,5,6],[146,150],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1189]? = some (⟨30,(0),[1,2,5,6],[146,150],152⟩) from rfl))
private theorem rec2374 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[1,2,5,6],[146,150],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1205]? = some (⟨30,(1),[1,2,5,6],[146,150],153⟩) from rfl))
private theorem rec2388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2,5,6],[146],154⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1219]? = some (⟨30,(2),[1,2,5,6],[146],154⟩) from rfl))
private theorem rec2389 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2,5,6],[150],200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1220]? = some (⟨30,(2),[1,2,5,6],[150],200⟩) from rfl))
private theorem rec2411 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2,5,6],[146],155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1242]? = some (⟨30,(3),[1,2,5,6],[146],155⟩) from rfl))
private theorem rec2420 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[5,6],[150],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1251]? = some (⟨30,(3),[5,6],[150],230⟩) from rfl))
private theorem rec2435 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2,5,6],[146],156⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1266]? = some (⟨30,(4),[1,2,5,6],[146],156⟩) from rfl))
private theorem rec2444 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[5,6],[150],231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1]? = some (⟨30,(4),[5,6],[150],231⟩) from rfl))
private theorem rec2459 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2,5,6],[146],155⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[16]? = some (⟨30,(5),[1,2,5,6],[146],155⟩) from rfl))
private theorem rec2468 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[5,6],[150],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[25]? = some (⟨30,(5),[5,6],[150],230⟩) from rfl))
private theorem rec2483 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2,5,6],[146],157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[40]? = some (⟨30,(6),[1,2,5,6],[146],157⟩) from rfl))
private theorem rec2492 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[5,6],[150],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[49]? = some (⟨30,(6),[5,6],[150],232⟩) from rfl))
private theorem rec2507 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2,5,6],[146],157⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[64]? = some (⟨30,(7),[1,2,5,6],[146],157⟩) from rfl))
private theorem rec2516 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[5,6],[150],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[73]? = some (⟨30,(7),[5,6],[150],232⟩) from rfl))
private theorem rec2531 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2,5,6],[146],158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[88]? = some (⟨30,(8),[1,2,5,6],[146],158⟩) from rfl))
private theorem rec2540 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[5,6],[150],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[97]? = some (⟨30,(8),[5,6],[150],233⟩) from rfl))
private theorem rec2555 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2,5,6],[146],158⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[112]? = some (⟨30,(9),[1,2,5,6],[146],158⟩) from rfl))
private theorem rec2564 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[5,6],[150],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[121]? = some (⟨30,(9),[5,6],[150],233⟩) from rfl))
private theorem rec2576 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,5,6],[146,150],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[133]? = some (⟨33,(0),[1,5,6],[146,150],98⟩) from rfl))
private theorem rec2589 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[2,5,6,14],[146,150],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[146]? = some (⟨33,(1),[2,5,6,14],[146,150],159⟩) from rfl))
private theorem rec2598 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[1,5,6,13,14],[146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[155]? = some (⟨33,(2),[1,5,6,13,14],[146,150],3⟩) from rfl))
private theorem rec2612 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[169]? = some (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2624 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,5,6],[146,150],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[181]? = some (⟨33,(4),[1,5,6],[146,150],98⟩) from rfl))
private theorem rec2633 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[190]? = some (⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩) from rfl))
private theorem rec2648 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[205]? = some (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2659 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[216]? = some (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2668 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[225]? = some (⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩) from rfl))
private theorem rec2678 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,5,6,13,14],[146,150],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[235]? = some (⟨33,(9),[1,2,5,6,13,14],[146,150],159⟩) from rfl))
private theorem rec2688 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[1,2,5,6,13,14],[146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[245]? = some (⟨33,(10),[1,2,5,6,13,14],[146,150],3⟩) from rfl))
private theorem rec2698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[255]? = some (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2707 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[264]? = some (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) from rfl))
private theorem rec2719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,2,5,6,13,14],[146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[276]? = some (⟨33,(13),[1,2,5,6,13,14],[146,150],99⟩) from rfl))
private theorem rec2732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[289]? = some (⟨33,(14),[1,2,5,14],[131,146,150],3⟩) from rfl))
private theorem rec2743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[300]? = some (⟨33,(15),[1,2,5,14],[131,146,150],3⟩) from rfl))
private theorem rec2753 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[310]? = some (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2758 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[315]? = some (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2766 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,2,5,6],[150],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[323]? = some (⟨35,(2),[1,2,5,6],[150],139⟩) from rfl))
private theorem rec2772 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[5],[146],185⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[329]? = some (⟨35,(2),[5],[146],185⟩) from rfl))
private theorem rec2781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[338]? = some (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2790 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[347]? = some (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[352]? = some (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2803 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,2,5,6],[150],140⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[360]? = some (⟨35,(6),[1,2,5,6],[150],140⟩) from rfl))
private theorem rec2809 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[5],[146],186⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[366]? = some (⟨35,(6),[5],[146],186⟩) from rfl))
private theorem rec2818 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[375]? = some (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[384]? = some (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2832 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[389]? = some (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2840 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,2,5,6],[150],141⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[397]? = some (⟨35,(10),[1,2,5,6],[150],141⟩) from rfl))
private theorem rec2846 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[5],[146],1396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[403]? = some (⟨35,(10),[5],[146],1396⟩) from rfl))
private theorem rec2855 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[412]? = some (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2864 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[421]? = some (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2869 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[426]? = some (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2877 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,2,5,6],[150],142⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[434]? = some (⟨35,(14),[1,2,5,6],[150],142⟩) from rfl))
private theorem rec2883 (si parent : ℕ) (hs : si ∈ ([5] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[5],[146],188⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[440]? = some (⟨35,(14),[5],[146],188⟩) from rfl))
private theorem rec2892 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[449]? = some (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2900 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[457]? = some (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) from rfl))
private theorem rec2910 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6,13,14],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[467]? = some (⟨36,(7),[1,2,5,6,13,14],[150],3⟩) from rfl))
private theorem rec2911 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[468]? = some (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) from rfl))
private theorem rec2921 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,2,5,6,13,14],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[478]? = some (⟨36,(8),[1,2,5,6,13,14],[150],3⟩) from rfl))
private theorem rec2925 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[482]? = some (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2935 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,2,5,6,13,14],[150],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[492]? = some (⟨36,(9),[1,2,5,6,13,14],[150],143⟩) from rfl))
private theorem rec2941 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[2,5,6,14],[131,146],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[498]? = some (⟨36,(9),[2,5,6,14],[131,146],143⟩) from rfl))
private theorem rec2950 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[507]? = some (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2951 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,5,6,14],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[508]? = some (⟨36,(15),[1,2,5,6,14],[150],3⟩) from rfl))
private theorem rec2958 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,2,5,6,13,14],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[515]? = some (⟨36,(16),[1,2,5,6,13,14],[150],3⟩) from rfl))
private theorem rec2962 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[519]? = some (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2978 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([131, 135, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[5,13],[131,135,146,150],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[535]? = some (⟨36,(17),[5,13],[131,135,146,150],48⟩) from rfl))
private theorem rec2988 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[545]? = some (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0144_0160 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 144).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 144).take 16 = [⟨1,144,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,145,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,146,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,147,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,148,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,149,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,150,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,151,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,152,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,153,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,154,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,155,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,156,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,157,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,158,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,159,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 5 144 (by decide) (by decide)
  · left
    exact rec361 5 145 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 17)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec504 5 146 (by decide) (by decide)
      · right
        exact rec521 5 146 (by decide) (by decide)
      · right
        exact rec538 5 146 (by decide) (by decide)
      · right
        exact rec555 5 146 (by decide) (by decide)
      · right
        exact rec572 5 146 (by decide) (by decide)
      · right
        exact rec589 5 146 (by decide) (by decide)
      · right
        exact rec606 5 146 (by decide) (by decide)
      · right
        exact rec623 5 146 (by decide) (by decide)
      · right
        exact rec640 5 146 (by decide) (by decide)
      · right
        exact rec657 5 146 (by decide) (by decide)
      · right
        exact rec674 5 146 (by decide) (by decide)
      · right
        exact rec691 5 146 (by decide) (by decide)
      · right
        exact rec708 5 146 (by decide) (by decide)
      · right
        exact rec725 5 146 (by decide) (by decide)
      · right
        exact rec742 5 146 (by decide) (by decide)
      · right
        exact rec759 5 146 (by decide) (by decide)
      · right
        exact rec776 5 146 (by decide) (by decide)
      · right
        exact rec793 5 146 (by decide) (by decide)
      · right
        exact rec810 5 146 (by decide) (by decide)
      · right
        exact rec827 5 146 (by decide) (by decide)
      · right
        exact rec844 5 146 (by decide) (by decide)
      · right
        exact rec861 5 146 (by decide) (by decide)
      · right
        exact rec878 5 146 (by decide) (by decide)
      · right
        exact rec895 5 146 (by decide) (by decide)
      · right
        exact rec912 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec919 5 146 (by decide) (by decide)
      · right
        exact rec930 5 146 (by decide) (by decide)
      · right
        exact rec941 5 146 (by decide) (by decide)
      · right
        exact rec952 5 146 (by decide) (by decide)
      · right
        exact rec963 5 146 (by decide) (by decide)
      · right
        exact rec974 5 146 (by decide) (by decide)
      · right
        exact rec985 5 146 (by decide) (by decide)
      · right
        exact rec996 5 146 (by decide) (by decide)
      · right
        exact rec1007 5 146 (by decide) (by decide)
      · right
        exact rec1018 5 146 (by decide) (by decide)
      · right
        exact rec1029 5 146 (by decide) (by decide)
      · right
        exact rec1040 5 146 (by decide) (by decide)
      · right
        exact rec1051 5 146 (by decide) (by decide)
      · right
        exact rec1062 5 146 (by decide) (by decide)
      · right
        exact rec1073 5 146 (by decide) (by decide)
      · right
        exact rec1084 5 146 (by decide) (by decide)
      · right
        exact rec1095 5 146 (by decide) (by decide)
      · right
        exact rec1106 5 146 (by decide) (by decide)
      · right
        exact rec1117 5 146 (by decide) (by decide)
      · right
        exact rec1128 5 146 (by decide) (by decide)
      · right
        exact rec1139 5 146 (by decide) (by decide)
      · right
        exact rec1150 5 146 (by decide) (by decide)
      · right
        exact rec1161 5 146 (by decide) (by decide)
      · right
        exact rec1172 5 146 (by decide) (by decide)
      · right
        exact rec1183 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 21)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1194 5 146 (by decide) (by decide)
      · right
        exact rec1201 5 146 (by decide) (by decide)
      · right
        exact rec1208 5 146 (by decide) (by decide)
      · right
        exact rec1215 5 146 (by decide) (by decide)
      · right
        exact rec1222 5 146 (by decide) (by decide)
      · right
        exact rec1229 5 146 (by decide) (by decide)
      · right
        exact rec1236 5 146 (by decide) (by decide)
      · right
        exact rec1243 5 146 (by decide) (by decide)
      · right
        exact rec1250 5 146 (by decide) (by decide)
      · right
        exact rec1257 5 146 (by decide) (by decide)
      · right
        exact rec1264 5 146 (by decide) (by decide)
      · right
        exact rec1271 5 146 (by decide) (by decide)
      · right
        exact rec1278 5 146 (by decide) (by decide)
      · right
        exact rec1285 5 146 (by decide) (by decide)
      · right
        exact rec1292 5 146 (by decide) (by decide)
      · right
        exact rec1299 5 146 (by decide) (by decide)
      · right
        exact rec1306 5 146 (by decide) (by decide)
      · right
        exact rec1313 5 146 (by decide) (by decide)
      · right
        exact rec1320 5 146 (by decide) (by decide)
      · right
        exact rec1327 5 146 (by decide) (by decide)
      · right
        exact rec1334 5 146 (by decide) (by decide)
      · right
        exact rec1341 5 146 (by decide) (by decide)
      · right
        exact rec1348 5 146 (by decide) (by decide)
      · right
        exact rec1355 5 146 (by decide) (by decide)
      · right
        exact rec1362 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1369 5 146 (by decide) (by decide)
      · right
        exact rec1390 5 146 (by decide) (by decide)
      · right
        exact rec1414 5 146 (by decide) (by decide)
      · right
        exact rec1438 5 146 (by decide) (by decide)
      · right
        exact rec1462 5 146 (by decide) (by decide)
      · right
        exact rec1486 5 146 (by decide) (by decide)
      · right
        exact rec1507 5 146 (by decide) (by decide)
      · right
        exact rec1531 5 146 (by decide) (by decide)
      · right
        exact rec1555 5 146 (by decide) (by decide)
      · right
        exact rec1579 5 146 (by decide) (by decide)
      · right
        exact rec1603 5 146 (by decide) (by decide)
      · right
        exact rec1624 5 146 (by decide) (by decide)
      · right
        exact rec1648 5 146 (by decide) (by decide)
      · right
        exact rec1672 5 146 (by decide) (by decide)
      · right
        exact rec1696 5 146 (by decide) (by decide)
      · right
        exact rec1720 5 146 (by decide) (by decide)
      · right
        exact rec1741 5 146 (by decide) (by decide)
      · right
        exact rec1765 5 146 (by decide) (by decide)
      · right
        exact rec1789 5 146 (by decide) (by decide)
      · right
        exact rec1813 5 146 (by decide) (by decide)
      · right
        exact rec1837 5 146 (by decide) (by decide)
      · right
        exact rec1858 5 146 (by decide) (by decide)
      · right
        exact rec1882 5 146 (by decide) (by decide)
      · right
        exact rec1906 5 146 (by decide) (by decide)
      · right
        exact rec1930 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 26)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1963 5 146 (by decide) (by decide)
      · right
        exact rec1979 5 146 (by decide) (by decide)
      · right
        exact rec1995 5 146 (by decide) (by decide)
      · right
        exact rec2011 5 146 (by decide) (by decide)
      · right
        exact rec2027 5 146 (by decide) (by decide)
      · right
        exact rec2043 5 146 (by decide) (by decide)
      · right
        exact rec2059 5 146 (by decide) (by decide)
      · right
        exact rec2075 5 146 (by decide) (by decide)
      · right
        exact rec2091 5 146 (by decide) (by decide)
      · right
        exact rec2107 5 146 (by decide) (by decide)
      · right
        exact rec2123 5 146 (by decide) (by decide)
      · right
        exact rec2139 5 146 (by decide) (by decide)
      · right
        exact rec2155 5 146 (by decide) (by decide)
      · right
        exact rec2171 5 146 (by decide) (by decide)
      · right
        exact rec2187 5 146 (by decide) (by decide)
      · right
        exact rec2203 5 146 (by decide) (by decide)
      · right
        exact rec2219 5 146 (by decide) (by decide)
      · right
        exact rec2235 5 146 (by decide) (by decide)
      · right
        exact rec2251 5 146 (by decide) (by decide)
      · right
        exact rec2267 5 146 (by decide) (by decide)
      · right
        exact rec2283 5 146 (by decide) (by decide)
      · right
        exact rec2299 5 146 (by decide) (by decide)
      · right
        exact rec2315 5 146 (by decide) (by decide)
      · right
        exact rec2331 5 146 (by decide) (by decide)
      · right
        exact rec2347 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
        exact rec2358 5 146 (by decide) (by decide)
      · right
        exact rec2374 5 146 (by decide) (by decide)
      · right
        exact rec2388 5 146 (by decide) (by decide)
      · right
        exact rec2411 5 146 (by decide) (by decide)
      · right
        exact rec2435 5 146 (by decide) (by decide)
      · right
        exact rec2459 5 146 (by decide) (by decide)
      · right
        exact rec2483 5 146 (by decide) (by decide)
      · right
        exact rec2507 5 146 (by decide) (by decide)
      · right
        exact rec2531 5 146 (by decide) (by decide)
      · right
        exact rec2555 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 31)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 32)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2576 5 146 (by decide) (by decide)
      · right
        exact rec2589 5 146 (by decide) (by decide)
      · right
        exact rec2598 5 146 (by decide) (by decide)
      · right
        exact rec2612 5 146 (by decide) (by decide)
      · right
        exact rec2624 5 146 (by decide) (by decide)
      · right
        exact rec2633 5 146 (by decide) (by decide)
      · right
        exact rec2648 5 146 (by decide) (by decide)
      · right
        exact rec2659 5 146 (by decide) (by decide)
      · right
        exact rec2668 5 146 (by decide) (by decide)
      · right
        exact rec2678 5 146 (by decide) (by decide)
      · right
        exact rec2688 5 146 (by decide) (by decide)
      · right
        exact rec2698 5 146 (by decide) (by decide)
      · right
        exact rec2707 5 146 (by decide) (by decide)
      · right
        exact rec2719 5 146 (by decide) (by decide)
      · right
        exact rec2732 5 146 (by decide) (by decide)
      · right
        exact rec2743 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2753 5 146 (by decide) (by decide)
      · right
        exact rec2758 5 146 (by decide) (by decide)
      · right
        exact rec2772 5 146 (by decide) (by decide)
      · right
        exact rec2781 5 146 (by decide) (by decide)
      · right
        exact rec2790 5 146 (by decide) (by decide)
      · right
        exact rec2795 5 146 (by decide) (by decide)
      · right
        exact rec2809 5 146 (by decide) (by decide)
      · right
        exact rec2818 5 146 (by decide) (by decide)
      · right
        exact rec2827 5 146 (by decide) (by decide)
      · right
        exact rec2832 5 146 (by decide) (by decide)
      · right
        exact rec2846 5 146 (by decide) (by decide)
      · right
        exact rec2855 5 146 (by decide) (by decide)
      · right
        exact rec2864 5 146 (by decide) (by decide)
      · right
        exact rec2869 5 146 (by decide) (by decide)
      · right
        exact rec2883 5 146 (by decide) (by decide)
      · right
        exact rec2892 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2900 5 146 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2911 5 146 (by decide) (by decide)
      · right
        exact rec2925 5 146 (by decide) (by decide)
      · right
        exact rec2941 5 146 (by decide) (by decide)
      · left
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
        exact rec2950 5 146 (by decide) (by decide)
      · right
        exact rec2962 5 146 (by decide) (by decide)
      · right
        exact rec2978 5 146 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2988 5 146 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 37)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
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
    exact rec445 5 147 (by decide) (by decide)
  · left
    exact rec361 5 148 (by decide) (by decide)
  · left
    exact rec361 5 149 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 17)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 18)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec494 5 150 (by decide) (by decide)
      · right
        exact rec511 5 150 (by decide) (by decide)
      · right
        exact rec528 5 150 (by decide) (by decide)
      · right
        exact rec545 5 150 (by decide) (by decide)
      · right
        exact rec562 5 150 (by decide) (by decide)
      · right
        exact rec579 5 150 (by decide) (by decide)
      · right
        exact rec596 5 150 (by decide) (by decide)
      · right
        exact rec613 5 150 (by decide) (by decide)
      · right
        exact rec630 5 150 (by decide) (by decide)
      · right
        exact rec647 5 150 (by decide) (by decide)
      · right
        exact rec664 5 150 (by decide) (by decide)
      · right
        exact rec681 5 150 (by decide) (by decide)
      · right
        exact rec698 5 150 (by decide) (by decide)
      · right
        exact rec715 5 150 (by decide) (by decide)
      · right
        exact rec732 5 150 (by decide) (by decide)
      · right
        exact rec749 5 150 (by decide) (by decide)
      · right
        exact rec766 5 150 (by decide) (by decide)
      · right
        exact rec783 5 150 (by decide) (by decide)
      · right
        exact rec800 5 150 (by decide) (by decide)
      · right
        exact rec817 5 150 (by decide) (by decide)
      · right
        exact rec834 5 150 (by decide) (by decide)
      · right
        exact rec851 5 150 (by decide) (by decide)
      · right
        exact rec868 5 150 (by decide) (by decide)
      · right
        exact rec885 5 150 (by decide) (by decide)
      · right
        exact rec902 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 19)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 20)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec919 5 150 (by decide) (by decide)
      · right
        exact rec930 5 150 (by decide) (by decide)
      · right
        exact rec941 5 150 (by decide) (by decide)
      · right
        exact rec952 5 150 (by decide) (by decide)
      · right
        exact rec963 5 150 (by decide) (by decide)
      · right
        exact rec974 5 150 (by decide) (by decide)
      · right
        exact rec985 5 150 (by decide) (by decide)
      · right
        exact rec996 5 150 (by decide) (by decide)
      · right
        exact rec1007 5 150 (by decide) (by decide)
      · right
        exact rec1018 5 150 (by decide) (by decide)
      · right
        exact rec1029 5 150 (by decide) (by decide)
      · right
        exact rec1040 5 150 (by decide) (by decide)
      · right
        exact rec1051 5 150 (by decide) (by decide)
      · right
        exact rec1062 5 150 (by decide) (by decide)
      · right
        exact rec1073 5 150 (by decide) (by decide)
      · right
        exact rec1084 5 150 (by decide) (by decide)
      · right
        exact rec1095 5 150 (by decide) (by decide)
      · right
        exact rec1106 5 150 (by decide) (by decide)
      · right
        exact rec1117 5 150 (by decide) (by decide)
      · right
        exact rec1128 5 150 (by decide) (by decide)
      · right
        exact rec1139 5 150 (by decide) (by decide)
      · right
        exact rec1150 5 150 (by decide) (by decide)
      · right
        exact rec1161 5 150 (by decide) (by decide)
      · right
        exact rec1172 5 150 (by decide) (by decide)
      · right
        exact rec1183 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 21)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 22)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 23)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1194 5 150 (by decide) (by decide)
      · right
        exact rec1201 5 150 (by decide) (by decide)
      · right
        exact rec1208 5 150 (by decide) (by decide)
      · right
        exact rec1215 5 150 (by decide) (by decide)
      · right
        exact rec1222 5 150 (by decide) (by decide)
      · right
        exact rec1229 5 150 (by decide) (by decide)
      · right
        exact rec1236 5 150 (by decide) (by decide)
      · right
        exact rec1243 5 150 (by decide) (by decide)
      · right
        exact rec1250 5 150 (by decide) (by decide)
      · right
        exact rec1257 5 150 (by decide) (by decide)
      · right
        exact rec1264 5 150 (by decide) (by decide)
      · right
        exact rec1271 5 150 (by decide) (by decide)
      · right
        exact rec1278 5 150 (by decide) (by decide)
      · right
        exact rec1285 5 150 (by decide) (by decide)
      · right
        exact rec1292 5 150 (by decide) (by decide)
      · right
        exact rec1299 5 150 (by decide) (by decide)
      · right
        exact rec1306 5 150 (by decide) (by decide)
      · right
        exact rec1313 5 150 (by decide) (by decide)
      · right
        exact rec1320 5 150 (by decide) (by decide)
      · right
        exact rec1327 5 150 (by decide) (by decide)
      · right
        exact rec1334 5 150 (by decide) (by decide)
      · right
        exact rec1341 5 150 (by decide) (by decide)
      · right
        exact rec1348 5 150 (by decide) (by decide)
      · right
        exact rec1355 5 150 (by decide) (by decide)
      · right
        exact rec1362 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 24)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 25)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1370 5 150 (by decide) (by decide)
      · right
        exact rec1405 5 150 (by decide) (by decide)
      · right
        exact rec1429 5 150 (by decide) (by decide)
      · right
        exact rec1453 5 150 (by decide) (by decide)
      · right
        exact rec1477 5 150 (by decide) (by decide)
      · right
        exact rec1487 5 150 (by decide) (by decide)
      · right
        exact rec1522 5 150 (by decide) (by decide)
      · right
        exact rec1546 5 150 (by decide) (by decide)
      · right
        exact rec1570 5 150 (by decide) (by decide)
      · right
        exact rec1594 5 150 (by decide) (by decide)
      · right
        exact rec1604 5 150 (by decide) (by decide)
      · right
        exact rec1639 5 150 (by decide) (by decide)
      · right
        exact rec1663 5 150 (by decide) (by decide)
      · right
        exact rec1687 5 150 (by decide) (by decide)
      · right
        exact rec1711 5 150 (by decide) (by decide)
      · right
        exact rec1721 5 150 (by decide) (by decide)
      · right
        exact rec1756 5 150 (by decide) (by decide)
      · right
        exact rec1780 5 150 (by decide) (by decide)
      · right
        exact rec1804 5 150 (by decide) (by decide)
      · right
        exact rec1828 5 150 (by decide) (by decide)
      · right
        exact rec1838 5 150 (by decide) (by decide)
      · right
        exact rec1873 5 150 (by decide) (by decide)
      · right
        exact rec1897 5 150 (by decide) (by decide)
      · right
        exact rec1921 5 150 (by decide) (by decide)
      · right
        exact rec1945 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 26)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 27)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 28)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec1958 5 150 (by decide) (by decide)
      · right
        exact rec1974 5 150 (by decide) (by decide)
      · right
        exact rec1990 5 150 (by decide) (by decide)
      · right
        exact rec2006 5 150 (by decide) (by decide)
      · right
        exact rec2022 5 150 (by decide) (by decide)
      · right
        exact rec2038 5 150 (by decide) (by decide)
      · right
        exact rec2054 5 150 (by decide) (by decide)
      · right
        exact rec2070 5 150 (by decide) (by decide)
      · right
        exact rec2086 5 150 (by decide) (by decide)
      · right
        exact rec2102 5 150 (by decide) (by decide)
      · right
        exact rec2118 5 150 (by decide) (by decide)
      · right
        exact rec2134 5 150 (by decide) (by decide)
      · right
        exact rec2150 5 150 (by decide) (by decide)
      · right
        exact rec2166 5 150 (by decide) (by decide)
      · right
        exact rec2182 5 150 (by decide) (by decide)
      · right
        exact rec2198 5 150 (by decide) (by decide)
      · right
        exact rec2214 5 150 (by decide) (by decide)
      · right
        exact rec2230 5 150 (by decide) (by decide)
      · right
        exact rec2246 5 150 (by decide) (by decide)
      · right
        exact rec2262 5 150 (by decide) (by decide)
      · right
        exact rec2278 5 150 (by decide) (by decide)
      · right
        exact rec2294 5 150 (by decide) (by decide)
      · right
        exact rec2310 5 150 (by decide) (by decide)
      · right
        exact rec2326 5 150 (by decide) (by decide)
      · right
        exact rec2342 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 29)).length = 10 := by decide +kernel
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
        exact rec2358 5 150 (by decide) (by decide)
      · right
        exact rec2374 5 150 (by decide) (by decide)
      · right
        exact rec2389 5 150 (by decide) (by decide)
      · right
        exact rec2420 5 150 (by decide) (by decide)
      · right
        exact rec2444 5 150 (by decide) (by decide)
      · right
        exact rec2468 5 150 (by decide) (by decide)
      · right
        exact rec2492 5 150 (by decide) (by decide)
      · right
        exact rec2516 5 150 (by decide) (by decide)
      · right
        exact rec2540 5 150 (by decide) (by decide)
      · right
        exact rec2564 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 31)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 32)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 33)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2576 5 150 (by decide) (by decide)
      · right
        exact rec2589 5 150 (by decide) (by decide)
      · right
        exact rec2598 5 150 (by decide) (by decide)
      · right
        exact rec2612 5 150 (by decide) (by decide)
      · right
        exact rec2624 5 150 (by decide) (by decide)
      · right
        exact rec2633 5 150 (by decide) (by decide)
      · right
        exact rec2648 5 150 (by decide) (by decide)
      · right
        exact rec2659 5 150 (by decide) (by decide)
      · right
        exact rec2668 5 150 (by decide) (by decide)
      · right
        exact rec2678 5 150 (by decide) (by decide)
      · right
        exact rec2688 5 150 (by decide) (by decide)
      · right
        exact rec2698 5 150 (by decide) (by decide)
      · right
        exact rec2707 5 150 (by decide) (by decide)
      · right
        exact rec2719 5 150 (by decide) (by decide)
      · right
        exact rec2732 5 150 (by decide) (by decide)
      · right
        exact rec2743 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 34)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 35)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec2753 5 150 (by decide) (by decide)
      · right
        exact rec2758 5 150 (by decide) (by decide)
      · right
        exact rec2766 5 150 (by decide) (by decide)
      · right
        exact rec2781 5 150 (by decide) (by decide)
      · right
        exact rec2790 5 150 (by decide) (by decide)
      · right
        exact rec2795 5 150 (by decide) (by decide)
      · right
        exact rec2803 5 150 (by decide) (by decide)
      · right
        exact rec2818 5 150 (by decide) (by decide)
      · right
        exact rec2827 5 150 (by decide) (by decide)
      · right
        exact rec2832 5 150 (by decide) (by decide)
      · right
        exact rec2840 5 150 (by decide) (by decide)
      · right
        exact rec2855 5 150 (by decide) (by decide)
      · right
        exact rec2864 5 150 (by decide) (by decide)
      · right
        exact rec2869 5 150 (by decide) (by decide)
      · right
        exact rec2877 5 150 (by decide) (by decide)
      · right
        exact rec2892 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 36)).length = 20 := by decide +kernel
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
        exact rec2900 5 150 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2910 5 150 (by decide) (by decide)
      · right
        exact rec2921 5 150 (by decide) (by decide)
      · right
        exact rec2935 5 150 (by decide) (by decide)
      · left
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
        exact rec2951 5 150 (by decide) (by decide)
      · right
        exact rec2958 5 150 (by decide) (by decide)
      · right
        exact rec2978 5 150 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2988 5 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 37)).length = 5 := by decide +kernel
      have hjj : j < 5 := by simpa only [List.mem_range,hlen] using hj
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
    exact rec441 5 151 (by decide) (by decide)
  · left
    exact rec388 5 152 (by decide) (by decide)
  · left
    exact rec388 5 153 (by decide) (by decide)
  · left
    exact rec362 5 154 (by decide) (by decide)
  · left
    exact rec362 5 155 (by decide) (by decide)
  · left
    exact rec388 5 156 (by decide) (by decide)
  · left
    exact rec388 5 157 (by decide) (by decide)
  · left
    exact rec362 5 158 (by decide) (by decide)
  · left
    exact rec362 5 159 (by decide) (by decide)
end Section14Coverage_5_1_p144_160

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0144_0160


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0160_0176
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p160_176
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec377 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[174],205⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[377]? = some (⟨16,(-1),[1,2,5,6,13,14],[174],205⟩) from rfl))
private theorem rec378 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([171, 187] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[378]? = some (⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩) from rfl))
private theorem rec379 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([175] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[175],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[379]? = some (⟨16,(-1),[1,2,5,6,13,14],[175],207⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec403 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,5,6,14],[170],208⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[403]? = some (⟨16,(-1),[2,5,6,14],[170],208⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0160_0176 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 160).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 160).take 16 = [⟨1,160,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,161,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,162,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,163,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,164,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,165,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,166,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,167,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,168,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,169,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,170,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨1,171,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,172,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,173,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,174,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,175,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 5 160 (by decide) (by decide)
  · left
    exact rec388 5 161 (by decide) (by decide)
  · left
    exact rec362 5 162 (by decide) (by decide)
  · left
    exact rec362 5 163 (by decide) (by decide)
  · left
    exact rec388 5 164 (by decide) (by decide)
  · left
    exact rec388 5 165 (by decide) (by decide)
  · left
    exact rec362 5 166 (by decide) (by decide)
  · left
    exact rec362 5 167 (by decide) (by decide)
  · left
    exact rec361 5 168 (by decide) (by decide)
  · left
    exact rec361 5 169 (by decide) (by decide)
  · left
    exact rec403 5 170 (by decide) (by decide)
  · left
    exact rec378 5 171 (by decide) (by decide)
  · left
    exact rec361 5 172 (by decide) (by decide)
  · left
    exact rec361 5 173 (by decide) (by decide)
  · left
    exact rec377 5 174 (by decide) (by decide)
  · left
    exact rec379 5 175 (by decide) (by decide)
end Section14Coverage_5_1_p160_176

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0160_0176


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0176_0192
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p176_192
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec378 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([171, 187] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[378]? = some (⟨16,(-1),[1,2,5,6,13,14],[171,187],206⟩) from rfl))
private theorem rec380 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[186],208⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[380]? = some (⟨16,(-1),[1,2,5,6,13,14],[186],208⟩) from rfl))
private theorem rec381 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([191] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[191],239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[381]? = some (⟨16,(-1),[1,2,5,6,13,14],[191],239⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec446 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[5,6],[190],1398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[446]? = some (⟨16,(-1),[5,6],[190],1398⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0176_0192 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 176).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 176).take 16 = [⟨1,176,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,177,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,178,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,179,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,180,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,181,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,182,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,183,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,184,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,185,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,186,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,187,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,188,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,189,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,190,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,191,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 5 176 (by decide) (by decide)
  · left
    exact rec388 5 177 (by decide) (by decide)
  · left
    exact rec362 5 178 (by decide) (by decide)
  · left
    exact rec362 5 179 (by decide) (by decide)
  · left
    exact rec388 5 180 (by decide) (by decide)
  · left
    exact rec388 5 181 (by decide) (by decide)
  · left
    exact rec362 5 182 (by decide) (by decide)
  · left
    exact rec362 5 183 (by decide) (by decide)
  · left
    exact rec361 5 184 (by decide) (by decide)
  · left
    exact rec361 5 185 (by decide) (by decide)
  · left
    exact rec380 5 186 (by decide) (by decide)
  · left
    exact rec378 5 187 (by decide) (by decide)
  · left
    exact rec361 5 188 (by decide) (by decide)
  · left
    exact rec361 5 189 (by decide) (by decide)
  · left
    exact rec446 5 190 (by decide) (by decide)
  · left
    exact rec381 5 191 (by decide) (by decide)
end Section14Coverage_5_1_p176_192

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0176_0192


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0192_0208
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p192_208
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec382 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([194, 195] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[194,195],240⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[382]? = some (⟨16,(-1),[1,2,5,6,13,14],[194,195],240⟩) from rfl))
private theorem rec383 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([198, 199] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[198,199],241⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[383]? = some (⟨16,(-1),[1,2,5,6,13,14],[198,199],241⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0192_0208 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 192).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 192).take 16 = [⟨1,192,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,193,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,194,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,195,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,196,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,197,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,198,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,199,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,200,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,201,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,202,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,203,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,204,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,205,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,206,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,207,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 5 192 (by decide) (by decide)
  · left
    exact rec361 5 193 (by decide) (by decide)
  · left
    exact rec382 5 194 (by decide) (by decide)
  · left
    exact rec382 5 195 (by decide) (by decide)
  · left
    exact rec361 5 196 (by decide) (by decide)
  · left
    exact rec361 5 197 (by decide) (by decide)
  · left
    exact rec383 5 198 (by decide) (by decide)
  · left
    exact rec383 5 199 (by decide) (by decide)
  · left
    exact rec388 5 200 (by decide) (by decide)
  · left
    exact rec388 5 201 (by decide) (by decide)
  · left
    exact rec362 5 202 (by decide) (by decide)
  · left
    exact rec362 5 203 (by decide) (by decide)
  · left
    exact rec388 5 204 (by decide) (by decide)
  · left
    exact rec388 5 205 (by decide) (by decide)
  · left
    exact rec362 5 206 (by decide) (by decide)
  · left
    exact rec362 5 207 (by decide) (by decide)
end Section14Coverage_5_1_p192_208

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0192_0208


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0208_0224
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p208_224
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec384 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([210] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[210],242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[384]? = some (⟨16,(-1),[1,2,5,6,13,14],[210],242⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec390 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([211] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,13,14],[211],242⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[390]? = some (⟨16,(-1),[1,2,5,13,14],[211],242⟩) from rfl))
private theorem rec442 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([214, 215] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[5,6],[214,215],241⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[442]? = some (⟨16,(-1),[5,6],[214,215],241⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0208_0224 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 208).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 208).take 16 = [⟨1,208,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,209,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,210,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,211,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,212,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,213,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,214,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,215,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,216,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,217,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,218,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,219,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,220,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,221,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,222,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,223,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 5 208 (by decide) (by decide)
  · left
    exact rec361 5 209 (by decide) (by decide)
  · left
    exact rec384 5 210 (by decide) (by decide)
  · left
    exact rec390 5 211 (by decide) (by decide)
  · left
    exact rec361 5 212 (by decide) (by decide)
  · left
    exact rec361 5 213 (by decide) (by decide)
  · left
    exact rec442 5 214 (by decide) (by decide)
  · left
    exact rec442 5 215 (by decide) (by decide)
  · left
    exact rec388 5 216 (by decide) (by decide)
  · left
    exact rec388 5 217 (by decide) (by decide)
  · left
    exact rec362 5 218 (by decide) (by decide)
  · left
    exact rec362 5 219 (by decide) (by decide)
  · left
    exact rec388 5 220 (by decide) (by decide)
  · left
    exact rec388 5 221 (by decide) (by decide)
  · left
    exact rec362 5 222 (by decide) (by decide)
  · left
    exact rec362 5 223 (by decide) (by decide)
end Section14Coverage_5_1_p208_224

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0208_0224


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0224_0240
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p224_240
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec385 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([234, 250] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[385]? = some (⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩) from rfl))
private theorem rec386 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([238] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[238],244⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[386]? = some (⟨16,(-1),[1,2,5,6,13,14],[238],244⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec391 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([235, 251] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,13,14],[235,251],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[391]? = some (⟨16,(-1),[1,2,5,13,14],[235,251],243⟩) from rfl))
private theorem rec400 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([239] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,5,13],[239],244⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[400]? = some (⟨16,(-1),[1,5,13],[239],244⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0224_0240 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 224).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 224).take 16 = [⟨1,224,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,225,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,226,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,227,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,228,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,229,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,230,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,231,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,232,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,233,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,234,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,235,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,236,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,237,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,238,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,239,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 5 224 (by decide) (by decide)
  · left
    exact rec388 5 225 (by decide) (by decide)
  · left
    exact rec362 5 226 (by decide) (by decide)
  · left
    exact rec362 5 227 (by decide) (by decide)
  · left
    exact rec388 5 228 (by decide) (by decide)
  · left
    exact rec388 5 229 (by decide) (by decide)
  · left
    exact rec362 5 230 (by decide) (by decide)
  · left
    exact rec362 5 231 (by decide) (by decide)
  · left
    exact rec361 5 232 (by decide) (by decide)
  · left
    exact rec361 5 233 (by decide) (by decide)
  · left
    exact rec385 5 234 (by decide) (by decide)
  · left
    exact rec391 5 235 (by decide) (by decide)
  · left
    exact rec361 5 236 (by decide) (by decide)
  · left
    exact rec361 5 237 (by decide) (by decide)
  · left
    exact rec386 5 238 (by decide) (by decide)
  · left
    exact rec400 5 239 (by decide) (by decide)
end Section14Coverage_5_1_p224_240

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0224_0240


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0240_0256
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_1_p240_256
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec385 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([234, 250] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[385]? = some (⟨16,(-1),[1,2,5,6,13,14],[234,250],243⟩) from rfl))
private theorem rec387 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([254] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[254],245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[387]? = some (⟨16,(-1),[1,2,5,6,13,14],[254],245⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec391 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([235, 251] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,13,14],[235,251],243⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[391]? = some (⟨16,(-1),[1,2,5,13,14],[235,251],243⟩) from rfl))
private theorem rec401 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([255] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,5,13],[255],245⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[401]? = some (⟨16,(-1),[1,5,13],[255],245⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0001_parents_0240_0256 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 240).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 240).take 16 = [⟨1,240,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,241,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,242,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,243,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,244,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,245,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,246,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,247,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,248,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,249,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,250,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,251,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,252,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,253,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,254,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,255,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 5 240 (by decide) (by decide)
  · left
    exact rec388 5 241 (by decide) (by decide)
  · left
    exact rec362 5 242 (by decide) (by decide)
  · left
    exact rec362 5 243 (by decide) (by decide)
  · left
    exact rec388 5 244 (by decide) (by decide)
  · left
    exact rec388 5 245 (by decide) (by decide)
  · left
    exact rec362 5 246 (by decide) (by decide)
  · left
    exact rec362 5 247 (by decide) (by decide)
  · left
    exact rec361 5 248 (by decide) (by decide)
  · left
    exact rec361 5 249 (by decide) (by decide)
  · left
    exact rec385 5 250 (by decide) (by decide)
  · left
    exact rec391 5 251 (by decide) (by decide)
  · left
    exact rec361 5 252 (by decide) (by decide)
  · left
    exact rec361 5 253 (by decide) (by decide)
  · left
    exact rec387 5 254 (by decide) (by decide)
  · left
    exact rec401 5 255 (by decide) (by decide)
end Section14Coverage_5_1_p240_256

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0001_parents_0240_0256

open Freiman
set_option synthInstance.maxSize 100000
set_option maxRecDepth 100000
namespace M7Section14Sep18
instance (r : CertRectangle) : Decidable (certRectangleValid r) := by
  unfold certRectangleValid
  infer_instance
instance (t : CertThreshold) : Decidable (certThresholdDataValid t) := by
  unfold certThresholdDataValid
  infer_instance
instance (z : CertField) (q : ℚ) : Decidable (certCoefficientBoundValid z q) := by
  unfold certCoefficientBoundValid
  infer_instance
instance (w : CertWitness) : Decidable (certWitnessValid w) := by
  unfold certWitnessValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (caseId : ℕ)
    (gs : ℕ × Section14Spec) : Decidable (section14SpecValid C S caseId gs) := by
  unfold section14SpecValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (p : Section14Plan) :
    Decidable (section14PlanValid C S p) := by
  unfold section14PlanValid
  infer_instance
instance (outer inner : CertRectangle) : Decidable (section14RectangleContains outer inner) := by
  unfold section14RectangleContains
  infer_instance
instance (C : Section14Catalog) (si : ℕ) (r : Section14Record) :
    Decidable (section14RecordValid C si r) := by
  unfold section14RecordValid
  infer_instance
instance (C : Section14Catalog) (si parent goal : ℕ) (branch : ℤ) :
    Decidable (section14Recorded C si parent goal branch) := by
  unfold section14Recorded
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14Coverage C si) := by
  unfold section14Coverage
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14StateValid C si) := by
  unfold section14StateValid
  infer_instance
end M7Section14Sep18

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 1).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 5), section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  intro pl hpl
  let xs := section14Parents section14Catalog (section14State section14Catalog 5)
  let P := fun b : Section14Parent => section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j
  have h256 : ∀ x ∈ xs.drop 256, P x := by
    apply all_empty P _
    rfl
  have h240 : ∀ x ∈ xs.drop 240, P x := by
    apply all_of_chunks P xs 240 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0240_0256 pl hpl)
    exact h256
  have h224 : ∀ x ∈ xs.drop 224, P x := by
    apply all_of_chunks P xs 224 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0224_0240 pl hpl)
    exact h240
  have h208 : ∀ x ∈ xs.drop 208, P x := by
    apply all_of_chunks P xs 208 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0208_0224 pl hpl)
    exact h224
  have h192 : ∀ x ∈ xs.drop 192, P x := by
    apply all_of_chunks P xs 192 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0192_0208 pl hpl)
    exact h208
  have h176 : ∀ x ∈ xs.drop 176, P x := by
    apply all_of_chunks P xs 176 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0176_0192 pl hpl)
    exact h192
  have h160 : ∀ x ∈ xs.drop 160, P x := by
    apply all_of_chunks P xs 160 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0160_0176 pl hpl)
    exact h176
  have h144 : ∀ x ∈ xs.drop 144, P x := by
    apply all_of_chunks P xs 144 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0144_0160 pl hpl)
    exact h160
  have h128 : ∀ x ∈ xs.drop 128, P x := by
    apply all_of_chunks P xs 128 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0128_0144 pl hpl)
    exact h144
  have h112 : ∀ x ∈ xs.drop 112, P x := by
    apply all_of_chunks P xs 112 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0112_0128 pl hpl)
    exact h128
  have h96 : ∀ x ∈ xs.drop 96, P x := by
    apply all_of_chunks P xs 96 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0096_0112 pl hpl)
    exact h112
  have h80 : ∀ x ∈ xs.drop 80, P x := by
    apply all_of_chunks P xs 80 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0080_0096 pl hpl)
    exact h96
  have h64 : ∀ x ∈ xs.drop 64, P x := by
    apply all_of_chunks P xs 64 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0064_0080 pl hpl)
    exact h80
  have h48 : ∀ x ∈ xs.drop 48, P x := by
    apply all_of_chunks P xs 48 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0048_0064 pl hpl)
    exact h64
  have h32 : ∀ x ∈ xs.drop 32, P x := by
    apply all_of_chunks P xs 32 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0032_0048 pl hpl)
    exact h48
  have h16 : ∀ x ∈ xs.drop 16, P x := by
    apply all_of_chunks P xs 16 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0016_0032 pl hpl)
    exact h32
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 16 (Freiman.workReverse20260919_s0005_coverage0001_parents_0000_0016 pl hpl)
    exact h16
  simpa only [List.drop_zero] using h0

#print axioms solution
