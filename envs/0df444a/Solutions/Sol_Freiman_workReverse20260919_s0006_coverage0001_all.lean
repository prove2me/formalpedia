-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_coverage0001_all
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:15:55.477898+00:00
-- url     : https://prove2.me/submissions/595b5019-729e-4789-9540-06222f01d273

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0000_0016
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p0_16
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
private theorem rec404 (si parent : ℕ) (hs : si ∈ ([2, 6, 10, 14] : List ℕ)) (hp : parent ∈ ([0] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,10,14],[0],912⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[404]? = some (⟨16,(-1),[2,6,10,14],[0],912⟩) from rfl))
private theorem rec449 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([4, 20] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[6],[4,20],1394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[449]? = some (⟨16,(-1),[6],[4,20],1394⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0000_0016 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 0).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 0).take 16 = [⟨1,0,[⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,1,[⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,2,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,3,[⟨true,true,1⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,4,[⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,5,[⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,6,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,7,[⟨true,true,1⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,8,[⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,9,[⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,10,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,11,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,12,[⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,13,[⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,14,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,15,[⟨true,true,1⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec404 6 0 (by decide) (by decide)
  · left
    exact rec360 6 1 (by decide) (by decide)
  · left
    exact rec359 6 2 (by decide) (by decide)
  · left
    exact rec359 6 3 (by decide) (by decide)
  · left
    exact rec449 6 4 (by decide) (by decide)
  · left
    exact rec363 6 5 (by decide) (by decide)
  · left
    exact rec359 6 6 (by decide) (by decide)
  · left
    exact rec359 6 7 (by decide) (by decide)
  · left
    exact rec362 6 8 (by decide) (by decide)
  · left
    exact rec362 6 9 (by decide) (by decide)
  · left
    exact rec388 6 10 (by decide) (by decide)
  · left
    exact rec388 6 11 (by decide) (by decide)
  · left
    exact rec362 6 12 (by decide) (by decide)
  · left
    exact rec362 6 13 (by decide) (by decide)
  · left
    exact rec388 6 14 (by decide) (by decide)
  · left
    exact rec388 6 15 (by decide) (by decide)
end Section14Coverage_6_1_p0_16

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0000_0016


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0016_0032
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p16_32
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
private theorem rec410 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([16] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[16],913⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[410]? = some (⟨16,(-1),[2,6,14],[16],913⟩) from rfl))
private theorem rec411 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([17] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[17],914⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[411]? = some (⟨16,(-1),[2,6,14],[17],914⟩) from rfl))
private theorem rec449 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([4, 20] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[6],[4,20],1394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[449]? = some (⟨16,(-1),[6],[4,20],1394⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0016_0032 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 16).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 16).take 16 = [⟨1,16,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,17,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,18,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,19,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,20,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,21,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,22,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,23,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,24,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,25,[⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,26,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,27,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,28,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,29,[⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,30,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,31,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec410 6 16 (by decide) (by decide)
  · left
    exact rec411 6 17 (by decide) (by decide)
  · left
    exact rec359 6 18 (by decide) (by decide)
  · left
    exact rec359 6 19 (by decide) (by decide)
  · left
    exact rec449 6 20 (by decide) (by decide)
  · left
    exact rec363 6 21 (by decide) (by decide)
  · left
    exact rec359 6 22 (by decide) (by decide)
  · left
    exact rec359 6 23 (by decide) (by decide)
  · left
    exact rec362 6 24 (by decide) (by decide)
  · left
    exact rec362 6 25 (by decide) (by decide)
  · left
    exact rec388 6 26 (by decide) (by decide)
  · left
    exact rec388 6 27 (by decide) (by decide)
  · left
    exact rec362 6 28 (by decide) (by decide)
  · left
    exact rec362 6 29 (by decide) (by decide)
  · left
    exact rec388 6 30 (by decide) (by decide)
  · left
    exact rec388 6 31 (by decide) (by decide)
end Section14Coverage_6_1_p16_32

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0016_0032


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0032_0048
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p32_48
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
private theorem rec405 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([40, 56] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[40,56],67⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[405]? = some (⟨16,(-1),[2,6,14],[40,56],67⟩) from rfl))
private theorem rec406 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([44] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[44],69⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[406]? = some (⟨16,(-1),[2,6,14],[44],69⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0032_0048 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 32).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 32).take 16 = [⟨1,32,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,33,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,34,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,35,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,36,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,37,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,38,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,39,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,40,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,41,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,42,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,43,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,44,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,45,[⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,46,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,47,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec362 6 32 (by decide) (by decide)
  · left
    exact rec362 6 33 (by decide) (by decide)
  · left
    exact rec388 6 34 (by decide) (by decide)
  · left
    exact rec388 6 35 (by decide) (by decide)
  · left
    exact rec362 6 36 (by decide) (by decide)
  · left
    exact rec362 6 37 (by decide) (by decide)
  · left
    exact rec388 6 38 (by decide) (by decide)
  · left
    exact rec388 6 39 (by decide) (by decide)
  · left
    exact rec405 6 40 (by decide) (by decide)
  · left
    exact rec364 6 41 (by decide) (by decide)
  · left
    exact rec361 6 42 (by decide) (by decide)
  · left
    exact rec361 6 43 (by decide) (by decide)
  · left
    exact rec406 6 44 (by decide) (by decide)
  · left
    exact rec365 6 45 (by decide) (by decide)
  · left
    exact rec361 6 46 (by decide) (by decide)
  · left
    exact rec361 6 47 (by decide) (by decide)
end Section14Coverage_6_1_p32_48

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0032_0048


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0048_0064
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p48_64
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
private theorem rec405 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([40, 56] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[40,56],67⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[405]? = some (⟨16,(-1),[2,6,14],[40,56],67⟩) from rfl))
private theorem rec407 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([60] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[60],71⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[407]? = some (⟨16,(-1),[2,6,14],[60],71⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0048_0064 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 48).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 48).take 16 = [⟨1,48,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,49,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,50,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,51,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩,⟨false,true,8⟩]⟩,⟨1,52,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,53,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,54,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,55,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,8⟩]⟩,⟨1,56,[⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,57,[⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,58,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,59,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,60,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩,⟨false,true,8⟩]⟩,⟨1,61,[⟨true,false,14⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,62,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩,⟨1,63,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,8⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec362 6 48 (by decide) (by decide)
  · left
    exact rec362 6 49 (by decide) (by decide)
  · left
    exact rec388 6 50 (by decide) (by decide)
  · left
    exact rec388 6 51 (by decide) (by decide)
  · left
    exact rec362 6 52 (by decide) (by decide)
  · left
    exact rec362 6 53 (by decide) (by decide)
  · left
    exact rec388 6 54 (by decide) (by decide)
  · left
    exact rec388 6 55 (by decide) (by decide)
  · left
    exact rec405 6 56 (by decide) (by decide)
  · left
    exact rec364 6 57 (by decide) (by decide)
  · left
    exact rec361 6 58 (by decide) (by decide)
  · left
    exact rec361 6 59 (by decide) (by decide)
  · left
    exact rec407 6 60 (by decide) (by decide)
  · left
    exact rec366 6 61 (by decide) (by decide)
  · left
    exact rec361 6 62 (by decide) (by decide)
  · left
    exact rec361 6 63 (by decide) (by decide)
end Section14Coverage_6_1_p48_64

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0048_0064


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0064_0080
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p64_80
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
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0064_0080 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 64).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 64).take 16 = [⟨1,64,[⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,65,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,66,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,67,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,68,[⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,69,[⟨true,false,15⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,70,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,71,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,72,[⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,73,[⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,74,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,75,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,76,[⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,77,[⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,78,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,79,[⟨true,true,1⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec367 6 64 (by decide) (by decide)
  · left
    exact rec368 6 65 (by decide) (by decide)
  · left
    exact rec361 6 66 (by decide) (by decide)
  · left
    exact rec361 6 67 (by decide) (by decide)
  · left
    exact rec443 6 68 (by decide) (by decide)
  · left
    exact rec444 6 69 (by decide) (by decide)
  · left
    exact rec361 6 70 (by decide) (by decide)
  · left
    exact rec361 6 71 (by decide) (by decide)
  · left
    exact rec362 6 72 (by decide) (by decide)
  · left
    exact rec362 6 73 (by decide) (by decide)
  · left
    exact rec388 6 74 (by decide) (by decide)
  · left
    exact rec388 6 75 (by decide) (by decide)
  · left
    exact rec362 6 76 (by decide) (by decide)
  · left
    exact rec362 6 77 (by decide) (by decide)
  · left
    exact rec388 6 78 (by decide) (by decide)
  · left
    exact rec388 6 79 (by decide) (by decide)
end Section14Coverage_6_1_p64_80

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0064_0080


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0080_0096
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p80_96
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
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0080_0096 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 80).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 80).take 16 = [⟨1,80,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,81,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,82,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,83,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,84,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,85,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,86,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,87,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,88,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,89,[⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,90,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,91,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,92,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,93,[⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,94,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,95,[⟨true,true,1⟩,⟨true,false,16⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec369 6 80 (by decide) (by decide)
  · left
    exact rec370 6 81 (by decide) (by decide)
  · left
    exact rec361 6 82 (by decide) (by decide)
  · left
    exact rec361 6 83 (by decide) (by decide)
  · left
    exact rec369 6 84 (by decide) (by decide)
  · left
    exact rec370 6 85 (by decide) (by decide)
  · left
    exact rec361 6 86 (by decide) (by decide)
  · left
    exact rec361 6 87 (by decide) (by decide)
  · left
    exact rec362 6 88 (by decide) (by decide)
  · left
    exact rec362 6 89 (by decide) (by decide)
  · left
    exact rec388 6 90 (by decide) (by decide)
  · left
    exact rec388 6 91 (by decide) (by decide)
  · left
    exact rec362 6 92 (by decide) (by decide)
  · left
    exact rec362 6 93 (by decide) (by decide)
  · left
    exact rec388 6 94 (by decide) (by decide)
  · left
    exact rec388 6 95 (by decide) (by decide)
end Section14Coverage_6_1_p80_96

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0080_0096


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0096_0112
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p96_112
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
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0096_0112 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 96).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 96).take 16 = [⟨1,96,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,97,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,98,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,99,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,100,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,101,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,102,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,103,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,104,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,105,[⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,106,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,107,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,108,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,109,[⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,110,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,111,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,15⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec362 6 96 (by decide) (by decide)
  · left
    exact rec362 6 97 (by decide) (by decide)
  · left
    exact rec388 6 98 (by decide) (by decide)
  · left
    exact rec388 6 99 (by decide) (by decide)
  · left
    exact rec362 6 100 (by decide) (by decide)
  · left
    exact rec362 6 101 (by decide) (by decide)
  · left
    exact rec388 6 102 (by decide) (by decide)
  · left
    exact rec388 6 103 (by decide) (by decide)
  · left
    exact rec371 6 104 (by decide) (by decide)
  · left
    exact rec372 6 105 (by decide) (by decide)
  · left
    exact rec361 6 106 (by decide) (by decide)
  · left
    exact rec361 6 107 (by decide) (by decide)
  · left
    exact rec373 6 108 (by decide) (by decide)
  · left
    exact rec374 6 109 (by decide) (by decide)
  · left
    exact rec361 6 110 (by decide) (by decide)
  · left
    exact rec361 6 111 (by decide) (by decide)
end Section14Coverage_6_1_p96_112

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0096_0112


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0112_0128
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p112_128
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
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0112_0128 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 112).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 112).take 16 = [⟨1,112,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,113,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,114,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,115,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,116,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,117,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,118,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,119,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,120,[⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,121,[⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,122,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,123,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,124,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,125,[⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,126,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,127,[⟨true,true,1⟩,⟨true,false,17⟩,⟨true,true,4⟩,⟨true,false,8⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec362 6 112 (by decide) (by decide)
  · left
    exact rec362 6 113 (by decide) (by decide)
  · left
    exact rec388 6 114 (by decide) (by decide)
  · left
    exact rec388 6 115 (by decide) (by decide)
  · left
    exact rec362 6 116 (by decide) (by decide)
  · left
    exact rec362 6 117 (by decide) (by decide)
  · left
    exact rec388 6 118 (by decide) (by decide)
  · left
    exact rec388 6 119 (by decide) (by decide)
  · left
    exact rec371 6 120 (by decide) (by decide)
  · left
    exact rec372 6 121 (by decide) (by decide)
  · left
    exact rec361 6 122 (by decide) (by decide)
  · left
    exact rec361 6 123 (by decide) (by decide)
  · left
    exact rec375 6 124 (by decide) (by decide)
  · left
    exact rec376 6 125 (by decide) (by decide)
  · left
    exact rec361 6 126 (by decide) (by decide)
  · left
    exact rec361 6 127 (by decide) (by decide)
end Section14Coverage_6_1_p112_128

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0112_0128


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0128_0144
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p128_144
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec412 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([134] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[134],916⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[412]? = some (⟨16,(-1),[2,6,14],[134],916⟩) from rfl))
private theorem rec448 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([135] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[6],[135],917⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[448]? = some (⟨16,(-1),[6],[135],917⟩) from rfl))
private theorem rec493 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[493]? = some (⟨18,(0),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec502 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[2,6],[130],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[502]? = some (⟨18,(0),[2,6],[130],106⟩) from rfl))
private theorem rec510 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[510]? = some (⟨18,(1),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec519 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[2,6],[130],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[519]? = some (⟨18,(1),[2,6],[130],106⟩) from rfl))
private theorem rec527 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[527]? = some (⟨18,(2),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec536 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[2,6],[130],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[536]? = some (⟨18,(2),[2,6],[130],106⟩) from rfl))
private theorem rec544 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[544]? = some (⟨18,(3),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec553 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[2,6],[130],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[553]? = some (⟨18,(3),[2,6],[130],106⟩) from rfl))
private theorem rec561 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,2,5,6,13,14],[131],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[561]? = some (⟨18,(4),[1,2,5,6,13,14],[131],106⟩) from rfl))
private theorem rec570 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[2,6],[130],106⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[570]? = some (⟨18,(4),[2,6],[130],106⟩) from rfl))
private theorem rec578 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[578]? = some (⟨18,(5),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec587 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[2,6],[130],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[587]? = some (⟨18,(5),[2,6],[130],107⟩) from rfl))
private theorem rec595 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[595]? = some (⟨18,(6),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec604 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[2,6],[130],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[604]? = some (⟨18,(6),[2,6],[130],107⟩) from rfl))
private theorem rec612 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[612]? = some (⟨18,(7),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec621 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[2,6],[130],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[621]? = some (⟨18,(7),[2,6],[130],107⟩) from rfl))
private theorem rec629 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[629]? = some (⟨18,(8),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec638 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[2,6],[130],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[638]? = some (⟨18,(8),[2,6],[130],107⟩) from rfl))
private theorem rec646 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[646]? = some (⟨18,(9),[1,2,5,6,13,14],[131],107⟩) from rfl))
private theorem rec655 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[2,6],[130],107⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[655]? = some (⟨18,(9),[2,6],[130],107⟩) from rfl))
private theorem rec663 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[663]? = some (⟨18,(10),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec672 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[2,6],[130],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[672]? = some (⟨18,(10),[2,6],[130],108⟩) from rfl))
private theorem rec680 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[680]? = some (⟨18,(11),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec689 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[2,6],[130],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[689]? = some (⟨18,(11),[2,6],[130],109⟩) from rfl))
private theorem rec697 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,2,5,6,13,14],[131],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[697]? = some (⟨18,(12),[1,2,5,6,13,14],[131],110⟩) from rfl))
private theorem rec706 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[2,6],[130],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[706]? = some (⟨18,(12),[2,6],[130],110⟩) from rfl))
private theorem rec714 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[714]? = some (⟨18,(13),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec723 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[2,6],[130],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[723]? = some (⟨18,(13),[2,6],[130],109⟩) from rfl))
private theorem rec731 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,2,5,6,13,14],[131],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[731]? = some (⟨18,(14),[1,2,5,6,13,14],[131],111⟩) from rfl))
private theorem rec740 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[2,6],[130],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[740]? = some (⟨18,(14),[2,6],[130],111⟩) from rfl))
private theorem rec748 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[748]? = some (⟨18,(15),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec757 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[2,6],[130],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[757]? = some (⟨18,(15),[2,6],[130],108⟩) from rfl))
private theorem rec765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[765]? = some (⟨18,(16),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec774 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[2,6],[130],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[774]? = some (⟨18,(16),[2,6],[130],112⟩) from rfl))
private theorem rec782 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[782]? = some (⟨18,(17),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec791 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[2,6],[130],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[791]? = some (⟨18,(17),[2,6],[130],112⟩) from rfl))
private theorem rec799 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[799]? = some (⟨18,(18),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec808 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[2,6],[130],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[808]? = some (⟨18,(18),[2,6],[130],112⟩) from rfl))
private theorem rec816 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,2,5,6,13,14],[131],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[816]? = some (⟨18,(19),[1,2,5,6,13,14],[131],112⟩) from rfl))
private theorem rec825 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[2,6],[130],112⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[825]? = some (⟨18,(19),[2,6],[130],112⟩) from rfl))
private theorem rec833 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,2,5,6,13,14],[131],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[833]? = some (⟨18,(20),[1,2,5,6,13,14],[131],108⟩) from rfl))
private theorem rec842 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[2,6],[130],108⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[842]? = some (⟨18,(20),[2,6],[130],108⟩) from rfl))
private theorem rec850 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[850]? = some (⟨18,(21),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec859 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[2,6],[130],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[859]? = some (⟨18,(21),[2,6],[130],109⟩) from rfl))
private theorem rec867 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[867]? = some (⟨18,(22),[1,2,5,6,13,14],[131],110⟩) from rfl))
private theorem rec876 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[2,6],[130],110⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[876]? = some (⟨18,(22),[2,6],[130],110⟩) from rfl))
private theorem rec884 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[884]? = some (⟨18,(23),[1,2,5,6,13,14],[131],109⟩) from rfl))
private theorem rec893 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[2,6],[130],109⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[893]? = some (⟨18,(23),[2,6],[130],109⟩) from rfl))
private theorem rec901 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,2,5,6,13,14],[131],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[901]? = some (⟨18,(24),[1,2,5,6,13,14],[131],111⟩) from rfl))
private theorem rec910 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[2,6],[130],111⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[910]? = some (⟨18,(24),[2,6],[130],111⟩) from rfl))
private theorem rec918 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[918]? = some (⟨20,(0),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[919]? = some (⟨20,(0),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec929 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[929]? = some (⟨20,(1),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[930]? = some (⟨20,(1),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec940 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[940]? = some (⟨20,(2),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec941 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[941]? = some (⟨20,(2),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec951 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[951]? = some (⟨20,(3),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec952 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[952]? = some (⟨20,(3),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec962 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[962]? = some (⟨20,(4),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec963 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[963]? = some (⟨20,(4),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec973 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[973]? = some (⟨20,(5),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[974]? = some (⟨20,(5),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec984 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[984]? = some (⟨20,(6),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec985 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[985]? = some (⟨20,(6),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[995]? = some (⟨20,(7),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec996 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[996]? = some (⟨20,(7),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1006 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1006]? = some (⟨20,(8),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1007 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1007]? = some (⟨20,(8),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1017 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1017]? = some (⟨20,(9),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1018 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1018]? = some (⟨20,(9),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1028 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1028]? = some (⟨20,(10),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1029 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1029]? = some (⟨20,(10),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1039 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1039]? = some (⟨20,(11),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1040 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1040]? = some (⟨20,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1050 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1050]? = some (⟨20,(12),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1051]? = some (⟨20,(12),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1061 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1061]? = some (⟨20,(13),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1062 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1062]? = some (⟨20,(13),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1072 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1072]? = some (⟨20,(14),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1073 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1073]? = some (⟨20,(14),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1083 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1083]? = some (⟨20,(15),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1084 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1084]? = some (⟨20,(15),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1094 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1094]? = some (⟨20,(16),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1095 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1095]? = some (⟨20,(16),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1105 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1105]? = some (⟨20,(17),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1106 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1106]? = some (⟨20,(17),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1116 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1116]? = some (⟨20,(18),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1117]? = some (⟨20,(18),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1127 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1127]? = some (⟨20,(19),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1128 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1128]? = some (⟨20,(19),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1138]? = some (⟨20,(20),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1139 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1139]? = some (⟨20,(20),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1149 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1149]? = some (⟨20,(21),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1150]? = some (⟨20,(21),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1160 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1160]? = some (⟨20,(22),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1161 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1161]? = some (⟨20,(22),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1171 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[2]? = some (⟨20,(23),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1172 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[3]? = some (⟨20,(23),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1182 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[13]? = some (⟨20,(24),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec1183 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[14]? = some (⟨20,(24),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec1193 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[24]? = some (⟨23,(0),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1194 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[25]? = some (⟨23,(0),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1200 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[31]? = some (⟨23,(1),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1201 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[32]? = some (⟨23,(1),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1207 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[38]? = some (⟨23,(2),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1208 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[39]? = some (⟨23,(2),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1214 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[45]? = some (⟨23,(3),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1215 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[46]? = some (⟨23,(3),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1221 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[52]? = some (⟨23,(4),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1222 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[53]? = some (⟨23,(4),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1228 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[59]? = some (⟨23,(5),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[60]? = some (⟨23,(5),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1235 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[66]? = some (⟨23,(6),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1236 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[67]? = some (⟨23,(6),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1242 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[73]? = some (⟨23,(7),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1243 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[74]? = some (⟨23,(7),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1249 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[80]? = some (⟨23,(8),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1250 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[81]? = some (⟨23,(8),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1256 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[87]? = some (⟨23,(9),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1257 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[88]? = some (⟨23,(9),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1263 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[94]? = some (⟨23,(10),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[95]? = some (⟨23,(10),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1270 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[101]? = some (⟨23,(11),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[102]? = some (⟨23,(11),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1277 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[108]? = some (⟨23,(12),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[109]? = some (⟨23,(12),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1284 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[115]? = some (⟨23,(13),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[116]? = some (⟨23,(13),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1291 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[122]? = some (⟨23,(14),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[123]? = some (⟨23,(14),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1298 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[129]? = some (⟨23,(15),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1299 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[130]? = some (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1305 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[136]? = some (⟨23,(16),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1306 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[137]? = some (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1312 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[143]? = some (⟨23,(17),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[144]? = some (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1319 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[150]? = some (⟨23,(18),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[151]? = some (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[157]? = some (⟨23,(19),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1327 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[158]? = some (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1333 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[164]? = some (⟨23,(20),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[165]? = some (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1340 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[171]? = some (⟨23,(21),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[172]? = some (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1347 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[178]? = some (⟨23,(22),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1348 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[179]? = some (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1354 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[185]? = some (⟨23,(23),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[186]? = some (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[192]? = some (⟨23,(24),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec1362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[193]? = some (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) from rfl))
private theorem rec1368 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[199]? = some (⟨25,(0),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1383 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[5,6],[131],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[214]? = some (⟨25,(0),[5,6],[131],167⟩) from rfl))
private theorem rec1389 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,5,6],[130],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[220]? = some (⟨25,(1),[1,2,5,6],[130],81⟩) from rfl))
private theorem rec1404 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[5,6],[131],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[235]? = some (⟨25,(1),[5,6],[131],168⟩) from rfl))
private theorem rec1413 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[244]? = some (⟨25,(2),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1428 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[5,6],[131],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[259]? = some (⟨25,(2),[5,6],[131],167⟩) from rfl))
private theorem rec1437 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,5,6],[130],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[268]? = some (⟨25,(3),[1,2,5,6],[130],82⟩) from rfl))
private theorem rec1452 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[5,6],[131],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[283]? = some (⟨25,(3),[5,6],[131],169⟩) from rfl))
private theorem rec1461 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[292]? = some (⟨25,(4),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1476 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[5,6],[131],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[307]? = some (⟨25,(4),[5,6],[131],170⟩) from rfl))
private theorem rec1485 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[316]? = some (⟨25,(5),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1500 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[5,6],[131],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[331]? = some (⟨25,(5),[5,6],[131],167⟩) from rfl))
private theorem rec1506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,5,6],[130],81⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[337]? = some (⟨25,(6),[1,2,5,6],[130],81⟩) from rfl))
private theorem rec1521 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[5,6],[131],168⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[352]? = some (⟨25,(6),[5,6],[131],168⟩) from rfl))
private theorem rec1530 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,5,6],[130],80⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[361]? = some (⟨25,(7),[1,2,5,6],[130],80⟩) from rfl))
private theorem rec1545 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[5,6],[131],167⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[376]? = some (⟨25,(7),[5,6],[131],167⟩) from rfl))
private theorem rec1554 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,5,6],[130],82⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[385]? = some (⟨25,(8),[1,2,5,6],[130],82⟩) from rfl))
private theorem rec1569 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[5,6],[131],169⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[400]? = some (⟨25,(8),[5,6],[131],169⟩) from rfl))
private theorem rec1578 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[409]? = some (⟨25,(9),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1593 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[5,6],[131],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[424]? = some (⟨25,(9),[5,6],[131],170⟩) from rfl))
private theorem rec1602 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[433]? = some (⟨25,(10),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1617 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[5,6],[131],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[448]? = some (⟨25,(10),[5,6],[131],171⟩) from rfl))
private theorem rec1623 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[454]? = some (⟨25,(11),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1638 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[5,6],[131],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[469]? = some (⟨25,(11),[5,6],[131],171⟩) from rfl))
private theorem rec1647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[478]? = some (⟨25,(12),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1662 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[5,6],[131],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[493]? = some (⟨25,(12),[5,6],[131],171⟩) from rfl))
private theorem rec1671 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,5,6],[130],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[502]? = some (⟨25,(13),[1,2,5,6],[130],84⟩) from rfl))
private theorem rec1686 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[5,6],[131],171⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[517]? = some (⟨25,(13),[5,6],[131],171⟩) from rfl))
private theorem rec1695 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,5,6],[130],83⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[526]? = some (⟨25,(14),[1,2,5,6],[130],83⟩) from rfl))
private theorem rec1710 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[5,6],[131],170⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[541]? = some (⟨25,(14),[5,6],[131],170⟩) from rfl))
private theorem rec1719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[550]? = some (⟨25,(15),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1734 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[565]? = some (⟨25,(15),[5,6],[131],172⟩) from rfl))
private theorem rec1740 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[571]? = some (⟨25,(16),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1755 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[586]? = some (⟨25,(16),[5,6],[131],172⟩) from rfl))
private theorem rec1764 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[595]? = some (⟨25,(17),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1779 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[610]? = some (⟨25,(17),[5,6],[131],172⟩) from rfl))
private theorem rec1788 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[619]? = some (⟨25,(18),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1803 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[634]? = some (⟨25,(18),[5,6],[131],172⟩) from rfl))
private theorem rec1812 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,5,6],[130],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[643]? = some (⟨25,(19),[1,2,5,6],[130],35⟩) from rfl))
private theorem rec1827 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[5,6],[131],172⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[658]? = some (⟨25,(19),[5,6],[131],172⟩) from rfl))
private theorem rec1836 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[667]? = some (⟨25,(20),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1851 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[682]? = some (⟨25,(20),[5,6],[131],173⟩) from rfl))
private theorem rec1857 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[688]? = some (⟨25,(21),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1872 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[703]? = some (⟨25,(21),[5,6],[131],173⟩) from rfl))
private theorem rec1881 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[712]? = some (⟨25,(22),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1896 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[727]? = some (⟨25,(22),[5,6],[131],173⟩) from rfl))
private theorem rec1905 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[736]? = some (⟨25,(23),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1920 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[751]? = some (⟨25,(23),[5,6],[131],173⟩) from rfl))
private theorem rec1929 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,5,6],[130],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[760]? = some (⟨25,(24),[1,2,5,6],[130],38⟩) from rfl))
private theorem rec1944 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[5,6],[131],173⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[775]? = some (⟨25,(24),[5,6],[131],173⟩) from rfl))
private theorem rec1957 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[788]? = some (⟨28,(0),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1962 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[2,6],[130],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[793]? = some (⟨28,(0),[2,6],[130],113⟩) from rfl))
private theorem rec1973 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[804]? = some (⟨28,(1),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1978 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[2,6],[130],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[809]? = some (⟨28,(1),[2,6],[130],113⟩) from rfl))
private theorem rec1989 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[820]? = some (⟨28,(2),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec1994 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[2,6],[130],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[825]? = some (⟨28,(2),[2,6],[130],113⟩) from rfl))
private theorem rec2005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[836]? = some (⟨28,(3),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec2010 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[2,6],[130],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[841]? = some (⟨28,(3),[2,6],[130],113⟩) from rfl))
private theorem rec2021 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,2,5,6],[131],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[852]? = some (⟨28,(4),[1,2,5,6],[131],113⟩) from rfl))
private theorem rec2026 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[2,6],[130],113⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[857]? = some (⟨28,(4),[2,6],[130],113⟩) from rfl))
private theorem rec2037 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[868]? = some (⟨28,(5),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2042 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[2,6],[130],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[873]? = some (⟨28,(5),[2,6],[130],114⟩) from rfl))
private theorem rec2053 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[884]? = some (⟨28,(6),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2058 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[2,6],[130],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[889]? = some (⟨28,(6),[2,6],[130],114⟩) from rfl))
private theorem rec2069 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[900]? = some (⟨28,(7),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2074 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[2,6],[130],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[905]? = some (⟨28,(7),[2,6],[130],114⟩) from rfl))
private theorem rec2085 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[916]? = some (⟨28,(8),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2090 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[2,6],[130],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[921]? = some (⟨28,(8),[2,6],[130],114⟩) from rfl))
private theorem rec2101 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,2,5,6],[131],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[932]? = some (⟨28,(9),[1,2,5,6],[131],114⟩) from rfl))
private theorem rec2106 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[2,6],[130],114⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[937]? = some (⟨28,(9),[2,6],[130],114⟩) from rfl))
private theorem rec2117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[948]? = some (⟨28,(10),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2122 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[2,6],[130],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[953]? = some (⟨28,(10),[2,6],[130],115⟩) from rfl))
private theorem rec2133 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[964]? = some (⟨28,(11),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2138 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[2,6],[130],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[969]? = some (⟨28,(11),[2,6],[130],116⟩) from rfl))
private theorem rec2149 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,2,5,6],[131],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[980]? = some (⟨28,(12),[1,2,5,6],[131],117⟩) from rfl))
private theorem rec2154 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[2,6],[130],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[985]? = some (⟨28,(12),[2,6],[130],117⟩) from rfl))
private theorem rec2165 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[996]? = some (⟨28,(13),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2170 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[2,6],[130],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1001]? = some (⟨28,(13),[2,6],[130],116⟩) from rfl))
private theorem rec2181 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,2,5,6],[131],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1012]? = some (⟨28,(14),[1,2,5,6],[131],118⟩) from rfl))
private theorem rec2186 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[2,6],[130],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1017]? = some (⟨28,(14),[2,6],[130],118⟩) from rfl))
private theorem rec2197 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1028]? = some (⟨28,(15),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2202 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[2,6],[130],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1033]? = some (⟨28,(15),[2,6],[130],115⟩) from rfl))
private theorem rec2213 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1044]? = some (⟨28,(16),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2218 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[2,6],[130],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1049]? = some (⟨28,(16),[2,6],[130],119⟩) from rfl))
private theorem rec2229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1060]? = some (⟨28,(17),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2234 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[2,6],[130],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1065]? = some (⟨28,(17),[2,6],[130],119⟩) from rfl))
private theorem rec2245 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1076]? = some (⟨28,(18),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2250 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[2,6],[130],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1081]? = some (⟨28,(18),[2,6],[130],119⟩) from rfl))
private theorem rec2261 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,2,5,6],[131],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1092]? = some (⟨28,(19),[1,2,5,6],[131],119⟩) from rfl))
private theorem rec2266 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[2,6],[130],119⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1097]? = some (⟨28,(19),[2,6],[130],119⟩) from rfl))
private theorem rec2277 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,2,5,6],[131],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1108]? = some (⟨28,(20),[1,2,5,6],[131],115⟩) from rfl))
private theorem rec2282 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[2,6],[130],115⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1113]? = some (⟨28,(20),[2,6],[130],115⟩) from rfl))
private theorem rec2293 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1124]? = some (⟨28,(21),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2298 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[2,6],[130],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1129]? = some (⟨28,(21),[2,6],[130],116⟩) from rfl))
private theorem rec2309 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,2,5,6],[131],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1140]? = some (⟨28,(22),[1,2,5,6],[131],117⟩) from rfl))
private theorem rec2314 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[2,6],[130],117⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1145]? = some (⟨28,(22),[2,6],[130],117⟩) from rfl))
private theorem rec2325 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,2,5,6],[131],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1156]? = some (⟨28,(23),[1,2,5,6],[131],116⟩) from rfl))
private theorem rec2330 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[2,6],[130],116⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1161]? = some (⟨28,(23),[2,6],[130],116⟩) from rfl))
private theorem rec2341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,2,5,6],[131],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1172]? = some (⟨28,(24),[1,2,5,6],[131],118⟩) from rfl))
private theorem rec2346 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[2,6],[130],118⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1177]? = some (⟨28,(24),[2,6],[130],118⟩) from rfl))
private theorem rec2359 (si parent : ℕ) (hs : si ∈ ([1, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1,6],[131],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1190]? = some (⟨30,(0),[1,6],[131],120⟩) from rfl))
private theorem rec2366 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[5,6],[130],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1197]? = some (⟨30,(0),[5,6],[130],152⟩) from rfl))
private theorem rec2380 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[5,6],[130],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1211]? = some (⟨30,(1),[5,6],[130],153⟩) from rfl))
private theorem rec2381 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[6],[131],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1212]? = some (⟨30,(1),[6],[131],181⟩) from rfl))
private theorem rec2387 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2,5,6],[130],92⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1218]? = some (⟨30,(2),[1,2,5,6],[130],92⟩) from rfl))
private theorem rec2392 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,5,6],[131],120⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1223]? = some (⟨30,(2),[1,5,6],[131],120⟩) from rfl))
private theorem rec2410 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2,5,6],[130],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1241]? = some (⟨30,(3),[1,2,5,6],[130],93⟩) from rfl))
private theorem rec2419 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[5,6],[131],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1250]? = some (⟨30,(3),[5,6],[131],181⟩) from rfl))
private theorem rec2434 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2,5,6],[130],94⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1265]? = some (⟨30,(4),[1,2,5,6],[130],94⟩) from rfl))
private theorem rec2443 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[5,6],[131],182⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[0]? = some (⟨30,(4),[5,6],[131],182⟩) from rfl))
private theorem rec2458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2,5,6],[130],93⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[15]? = some (⟨30,(5),[1,2,5,6],[130],93⟩) from rfl))
private theorem rec2467 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[5,6],[131],181⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[24]? = some (⟨30,(5),[5,6],[131],181⟩) from rfl))
private theorem rec2482 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2,5,6],[130],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[39]? = some (⟨30,(6),[1,2,5,6],[130],95⟩) from rfl))
private theorem rec2491 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[5,6],[131],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[48]? = some (⟨30,(6),[5,6],[131],183⟩) from rfl))
private theorem rec2506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2,5,6],[130],95⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[63]? = some (⟨30,(7),[1,2,5,6],[130],95⟩) from rfl))
private theorem rec2515 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[5,6],[131],183⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[72]? = some (⟨30,(7),[5,6],[131],183⟩) from rfl))
private theorem rec2530 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2,5,6],[130],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[87]? = some (⟨30,(8),[1,2,5,6],[130],96⟩) from rfl))
private theorem rec2539 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[5,6],[131],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[96]? = some (⟨30,(8),[5,6],[131],184⟩) from rfl))
private theorem rec2554 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2,5,6],[130],96⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[111]? = some (⟨30,(9),[1,2,5,6],[130],96⟩) from rfl))
private theorem rec2563 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[5,6],[131],184⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[120]? = some (⟨30,(9),[5,6],[131],184⟩) from rfl))
private theorem rec2573 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,2,5,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[130]? = some (⟨33,(0),[1,2,5,6],[130],97⟩) from rfl))
private theorem rec2574 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[1,2,5,6,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[131]? = some (⟨33,(0),[1,2,5,6,14],[131],97⟩) from rfl))
private theorem rec2585 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[1,5,6],[130,131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[142]? = some (⟨33,(1),[1,5,6],[130,131],98⟩) from rfl))
private theorem rec2602 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[2,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[159]? = some (⟨33,(2),[2,6],[130],97⟩) from rfl))
private theorem rec2603 (si parent : ℕ) (hs : si ∈ ([2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[2,6,13,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[160]? = some (⟨33,(2),[2,6,13,14],[131],97⟩) from rfl))
private theorem rec2611 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[168]? = some (⟨33,(3),[1,5,6],[130],3⟩) from rfl))
private theorem rec2612 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[169]? = some (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2621 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,2,5,6],[130],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[178]? = some (⟨33,(4),[1,2,5,6],[130],2⟩) from rfl))
private theorem rec2622 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[179]? = some (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) from rfl))
private theorem rec2636 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[1,5,6],[130,131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[193]? = some (⟨33,(5),[1,5,6],[130,131],98⟩) from rfl))
private theorem rec2647 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[204]? = some (⟨33,(6),[1,5,6],[130],3⟩) from rfl))
private theorem rec2648 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[205]? = some (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2658 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[215]? = some (⟨33,(7),[1,5,6],[130],3⟩) from rfl))
private theorem rec2659 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[216]? = some (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2666 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,5,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[223]? = some (⟨33,(8),[1,2,5,6],[130],97⟩) from rfl))
private theorem rec2667 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[224]? = some (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) from rfl))
private theorem rec2676 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,5,6],[130],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[233]? = some (⟨33,(9),[1,2,5,6],[130],98⟩) from rfl))
private theorem rec2677 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,5,6,13,14],[131],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[234]? = some (⟨33,(9),[1,2,5,6,13,14],[131],98⟩) from rfl))
private theorem rec2693 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[5,6],[130],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[250]? = some (⟨33,(10),[5,6],[130],97⟩) from rfl))
private theorem rec2694 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[5,6,13,14],[131],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[251]? = some (⟨33,(10),[5,6,13,14],[131],97⟩) from rfl))
private theorem rec2697 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[254]? = some (⟨33,(11),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec2698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[255]? = some (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) from rfl))
private theorem rec2707 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[264]? = some (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) from rfl))
private theorem rec2708 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,5,6,13,14],[131],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[265]? = some (⟨33,(12),[1,2,5,6,13,14],[131],99⟩) from rfl))
private theorem rec2718 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,2,5,6],[130,131],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[275]? = some (⟨33,(13),[1,2,5,6],[130,131],99⟩) from rfl))
private theorem rec2736 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[6],[130],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[293]? = some (⟨33,(14),[6],[130],99⟩) from rfl))
private theorem rec2737 (si parent : ℕ) (hs : si ∈ ([6, 13] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[6,13],[131,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[294]? = some (⟨33,(14),[6,13],[131,146,150],99⟩) from rfl))
private theorem rec2747 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[6],[130],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[304]? = some (⟨33,(15),[6],[130],99⟩) from rfl))
private theorem rec2748 (si parent : ℕ) (hs : si ∈ ([6, 13] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[6,13],[131,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[305]? = some (⟨33,(15),[6,13],[131,146,150],99⟩) from rfl))
private theorem rec2753 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[310]? = some (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2758 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[315]? = some (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[322]? = some (⟨35,(2),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2771 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[2,6],[130],121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[328]? = some (⟨35,(2),[2,6],[130],121⟩) from rfl))
private theorem rec2781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[338]? = some (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2782 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2,5,6],[131],121⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[339]? = some (⟨35,(3),[1,2,5,6],[131],121⟩) from rfl))
private theorem rec2790 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[347]? = some (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[352]? = some (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2802 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[359]? = some (⟨35,(6),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2808 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[2,6],[130],122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[365]? = some (⟨35,(6),[2,6],[130],122⟩) from rfl))
private theorem rec2818 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[375]? = some (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2819 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2,5,6],[131],122⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[376]? = some (⟨35,(7),[1,2,5,6],[131],122⟩) from rfl))
private theorem rec2827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[384]? = some (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2832 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[389]? = some (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2839 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[396]? = some (⟨35,(10),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2845 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[2,6],[130],915⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[402]? = some (⟨35,(10),[2,6],[130],915⟩) from rfl))
private theorem rec2855 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[412]? = some (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2856 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2,5,6],[131],123⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[413]? = some (⟨35,(11),[1,2,5,6],[131],123⟩) from rfl))
private theorem rec2864 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[421]? = some (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2869 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[426]? = some (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2876 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,2,5,6],[131],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[433]? = some (⟨35,(14),[1,2,5,6],[131],101⟩) from rfl))
private theorem rec2882 (si parent : ℕ) (hs : si ∈ ([2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[2,6],[130],124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[439]? = some (⟨35,(14),[2,6],[130],124⟩) from rfl))
private theorem rec2892 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[449]? = some (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) from rfl))
private theorem rec2893 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([131] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2,5,6],[131],124⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[450]? = some (⟨35,(15),[1,2,5,6],[131],124⟩) from rfl))
private theorem rec2899 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,5,6],[130],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[456]? = some (⟨36,(5),[1,2,5,6],[130],105⟩) from rfl))
private theorem rec2900 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[457]? = some (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) from rfl))
private theorem rec2909 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[466]? = some (⟨36,(7),[1,2,5,6],[130],3⟩) from rfl))
private theorem rec2911 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[468]? = some (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) from rfl))
private theorem rec2924 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[481]? = some (⟨36,(8),[1,5,6],[130],3⟩) from rfl))
private theorem rec2925 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[482]? = some (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) from rfl))
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
private theorem rec2961 (si parent : ℕ) (hs : si ∈ ([1, 5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[518]? = some (⟨36,(16),[1,5,6],[130],3⟩) from rfl))
private theorem rec2962 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[519]? = some (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) from rfl))
private theorem rec2971 (si parent : ℕ) (hs : si ∈ ([1, 2, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1,2,6],[130],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[528]? = some (⟨36,(17),[1,2,6],[130],3⟩) from rfl))
private theorem rec2972 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[529]? = some (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) from rfl))
private theorem rec2987 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([130] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[5,6],[130],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[544]? = some (⟨36,(19),[5,6],[130],143⟩) from rfl))
private theorem rec2988 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[545]? = some (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0128_0144 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 128).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 128).take 16 = [⟨1,128,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,129,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,130,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,131,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,132,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,133,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,134,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,135,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,136,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,137,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,138,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,139,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,140,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,141,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,142,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,143,[⟨true,true,1⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 6 128 (by decide) (by decide)
  · left
    exact rec361 6 129 (by decide) (by decide)
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
        exact rec502 6 130 (by decide) (by decide)
      · right
        exact rec519 6 130 (by decide) (by decide)
      · right
        exact rec536 6 130 (by decide) (by decide)
      · right
        exact rec553 6 130 (by decide) (by decide)
      · right
        exact rec570 6 130 (by decide) (by decide)
      · right
        exact rec587 6 130 (by decide) (by decide)
      · right
        exact rec604 6 130 (by decide) (by decide)
      · right
        exact rec621 6 130 (by decide) (by decide)
      · right
        exact rec638 6 130 (by decide) (by decide)
      · right
        exact rec655 6 130 (by decide) (by decide)
      · right
        exact rec672 6 130 (by decide) (by decide)
      · right
        exact rec689 6 130 (by decide) (by decide)
      · right
        exact rec706 6 130 (by decide) (by decide)
      · right
        exact rec723 6 130 (by decide) (by decide)
      · right
        exact rec740 6 130 (by decide) (by decide)
      · right
        exact rec757 6 130 (by decide) (by decide)
      · right
        exact rec774 6 130 (by decide) (by decide)
      · right
        exact rec791 6 130 (by decide) (by decide)
      · right
        exact rec808 6 130 (by decide) (by decide)
      · right
        exact rec825 6 130 (by decide) (by decide)
      · right
        exact rec842 6 130 (by decide) (by decide)
      · right
        exact rec859 6 130 (by decide) (by decide)
      · right
        exact rec876 6 130 (by decide) (by decide)
      · right
        exact rec893 6 130 (by decide) (by decide)
      · right
        exact rec910 6 130 (by decide) (by decide)
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
        exact rec918 6 130 (by decide) (by decide)
      · right
        exact rec929 6 130 (by decide) (by decide)
      · right
        exact rec940 6 130 (by decide) (by decide)
      · right
        exact rec951 6 130 (by decide) (by decide)
      · right
        exact rec962 6 130 (by decide) (by decide)
      · right
        exact rec973 6 130 (by decide) (by decide)
      · right
        exact rec984 6 130 (by decide) (by decide)
      · right
        exact rec995 6 130 (by decide) (by decide)
      · right
        exact rec1006 6 130 (by decide) (by decide)
      · right
        exact rec1017 6 130 (by decide) (by decide)
      · right
        exact rec1028 6 130 (by decide) (by decide)
      · right
        exact rec1039 6 130 (by decide) (by decide)
      · right
        exact rec1050 6 130 (by decide) (by decide)
      · right
        exact rec1061 6 130 (by decide) (by decide)
      · right
        exact rec1072 6 130 (by decide) (by decide)
      · right
        exact rec1083 6 130 (by decide) (by decide)
      · right
        exact rec1094 6 130 (by decide) (by decide)
      · right
        exact rec1105 6 130 (by decide) (by decide)
      · right
        exact rec1116 6 130 (by decide) (by decide)
      · right
        exact rec1127 6 130 (by decide) (by decide)
      · right
        exact rec1138 6 130 (by decide) (by decide)
      · right
        exact rec1149 6 130 (by decide) (by decide)
      · right
        exact rec1160 6 130 (by decide) (by decide)
      · right
        exact rec1171 6 130 (by decide) (by decide)
      · right
        exact rec1182 6 130 (by decide) (by decide)
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
        exact rec1193 6 130 (by decide) (by decide)
      · right
        exact rec1200 6 130 (by decide) (by decide)
      · right
        exact rec1207 6 130 (by decide) (by decide)
      · right
        exact rec1214 6 130 (by decide) (by decide)
      · right
        exact rec1221 6 130 (by decide) (by decide)
      · right
        exact rec1228 6 130 (by decide) (by decide)
      · right
        exact rec1235 6 130 (by decide) (by decide)
      · right
        exact rec1242 6 130 (by decide) (by decide)
      · right
        exact rec1249 6 130 (by decide) (by decide)
      · right
        exact rec1256 6 130 (by decide) (by decide)
      · right
        exact rec1263 6 130 (by decide) (by decide)
      · right
        exact rec1270 6 130 (by decide) (by decide)
      · right
        exact rec1277 6 130 (by decide) (by decide)
      · right
        exact rec1284 6 130 (by decide) (by decide)
      · right
        exact rec1291 6 130 (by decide) (by decide)
      · right
        exact rec1298 6 130 (by decide) (by decide)
      · right
        exact rec1305 6 130 (by decide) (by decide)
      · right
        exact rec1312 6 130 (by decide) (by decide)
      · right
        exact rec1319 6 130 (by decide) (by decide)
      · right
        exact rec1326 6 130 (by decide) (by decide)
      · right
        exact rec1333 6 130 (by decide) (by decide)
      · right
        exact rec1340 6 130 (by decide) (by decide)
      · right
        exact rec1347 6 130 (by decide) (by decide)
      · right
        exact rec1354 6 130 (by decide) (by decide)
      · right
        exact rec1361 6 130 (by decide) (by decide)
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
        exact rec1368 6 130 (by decide) (by decide)
      · right
        exact rec1389 6 130 (by decide) (by decide)
      · right
        exact rec1413 6 130 (by decide) (by decide)
      · right
        exact rec1437 6 130 (by decide) (by decide)
      · right
        exact rec1461 6 130 (by decide) (by decide)
      · right
        exact rec1485 6 130 (by decide) (by decide)
      · right
        exact rec1506 6 130 (by decide) (by decide)
      · right
        exact rec1530 6 130 (by decide) (by decide)
      · right
        exact rec1554 6 130 (by decide) (by decide)
      · right
        exact rec1578 6 130 (by decide) (by decide)
      · right
        exact rec1602 6 130 (by decide) (by decide)
      · right
        exact rec1623 6 130 (by decide) (by decide)
      · right
        exact rec1647 6 130 (by decide) (by decide)
      · right
        exact rec1671 6 130 (by decide) (by decide)
      · right
        exact rec1695 6 130 (by decide) (by decide)
      · right
        exact rec1719 6 130 (by decide) (by decide)
      · right
        exact rec1740 6 130 (by decide) (by decide)
      · right
        exact rec1764 6 130 (by decide) (by decide)
      · right
        exact rec1788 6 130 (by decide) (by decide)
      · right
        exact rec1812 6 130 (by decide) (by decide)
      · right
        exact rec1836 6 130 (by decide) (by decide)
      · right
        exact rec1857 6 130 (by decide) (by decide)
      · right
        exact rec1881 6 130 (by decide) (by decide)
      · right
        exact rec1905 6 130 (by decide) (by decide)
      · right
        exact rec1929 6 130 (by decide) (by decide)
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
        exact rec1962 6 130 (by decide) (by decide)
      · right
        exact rec1978 6 130 (by decide) (by decide)
      · right
        exact rec1994 6 130 (by decide) (by decide)
      · right
        exact rec2010 6 130 (by decide) (by decide)
      · right
        exact rec2026 6 130 (by decide) (by decide)
      · right
        exact rec2042 6 130 (by decide) (by decide)
      · right
        exact rec2058 6 130 (by decide) (by decide)
      · right
        exact rec2074 6 130 (by decide) (by decide)
      · right
        exact rec2090 6 130 (by decide) (by decide)
      · right
        exact rec2106 6 130 (by decide) (by decide)
      · right
        exact rec2122 6 130 (by decide) (by decide)
      · right
        exact rec2138 6 130 (by decide) (by decide)
      · right
        exact rec2154 6 130 (by decide) (by decide)
      · right
        exact rec2170 6 130 (by decide) (by decide)
      · right
        exact rec2186 6 130 (by decide) (by decide)
      · right
        exact rec2202 6 130 (by decide) (by decide)
      · right
        exact rec2218 6 130 (by decide) (by decide)
      · right
        exact rec2234 6 130 (by decide) (by decide)
      · right
        exact rec2250 6 130 (by decide) (by decide)
      · right
        exact rec2266 6 130 (by decide) (by decide)
      · right
        exact rec2282 6 130 (by decide) (by decide)
      · right
        exact rec2298 6 130 (by decide) (by decide)
      · right
        exact rec2314 6 130 (by decide) (by decide)
      · right
        exact rec2330 6 130 (by decide) (by decide)
      · right
        exact rec2346 6 130 (by decide) (by decide)
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
        exact rec2366 6 130 (by decide) (by decide)
      · right
        exact rec2380 6 130 (by decide) (by decide)
      · right
        exact rec2387 6 130 (by decide) (by decide)
      · right
        exact rec2410 6 130 (by decide) (by decide)
      · right
        exact rec2434 6 130 (by decide) (by decide)
      · right
        exact rec2458 6 130 (by decide) (by decide)
      · right
        exact rec2482 6 130 (by decide) (by decide)
      · right
        exact rec2506 6 130 (by decide) (by decide)
      · right
        exact rec2530 6 130 (by decide) (by decide)
      · right
        exact rec2554 6 130 (by decide) (by decide)
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
        exact rec2573 6 130 (by decide) (by decide)
      · right
        exact rec2585 6 130 (by decide) (by decide)
      · right
        exact rec2602 6 130 (by decide) (by decide)
      · right
        exact rec2611 6 130 (by decide) (by decide)
      · right
        exact rec2621 6 130 (by decide) (by decide)
      · right
        exact rec2636 6 130 (by decide) (by decide)
      · right
        exact rec2647 6 130 (by decide) (by decide)
      · right
        exact rec2658 6 130 (by decide) (by decide)
      · right
        exact rec2666 6 130 (by decide) (by decide)
      · right
        exact rec2676 6 130 (by decide) (by decide)
      · right
        exact rec2693 6 130 (by decide) (by decide)
      · right
        exact rec2697 6 130 (by decide) (by decide)
      · right
        exact rec2707 6 130 (by decide) (by decide)
      · right
        exact rec2718 6 130 (by decide) (by decide)
      · right
        exact rec2736 6 130 (by decide) (by decide)
      · right
        exact rec2747 6 130 (by decide) (by decide)
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
        exact rec2753 6 130 (by decide) (by decide)
      · right
        exact rec2758 6 130 (by decide) (by decide)
      · right
        exact rec2771 6 130 (by decide) (by decide)
      · right
        exact rec2781 6 130 (by decide) (by decide)
      · right
        exact rec2790 6 130 (by decide) (by decide)
      · right
        exact rec2795 6 130 (by decide) (by decide)
      · right
        exact rec2808 6 130 (by decide) (by decide)
      · right
        exact rec2818 6 130 (by decide) (by decide)
      · right
        exact rec2827 6 130 (by decide) (by decide)
      · right
        exact rec2832 6 130 (by decide) (by decide)
      · right
        exact rec2845 6 130 (by decide) (by decide)
      · right
        exact rec2855 6 130 (by decide) (by decide)
      · right
        exact rec2864 6 130 (by decide) (by decide)
      · right
        exact rec2869 6 130 (by decide) (by decide)
      · right
        exact rec2882 6 130 (by decide) (by decide)
      · right
        exact rec2892 6 130 (by decide) (by decide)
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
        exact rec2899 6 130 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2909 6 130 (by decide) (by decide)
      · right
        exact rec2924 6 130 (by decide) (by decide)
      · right
        exact rec2940 6 130 (by decide) (by decide)
      · left
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
        exact rec2949 6 130 (by decide) (by decide)
      · right
        exact rec2961 6 130 (by decide) (by decide)
      · right
        exact rec2971 6 130 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2987 6 130 (by decide) (by decide)
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
        exact rec493 6 131 (by decide) (by decide)
      · right
        exact rec510 6 131 (by decide) (by decide)
      · right
        exact rec527 6 131 (by decide) (by decide)
      · right
        exact rec544 6 131 (by decide) (by decide)
      · right
        exact rec561 6 131 (by decide) (by decide)
      · right
        exact rec578 6 131 (by decide) (by decide)
      · right
        exact rec595 6 131 (by decide) (by decide)
      · right
        exact rec612 6 131 (by decide) (by decide)
      · right
        exact rec629 6 131 (by decide) (by decide)
      · right
        exact rec646 6 131 (by decide) (by decide)
      · right
        exact rec663 6 131 (by decide) (by decide)
      · right
        exact rec680 6 131 (by decide) (by decide)
      · right
        exact rec697 6 131 (by decide) (by decide)
      · right
        exact rec714 6 131 (by decide) (by decide)
      · right
        exact rec731 6 131 (by decide) (by decide)
      · right
        exact rec748 6 131 (by decide) (by decide)
      · right
        exact rec765 6 131 (by decide) (by decide)
      · right
        exact rec782 6 131 (by decide) (by decide)
      · right
        exact rec799 6 131 (by decide) (by decide)
      · right
        exact rec816 6 131 (by decide) (by decide)
      · right
        exact rec833 6 131 (by decide) (by decide)
      · right
        exact rec850 6 131 (by decide) (by decide)
      · right
        exact rec867 6 131 (by decide) (by decide)
      · right
        exact rec884 6 131 (by decide) (by decide)
      · right
        exact rec901 6 131 (by decide) (by decide)
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
        exact rec919 6 131 (by decide) (by decide)
      · right
        exact rec930 6 131 (by decide) (by decide)
      · right
        exact rec941 6 131 (by decide) (by decide)
      · right
        exact rec952 6 131 (by decide) (by decide)
      · right
        exact rec963 6 131 (by decide) (by decide)
      · right
        exact rec974 6 131 (by decide) (by decide)
      · right
        exact rec985 6 131 (by decide) (by decide)
      · right
        exact rec996 6 131 (by decide) (by decide)
      · right
        exact rec1007 6 131 (by decide) (by decide)
      · right
        exact rec1018 6 131 (by decide) (by decide)
      · right
        exact rec1029 6 131 (by decide) (by decide)
      · right
        exact rec1040 6 131 (by decide) (by decide)
      · right
        exact rec1051 6 131 (by decide) (by decide)
      · right
        exact rec1062 6 131 (by decide) (by decide)
      · right
        exact rec1073 6 131 (by decide) (by decide)
      · right
        exact rec1084 6 131 (by decide) (by decide)
      · right
        exact rec1095 6 131 (by decide) (by decide)
      · right
        exact rec1106 6 131 (by decide) (by decide)
      · right
        exact rec1117 6 131 (by decide) (by decide)
      · right
        exact rec1128 6 131 (by decide) (by decide)
      · right
        exact rec1139 6 131 (by decide) (by decide)
      · right
        exact rec1150 6 131 (by decide) (by decide)
      · right
        exact rec1161 6 131 (by decide) (by decide)
      · right
        exact rec1172 6 131 (by decide) (by decide)
      · right
        exact rec1183 6 131 (by decide) (by decide)
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
        exact rec1194 6 131 (by decide) (by decide)
      · right
        exact rec1201 6 131 (by decide) (by decide)
      · right
        exact rec1208 6 131 (by decide) (by decide)
      · right
        exact rec1215 6 131 (by decide) (by decide)
      · right
        exact rec1222 6 131 (by decide) (by decide)
      · right
        exact rec1229 6 131 (by decide) (by decide)
      · right
        exact rec1236 6 131 (by decide) (by decide)
      · right
        exact rec1243 6 131 (by decide) (by decide)
      · right
        exact rec1250 6 131 (by decide) (by decide)
      · right
        exact rec1257 6 131 (by decide) (by decide)
      · right
        exact rec1264 6 131 (by decide) (by decide)
      · right
        exact rec1271 6 131 (by decide) (by decide)
      · right
        exact rec1278 6 131 (by decide) (by decide)
      · right
        exact rec1285 6 131 (by decide) (by decide)
      · right
        exact rec1292 6 131 (by decide) (by decide)
      · right
        exact rec1299 6 131 (by decide) (by decide)
      · right
        exact rec1306 6 131 (by decide) (by decide)
      · right
        exact rec1313 6 131 (by decide) (by decide)
      · right
        exact rec1320 6 131 (by decide) (by decide)
      · right
        exact rec1327 6 131 (by decide) (by decide)
      · right
        exact rec1334 6 131 (by decide) (by decide)
      · right
        exact rec1341 6 131 (by decide) (by decide)
      · right
        exact rec1348 6 131 (by decide) (by decide)
      · right
        exact rec1355 6 131 (by decide) (by decide)
      · right
        exact rec1362 6 131 (by decide) (by decide)
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
        exact rec1383 6 131 (by decide) (by decide)
      · right
        exact rec1404 6 131 (by decide) (by decide)
      · right
        exact rec1428 6 131 (by decide) (by decide)
      · right
        exact rec1452 6 131 (by decide) (by decide)
      · right
        exact rec1476 6 131 (by decide) (by decide)
      · right
        exact rec1500 6 131 (by decide) (by decide)
      · right
        exact rec1521 6 131 (by decide) (by decide)
      · right
        exact rec1545 6 131 (by decide) (by decide)
      · right
        exact rec1569 6 131 (by decide) (by decide)
      · right
        exact rec1593 6 131 (by decide) (by decide)
      · right
        exact rec1617 6 131 (by decide) (by decide)
      · right
        exact rec1638 6 131 (by decide) (by decide)
      · right
        exact rec1662 6 131 (by decide) (by decide)
      · right
        exact rec1686 6 131 (by decide) (by decide)
      · right
        exact rec1710 6 131 (by decide) (by decide)
      · right
        exact rec1734 6 131 (by decide) (by decide)
      · right
        exact rec1755 6 131 (by decide) (by decide)
      · right
        exact rec1779 6 131 (by decide) (by decide)
      · right
        exact rec1803 6 131 (by decide) (by decide)
      · right
        exact rec1827 6 131 (by decide) (by decide)
      · right
        exact rec1851 6 131 (by decide) (by decide)
      · right
        exact rec1872 6 131 (by decide) (by decide)
      · right
        exact rec1896 6 131 (by decide) (by decide)
      · right
        exact rec1920 6 131 (by decide) (by decide)
      · right
        exact rec1944 6 131 (by decide) (by decide)
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
        exact rec1957 6 131 (by decide) (by decide)
      · right
        exact rec1973 6 131 (by decide) (by decide)
      · right
        exact rec1989 6 131 (by decide) (by decide)
      · right
        exact rec2005 6 131 (by decide) (by decide)
      · right
        exact rec2021 6 131 (by decide) (by decide)
      · right
        exact rec2037 6 131 (by decide) (by decide)
      · right
        exact rec2053 6 131 (by decide) (by decide)
      · right
        exact rec2069 6 131 (by decide) (by decide)
      · right
        exact rec2085 6 131 (by decide) (by decide)
      · right
        exact rec2101 6 131 (by decide) (by decide)
      · right
        exact rec2117 6 131 (by decide) (by decide)
      · right
        exact rec2133 6 131 (by decide) (by decide)
      · right
        exact rec2149 6 131 (by decide) (by decide)
      · right
        exact rec2165 6 131 (by decide) (by decide)
      · right
        exact rec2181 6 131 (by decide) (by decide)
      · right
        exact rec2197 6 131 (by decide) (by decide)
      · right
        exact rec2213 6 131 (by decide) (by decide)
      · right
        exact rec2229 6 131 (by decide) (by decide)
      · right
        exact rec2245 6 131 (by decide) (by decide)
      · right
        exact rec2261 6 131 (by decide) (by decide)
      · right
        exact rec2277 6 131 (by decide) (by decide)
      · right
        exact rec2293 6 131 (by decide) (by decide)
      · right
        exact rec2309 6 131 (by decide) (by decide)
      · right
        exact rec2325 6 131 (by decide) (by decide)
      · right
        exact rec2341 6 131 (by decide) (by decide)
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
        exact rec2359 6 131 (by decide) (by decide)
      · right
        exact rec2381 6 131 (by decide) (by decide)
      · right
        exact rec2392 6 131 (by decide) (by decide)
      · right
        exact rec2419 6 131 (by decide) (by decide)
      · right
        exact rec2443 6 131 (by decide) (by decide)
      · right
        exact rec2467 6 131 (by decide) (by decide)
      · right
        exact rec2491 6 131 (by decide) (by decide)
      · right
        exact rec2515 6 131 (by decide) (by decide)
      · right
        exact rec2539 6 131 (by decide) (by decide)
      · right
        exact rec2563 6 131 (by decide) (by decide)
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
        exact rec2574 6 131 (by decide) (by decide)
      · right
        exact rec2585 6 131 (by decide) (by decide)
      · right
        exact rec2603 6 131 (by decide) (by decide)
      · right
        exact rec2612 6 131 (by decide) (by decide)
      · right
        exact rec2622 6 131 (by decide) (by decide)
      · right
        exact rec2636 6 131 (by decide) (by decide)
      · right
        exact rec2648 6 131 (by decide) (by decide)
      · right
        exact rec2659 6 131 (by decide) (by decide)
      · right
        exact rec2667 6 131 (by decide) (by decide)
      · right
        exact rec2677 6 131 (by decide) (by decide)
      · right
        exact rec2694 6 131 (by decide) (by decide)
      · right
        exact rec2698 6 131 (by decide) (by decide)
      · right
        exact rec2708 6 131 (by decide) (by decide)
      · right
        exact rec2718 6 131 (by decide) (by decide)
      · right
        exact rec2737 6 131 (by decide) (by decide)
      · right
        exact rec2748 6 131 (by decide) (by decide)
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
        exact rec2753 6 131 (by decide) (by decide)
      · right
        exact rec2758 6 131 (by decide) (by decide)
      · right
        exact rec2765 6 131 (by decide) (by decide)
      · right
        exact rec2782 6 131 (by decide) (by decide)
      · right
        exact rec2790 6 131 (by decide) (by decide)
      · right
        exact rec2795 6 131 (by decide) (by decide)
      · right
        exact rec2802 6 131 (by decide) (by decide)
      · right
        exact rec2819 6 131 (by decide) (by decide)
      · right
        exact rec2827 6 131 (by decide) (by decide)
      · right
        exact rec2832 6 131 (by decide) (by decide)
      · right
        exact rec2839 6 131 (by decide) (by decide)
      · right
        exact rec2856 6 131 (by decide) (by decide)
      · right
        exact rec2864 6 131 (by decide) (by decide)
      · right
        exact rec2869 6 131 (by decide) (by decide)
      · right
        exact rec2876 6 131 (by decide) (by decide)
      · right
        exact rec2893 6 131 (by decide) (by decide)
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
        exact rec2900 6 131 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2911 6 131 (by decide) (by decide)
      · right
        exact rec2925 6 131 (by decide) (by decide)
      · right
        exact rec2941 6 131 (by decide) (by decide)
      · left
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
        exact rec2950 6 131 (by decide) (by decide)
      · right
        exact rec2962 6 131 (by decide) (by decide)
      · right
        exact rec2972 6 131 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2988 6 131 (by decide) (by decide)
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
    exact rec361 6 132 (by decide) (by decide)
  · left
    exact rec361 6 133 (by decide) (by decide)
  · left
    exact rec412 6 134 (by decide) (by decide)
  · left
    exact rec448 6 135 (by decide) (by decide)
  · left
    exact rec388 6 136 (by decide) (by decide)
  · left
    exact rec388 6 137 (by decide) (by decide)
  · left
    exact rec362 6 138 (by decide) (by decide)
  · left
    exact rec362 6 139 (by decide) (by decide)
  · left
    exact rec388 6 140 (by decide) (by decide)
  · left
    exact rec388 6 141 (by decide) (by decide)
  · left
    exact rec362 6 142 (by decide) (by decide)
  · left
    exact rec362 6 143 (by decide) (by decide)
end Section14Coverage_6_1_p128_144

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0128_0144


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0144_0160
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p144_160
private theorem rec361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[361]? = some (⟨16,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[362]? = some (⟨16,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[388]? = some (⟨16,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec413 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([151] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[151],917⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[413]? = some (⟨16,(-1),[2,6,14],[151],917⟩) from rfl))
private theorem rec445 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([147] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[5,6],[147],1397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[445]? = some (⟨16,(-1),[5,6],[147],1397⟩) from rfl))
private theorem rec494 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[494]? = some (⟨18,(0),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec505 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[6],[146],1513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[505]? = some (⟨18,(0),[6],[146],1513⟩) from rfl))
private theorem rec511 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[511]? = some (⟨18,(1),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec522 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[6],[146],1513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[522]? = some (⟨18,(1),[6],[146],1513⟩) from rfl))
private theorem rec528 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[528]? = some (⟨18,(2),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec539 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[6],[146],1513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[539]? = some (⟨18,(2),[6],[146],1513⟩) from rfl))
private theorem rec545 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[545]? = some (⟨18,(3),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec556 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[6],[146],1513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[556]? = some (⟨18,(3),[6],[146],1513⟩) from rfl))
private theorem rec562 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,2,5,6,13,14],[150],125⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[562]? = some (⟨18,(4),[1,2,5,6,13,14],[150],125⟩) from rfl))
private theorem rec573 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[6],[146],1513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[573]? = some (⟨18,(4),[6],[146],1513⟩) from rfl))
private theorem rec579 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[579]? = some (⟨18,(5),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec590 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[6],[146],1514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[590]? = some (⟨18,(5),[6],[146],1514⟩) from rfl))
private theorem rec596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[596]? = some (⟨18,(6),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec607 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[6],[146],1514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[607]? = some (⟨18,(6),[6],[146],1514⟩) from rfl))
private theorem rec613 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[613]? = some (⟨18,(7),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec624 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[6],[146],1514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[624]? = some (⟨18,(7),[6],[146],1514⟩) from rfl))
private theorem rec630 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[630]? = some (⟨18,(8),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec641 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[6],[146],1514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[641]? = some (⟨18,(8),[6],[146],1514⟩) from rfl))
private theorem rec647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[647]? = some (⟨18,(9),[1,2,5,6,13,14],[150],126⟩) from rfl))
private theorem rec658 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[6],[146],1514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[658]? = some (⟨18,(9),[6],[146],1514⟩) from rfl))
private theorem rec664 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[664]? = some (⟨18,(10),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec675 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[6],[146],1515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[675]? = some (⟨18,(10),[6],[146],1515⟩) from rfl))
private theorem rec681 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[681]? = some (⟨18,(11),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec692 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[6],[146],1516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[692]? = some (⟨18,(11),[6],[146],1516⟩) from rfl))
private theorem rec698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,2,5,6,13,14],[150],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[698]? = some (⟨18,(12),[1,2,5,6,13,14],[150],129⟩) from rfl))
private theorem rec709 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[6],[146],1517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[709]? = some (⟨18,(12),[6],[146],1517⟩) from rfl))
private theorem rec715 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[715]? = some (⟨18,(13),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec726 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[6],[146],1516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[726]? = some (⟨18,(13),[6],[146],1516⟩) from rfl))
private theorem rec732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,2,5,6,13,14],[150],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[732]? = some (⟨18,(14),[1,2,5,6,13,14],[150],130⟩) from rfl))
private theorem rec743 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[6],[146],1518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[743]? = some (⟨18,(14),[6],[146],1518⟩) from rfl))
private theorem rec749 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[749]? = some (⟨18,(15),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec760 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[6],[146],1515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[760]? = some (⟨18,(15),[6],[146],1515⟩) from rfl))
private theorem rec766 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[766]? = some (⟨18,(16),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec777 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[6],[146],1519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[777]? = some (⟨18,(16),[6],[146],1519⟩) from rfl))
private theorem rec783 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[783]? = some (⟨18,(17),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec794 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[6],[146],1519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[794]? = some (⟨18,(17),[6],[146],1519⟩) from rfl))
private theorem rec800 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[800]? = some (⟨18,(18),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec811 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[6],[146],1519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[811]? = some (⟨18,(18),[6],[146],1519⟩) from rfl))
private theorem rec817 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,2,5,6,13,14],[150],131⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[817]? = some (⟨18,(19),[1,2,5,6,13,14],[150],131⟩) from rfl))
private theorem rec828 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[6],[146],1519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[828]? = some (⟨18,(19),[6],[146],1519⟩) from rfl))
private theorem rec834 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,2,5,6,13,14],[150],127⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[834]? = some (⟨18,(20),[1,2,5,6,13,14],[150],127⟩) from rfl))
private theorem rec845 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[6],[146],1515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[845]? = some (⟨18,(20),[6],[146],1515⟩) from rfl))
private theorem rec851 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[851]? = some (⟨18,(21),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec862 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[6],[146],1516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[862]? = some (⟨18,(21),[6],[146],1516⟩) from rfl))
private theorem rec868 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[868]? = some (⟨18,(22),[1,2,5,6,13,14],[150],129⟩) from rfl))
private theorem rec879 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[6],[146],1517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[879]? = some (⟨18,(22),[6],[146],1517⟩) from rfl))
private theorem rec885 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[885]? = some (⟨18,(23),[1,2,5,6,13,14],[150],128⟩) from rfl))
private theorem rec896 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[6],[146],1516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[896]? = some (⟨18,(23),[6],[146],1516⟩) from rfl))
private theorem rec902 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,2,5,6,13,14],[150],130⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[902]? = some (⟨18,(24),[1,2,5,6,13,14],[150],130⟩) from rfl))
private theorem rec913 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[6],[146],1518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[913]? = some (⟨18,(24),[6],[146],1518⟩) from rfl))
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
private theorem rec1964 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[6],[146],1520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[795]? = some (⟨28,(0),[6],[146],1520⟩) from rfl))
private theorem rec1974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[805]? = some (⟨28,(1),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec1980 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[6],[146],1520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[811]? = some (⟨28,(1),[6],[146],1520⟩) from rfl))
private theorem rec1990 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[821]? = some (⟨28,(2),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec1996 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[6],[146],1520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[827]? = some (⟨28,(2),[6],[146],1520⟩) from rfl))
private theorem rec2006 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[837]? = some (⟨28,(3),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec2012 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[6],[146],1520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[843]? = some (⟨28,(3),[6],[146],1520⟩) from rfl))
private theorem rec2022 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,2,5,6],[150],132⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[853]? = some (⟨28,(4),[1,2,5,6],[150],132⟩) from rfl))
private theorem rec2028 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[6],[146],1520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[859]? = some (⟨28,(4),[6],[146],1520⟩) from rfl))
private theorem rec2038 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[869]? = some (⟨28,(5),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2044 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[6],[146],1521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[875]? = some (⟨28,(5),[6],[146],1521⟩) from rfl))
private theorem rec2054 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[885]? = some (⟨28,(6),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2060 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[6],[146],1521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[891]? = some (⟨28,(6),[6],[146],1521⟩) from rfl))
private theorem rec2070 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[901]? = some (⟨28,(7),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2076 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[6],[146],1521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[907]? = some (⟨28,(7),[6],[146],1521⟩) from rfl))
private theorem rec2086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[917]? = some (⟨28,(8),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2092 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[6],[146],1521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[923]? = some (⟨28,(8),[6],[146],1521⟩) from rfl))
private theorem rec2102 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,2,5,6],[150],133⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[933]? = some (⟨28,(9),[1,2,5,6],[150],133⟩) from rfl))
private theorem rec2108 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[6],[146],1521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[939]? = some (⟨28,(9),[6],[146],1521⟩) from rfl))
private theorem rec2118 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[949]? = some (⟨28,(10),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2124 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[6],[146],1522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[955]? = some (⟨28,(10),[6],[146],1522⟩) from rfl))
private theorem rec2134 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[965]? = some (⟨28,(11),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2140 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[6],[146],1523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[971]? = some (⟨28,(11),[6],[146],1523⟩) from rfl))
private theorem rec2150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,2,5,6],[150],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[981]? = some (⟨28,(12),[1,2,5,6],[150],136⟩) from rfl))
private theorem rec2156 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[6],[146],1524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[987]? = some (⟨28,(12),[6],[146],1524⟩) from rfl))
private theorem rec2166 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[997]? = some (⟨28,(13),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2172 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[6],[146],1523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1003]? = some (⟨28,(13),[6],[146],1523⟩) from rfl))
private theorem rec2182 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,2,5,6],[150],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1013]? = some (⟨28,(14),[1,2,5,6],[150],137⟩) from rfl))
private theorem rec2188 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[6],[146],1525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1019]? = some (⟨28,(14),[6],[146],1525⟩) from rfl))
private theorem rec2198 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1029]? = some (⟨28,(15),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2204 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[6],[146],1522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1035]? = some (⟨28,(15),[6],[146],1522⟩) from rfl))
private theorem rec2214 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1045]? = some (⟨28,(16),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2220 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[6],[146],1526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1051]? = some (⟨28,(16),[6],[146],1526⟩) from rfl))
private theorem rec2230 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1061]? = some (⟨28,(17),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2236 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[6],[146],1526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1067]? = some (⟨28,(17),[6],[146],1526⟩) from rfl))
private theorem rec2246 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1077]? = some (⟨28,(18),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2252 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[6],[146],1526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1083]? = some (⟨28,(18),[6],[146],1526⟩) from rfl))
private theorem rec2262 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,2,5,6],[150],138⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1093]? = some (⟨28,(19),[1,2,5,6],[150],138⟩) from rfl))
private theorem rec2268 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[6],[146],1526⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1099]? = some (⟨28,(19),[6],[146],1526⟩) from rfl))
private theorem rec2278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,2,5,6],[150],134⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1109]? = some (⟨28,(20),[1,2,5,6],[150],134⟩) from rfl))
private theorem rec2284 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[6],[146],1522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1115]? = some (⟨28,(20),[6],[146],1522⟩) from rfl))
private theorem rec2294 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1125]? = some (⟨28,(21),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2300 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[6],[146],1523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1131]? = some (⟨28,(21),[6],[146],1523⟩) from rfl))
private theorem rec2310 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,2,5,6],[150],136⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1141]? = some (⟨28,(22),[1,2,5,6],[150],136⟩) from rfl))
private theorem rec2316 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[6],[146],1524⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1147]? = some (⟨28,(22),[6],[146],1524⟩) from rfl))
private theorem rec2326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,2,5,6],[150],135⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1157]? = some (⟨28,(23),[1,2,5,6],[150],135⟩) from rfl))
private theorem rec2332 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[6],[146],1523⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1163]? = some (⟨28,(23),[6],[146],1523⟩) from rfl))
private theorem rec2342 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,2,5,6],[150],137⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1173]? = some (⟨28,(24),[1,2,5,6],[150],137⟩) from rfl))
private theorem rec2348 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[6],[146],1525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1179]? = some (⟨28,(24),[6],[146],1525⟩) from rfl))
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
private theorem rec2737 (si parent : ℕ) (hs : si ∈ ([6, 13] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[6,13],[131,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[294]? = some (⟨33,(14),[6,13],[131,146,150],99⟩) from rfl))
private theorem rec2748 (si parent : ℕ) (hs : si ∈ ([6, 13] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[6,13],[131,146,150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[305]? = some (⟨33,(15),[6,13],[131,146,150],99⟩) from rfl))
private theorem rec2753 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[310]? = some (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2758 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([130, 131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[315]? = some (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) from rfl))
private theorem rec2766 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,2,5,6],[150],139⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[323]? = some (⟨35,(2),[1,2,5,6],[150],139⟩) from rfl))
private theorem rec2773 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[6],[146],1527⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[330]? = some (⟨35,(2),[6],[146],1527⟩) from rfl))
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
private theorem rec2810 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[6],[146],1528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[367]? = some (⟨35,(6),[6],[146],1528⟩) from rfl))
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
private theorem rec2847 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[6],[146],1529⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[404]? = some (⟨35,(10),[6],[146],1529⟩) from rfl))
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
private theorem rec2884 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[6],[146],1530⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[441]? = some (⟨35,(14),[6],[146],1530⟩) from rfl))
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
private theorem rec2972 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[529]? = some (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) from rfl))
private theorem rec2988 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([131, 146, 150] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[545]? = some (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0144_0160 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 144).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 144).take 16 = [⟨1,144,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,145,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,146,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,147,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,148,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,149,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,150,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,151,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,152,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,153,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,154,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,155,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,156,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,157,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,158,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,159,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 6 144 (by decide) (by decide)
  · left
    exact rec361 6 145 (by decide) (by decide)
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
        exact rec505 6 146 (by decide) (by decide)
      · right
        exact rec522 6 146 (by decide) (by decide)
      · right
        exact rec539 6 146 (by decide) (by decide)
      · right
        exact rec556 6 146 (by decide) (by decide)
      · right
        exact rec573 6 146 (by decide) (by decide)
      · right
        exact rec590 6 146 (by decide) (by decide)
      · right
        exact rec607 6 146 (by decide) (by decide)
      · right
        exact rec624 6 146 (by decide) (by decide)
      · right
        exact rec641 6 146 (by decide) (by decide)
      · right
        exact rec658 6 146 (by decide) (by decide)
      · right
        exact rec675 6 146 (by decide) (by decide)
      · right
        exact rec692 6 146 (by decide) (by decide)
      · right
        exact rec709 6 146 (by decide) (by decide)
      · right
        exact rec726 6 146 (by decide) (by decide)
      · right
        exact rec743 6 146 (by decide) (by decide)
      · right
        exact rec760 6 146 (by decide) (by decide)
      · right
        exact rec777 6 146 (by decide) (by decide)
      · right
        exact rec794 6 146 (by decide) (by decide)
      · right
        exact rec811 6 146 (by decide) (by decide)
      · right
        exact rec828 6 146 (by decide) (by decide)
      · right
        exact rec845 6 146 (by decide) (by decide)
      · right
        exact rec862 6 146 (by decide) (by decide)
      · right
        exact rec879 6 146 (by decide) (by decide)
      · right
        exact rec896 6 146 (by decide) (by decide)
      · right
        exact rec913 6 146 (by decide) (by decide)
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
        exact rec919 6 146 (by decide) (by decide)
      · right
        exact rec930 6 146 (by decide) (by decide)
      · right
        exact rec941 6 146 (by decide) (by decide)
      · right
        exact rec952 6 146 (by decide) (by decide)
      · right
        exact rec963 6 146 (by decide) (by decide)
      · right
        exact rec974 6 146 (by decide) (by decide)
      · right
        exact rec985 6 146 (by decide) (by decide)
      · right
        exact rec996 6 146 (by decide) (by decide)
      · right
        exact rec1007 6 146 (by decide) (by decide)
      · right
        exact rec1018 6 146 (by decide) (by decide)
      · right
        exact rec1029 6 146 (by decide) (by decide)
      · right
        exact rec1040 6 146 (by decide) (by decide)
      · right
        exact rec1051 6 146 (by decide) (by decide)
      · right
        exact rec1062 6 146 (by decide) (by decide)
      · right
        exact rec1073 6 146 (by decide) (by decide)
      · right
        exact rec1084 6 146 (by decide) (by decide)
      · right
        exact rec1095 6 146 (by decide) (by decide)
      · right
        exact rec1106 6 146 (by decide) (by decide)
      · right
        exact rec1117 6 146 (by decide) (by decide)
      · right
        exact rec1128 6 146 (by decide) (by decide)
      · right
        exact rec1139 6 146 (by decide) (by decide)
      · right
        exact rec1150 6 146 (by decide) (by decide)
      · right
        exact rec1161 6 146 (by decide) (by decide)
      · right
        exact rec1172 6 146 (by decide) (by decide)
      · right
        exact rec1183 6 146 (by decide) (by decide)
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
        exact rec1194 6 146 (by decide) (by decide)
      · right
        exact rec1201 6 146 (by decide) (by decide)
      · right
        exact rec1208 6 146 (by decide) (by decide)
      · right
        exact rec1215 6 146 (by decide) (by decide)
      · right
        exact rec1222 6 146 (by decide) (by decide)
      · right
        exact rec1229 6 146 (by decide) (by decide)
      · right
        exact rec1236 6 146 (by decide) (by decide)
      · right
        exact rec1243 6 146 (by decide) (by decide)
      · right
        exact rec1250 6 146 (by decide) (by decide)
      · right
        exact rec1257 6 146 (by decide) (by decide)
      · right
        exact rec1264 6 146 (by decide) (by decide)
      · right
        exact rec1271 6 146 (by decide) (by decide)
      · right
        exact rec1278 6 146 (by decide) (by decide)
      · right
        exact rec1285 6 146 (by decide) (by decide)
      · right
        exact rec1292 6 146 (by decide) (by decide)
      · right
        exact rec1299 6 146 (by decide) (by decide)
      · right
        exact rec1306 6 146 (by decide) (by decide)
      · right
        exact rec1313 6 146 (by decide) (by decide)
      · right
        exact rec1320 6 146 (by decide) (by decide)
      · right
        exact rec1327 6 146 (by decide) (by decide)
      · right
        exact rec1334 6 146 (by decide) (by decide)
      · right
        exact rec1341 6 146 (by decide) (by decide)
      · right
        exact rec1348 6 146 (by decide) (by decide)
      · right
        exact rec1355 6 146 (by decide) (by decide)
      · right
        exact rec1362 6 146 (by decide) (by decide)
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
        exact rec1369 6 146 (by decide) (by decide)
      · right
        exact rec1390 6 146 (by decide) (by decide)
      · right
        exact rec1414 6 146 (by decide) (by decide)
      · right
        exact rec1438 6 146 (by decide) (by decide)
      · right
        exact rec1462 6 146 (by decide) (by decide)
      · right
        exact rec1486 6 146 (by decide) (by decide)
      · right
        exact rec1507 6 146 (by decide) (by decide)
      · right
        exact rec1531 6 146 (by decide) (by decide)
      · right
        exact rec1555 6 146 (by decide) (by decide)
      · right
        exact rec1579 6 146 (by decide) (by decide)
      · right
        exact rec1603 6 146 (by decide) (by decide)
      · right
        exact rec1624 6 146 (by decide) (by decide)
      · right
        exact rec1648 6 146 (by decide) (by decide)
      · right
        exact rec1672 6 146 (by decide) (by decide)
      · right
        exact rec1696 6 146 (by decide) (by decide)
      · right
        exact rec1720 6 146 (by decide) (by decide)
      · right
        exact rec1741 6 146 (by decide) (by decide)
      · right
        exact rec1765 6 146 (by decide) (by decide)
      · right
        exact rec1789 6 146 (by decide) (by decide)
      · right
        exact rec1813 6 146 (by decide) (by decide)
      · right
        exact rec1837 6 146 (by decide) (by decide)
      · right
        exact rec1858 6 146 (by decide) (by decide)
      · right
        exact rec1882 6 146 (by decide) (by decide)
      · right
        exact rec1906 6 146 (by decide) (by decide)
      · right
        exact rec1930 6 146 (by decide) (by decide)
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
        exact rec1964 6 146 (by decide) (by decide)
      · right
        exact rec1980 6 146 (by decide) (by decide)
      · right
        exact rec1996 6 146 (by decide) (by decide)
      · right
        exact rec2012 6 146 (by decide) (by decide)
      · right
        exact rec2028 6 146 (by decide) (by decide)
      · right
        exact rec2044 6 146 (by decide) (by decide)
      · right
        exact rec2060 6 146 (by decide) (by decide)
      · right
        exact rec2076 6 146 (by decide) (by decide)
      · right
        exact rec2092 6 146 (by decide) (by decide)
      · right
        exact rec2108 6 146 (by decide) (by decide)
      · right
        exact rec2124 6 146 (by decide) (by decide)
      · right
        exact rec2140 6 146 (by decide) (by decide)
      · right
        exact rec2156 6 146 (by decide) (by decide)
      · right
        exact rec2172 6 146 (by decide) (by decide)
      · right
        exact rec2188 6 146 (by decide) (by decide)
      · right
        exact rec2204 6 146 (by decide) (by decide)
      · right
        exact rec2220 6 146 (by decide) (by decide)
      · right
        exact rec2236 6 146 (by decide) (by decide)
      · right
        exact rec2252 6 146 (by decide) (by decide)
      · right
        exact rec2268 6 146 (by decide) (by decide)
      · right
        exact rec2284 6 146 (by decide) (by decide)
      · right
        exact rec2300 6 146 (by decide) (by decide)
      · right
        exact rec2316 6 146 (by decide) (by decide)
      · right
        exact rec2332 6 146 (by decide) (by decide)
      · right
        exact rec2348 6 146 (by decide) (by decide)
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
        exact rec2358 6 146 (by decide) (by decide)
      · right
        exact rec2374 6 146 (by decide) (by decide)
      · right
        exact rec2388 6 146 (by decide) (by decide)
      · right
        exact rec2411 6 146 (by decide) (by decide)
      · right
        exact rec2435 6 146 (by decide) (by decide)
      · right
        exact rec2459 6 146 (by decide) (by decide)
      · right
        exact rec2483 6 146 (by decide) (by decide)
      · right
        exact rec2507 6 146 (by decide) (by decide)
      · right
        exact rec2531 6 146 (by decide) (by decide)
      · right
        exact rec2555 6 146 (by decide) (by decide)
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
        exact rec2576 6 146 (by decide) (by decide)
      · right
        exact rec2589 6 146 (by decide) (by decide)
      · right
        exact rec2598 6 146 (by decide) (by decide)
      · right
        exact rec2612 6 146 (by decide) (by decide)
      · right
        exact rec2624 6 146 (by decide) (by decide)
      · right
        exact rec2633 6 146 (by decide) (by decide)
      · right
        exact rec2648 6 146 (by decide) (by decide)
      · right
        exact rec2659 6 146 (by decide) (by decide)
      · right
        exact rec2668 6 146 (by decide) (by decide)
      · right
        exact rec2678 6 146 (by decide) (by decide)
      · right
        exact rec2688 6 146 (by decide) (by decide)
      · right
        exact rec2698 6 146 (by decide) (by decide)
      · right
        exact rec2707 6 146 (by decide) (by decide)
      · right
        exact rec2719 6 146 (by decide) (by decide)
      · right
        exact rec2737 6 146 (by decide) (by decide)
      · right
        exact rec2748 6 146 (by decide) (by decide)
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
        exact rec2753 6 146 (by decide) (by decide)
      · right
        exact rec2758 6 146 (by decide) (by decide)
      · right
        exact rec2773 6 146 (by decide) (by decide)
      · right
        exact rec2781 6 146 (by decide) (by decide)
      · right
        exact rec2790 6 146 (by decide) (by decide)
      · right
        exact rec2795 6 146 (by decide) (by decide)
      · right
        exact rec2810 6 146 (by decide) (by decide)
      · right
        exact rec2818 6 146 (by decide) (by decide)
      · right
        exact rec2827 6 146 (by decide) (by decide)
      · right
        exact rec2832 6 146 (by decide) (by decide)
      · right
        exact rec2847 6 146 (by decide) (by decide)
      · right
        exact rec2855 6 146 (by decide) (by decide)
      · right
        exact rec2864 6 146 (by decide) (by decide)
      · right
        exact rec2869 6 146 (by decide) (by decide)
      · right
        exact rec2884 6 146 (by decide) (by decide)
      · right
        exact rec2892 6 146 (by decide) (by decide)
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
        exact rec2900 6 146 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2911 6 146 (by decide) (by decide)
      · right
        exact rec2925 6 146 (by decide) (by decide)
      · right
        exact rec2941 6 146 (by decide) (by decide)
      · left
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
        exact rec2950 6 146 (by decide) (by decide)
      · right
        exact rec2962 6 146 (by decide) (by decide)
      · right
        exact rec2972 6 146 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2988 6 146 (by decide) (by decide)
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
    exact rec445 6 147 (by decide) (by decide)
  · left
    exact rec361 6 148 (by decide) (by decide)
  · left
    exact rec361 6 149 (by decide) (by decide)
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
        exact rec494 6 150 (by decide) (by decide)
      · right
        exact rec511 6 150 (by decide) (by decide)
      · right
        exact rec528 6 150 (by decide) (by decide)
      · right
        exact rec545 6 150 (by decide) (by decide)
      · right
        exact rec562 6 150 (by decide) (by decide)
      · right
        exact rec579 6 150 (by decide) (by decide)
      · right
        exact rec596 6 150 (by decide) (by decide)
      · right
        exact rec613 6 150 (by decide) (by decide)
      · right
        exact rec630 6 150 (by decide) (by decide)
      · right
        exact rec647 6 150 (by decide) (by decide)
      · right
        exact rec664 6 150 (by decide) (by decide)
      · right
        exact rec681 6 150 (by decide) (by decide)
      · right
        exact rec698 6 150 (by decide) (by decide)
      · right
        exact rec715 6 150 (by decide) (by decide)
      · right
        exact rec732 6 150 (by decide) (by decide)
      · right
        exact rec749 6 150 (by decide) (by decide)
      · right
        exact rec766 6 150 (by decide) (by decide)
      · right
        exact rec783 6 150 (by decide) (by decide)
      · right
        exact rec800 6 150 (by decide) (by decide)
      · right
        exact rec817 6 150 (by decide) (by decide)
      · right
        exact rec834 6 150 (by decide) (by decide)
      · right
        exact rec851 6 150 (by decide) (by decide)
      · right
        exact rec868 6 150 (by decide) (by decide)
      · right
        exact rec885 6 150 (by decide) (by decide)
      · right
        exact rec902 6 150 (by decide) (by decide)
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
        exact rec919 6 150 (by decide) (by decide)
      · right
        exact rec930 6 150 (by decide) (by decide)
      · right
        exact rec941 6 150 (by decide) (by decide)
      · right
        exact rec952 6 150 (by decide) (by decide)
      · right
        exact rec963 6 150 (by decide) (by decide)
      · right
        exact rec974 6 150 (by decide) (by decide)
      · right
        exact rec985 6 150 (by decide) (by decide)
      · right
        exact rec996 6 150 (by decide) (by decide)
      · right
        exact rec1007 6 150 (by decide) (by decide)
      · right
        exact rec1018 6 150 (by decide) (by decide)
      · right
        exact rec1029 6 150 (by decide) (by decide)
      · right
        exact rec1040 6 150 (by decide) (by decide)
      · right
        exact rec1051 6 150 (by decide) (by decide)
      · right
        exact rec1062 6 150 (by decide) (by decide)
      · right
        exact rec1073 6 150 (by decide) (by decide)
      · right
        exact rec1084 6 150 (by decide) (by decide)
      · right
        exact rec1095 6 150 (by decide) (by decide)
      · right
        exact rec1106 6 150 (by decide) (by decide)
      · right
        exact rec1117 6 150 (by decide) (by decide)
      · right
        exact rec1128 6 150 (by decide) (by decide)
      · right
        exact rec1139 6 150 (by decide) (by decide)
      · right
        exact rec1150 6 150 (by decide) (by decide)
      · right
        exact rec1161 6 150 (by decide) (by decide)
      · right
        exact rec1172 6 150 (by decide) (by decide)
      · right
        exact rec1183 6 150 (by decide) (by decide)
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
        exact rec1194 6 150 (by decide) (by decide)
      · right
        exact rec1201 6 150 (by decide) (by decide)
      · right
        exact rec1208 6 150 (by decide) (by decide)
      · right
        exact rec1215 6 150 (by decide) (by decide)
      · right
        exact rec1222 6 150 (by decide) (by decide)
      · right
        exact rec1229 6 150 (by decide) (by decide)
      · right
        exact rec1236 6 150 (by decide) (by decide)
      · right
        exact rec1243 6 150 (by decide) (by decide)
      · right
        exact rec1250 6 150 (by decide) (by decide)
      · right
        exact rec1257 6 150 (by decide) (by decide)
      · right
        exact rec1264 6 150 (by decide) (by decide)
      · right
        exact rec1271 6 150 (by decide) (by decide)
      · right
        exact rec1278 6 150 (by decide) (by decide)
      · right
        exact rec1285 6 150 (by decide) (by decide)
      · right
        exact rec1292 6 150 (by decide) (by decide)
      · right
        exact rec1299 6 150 (by decide) (by decide)
      · right
        exact rec1306 6 150 (by decide) (by decide)
      · right
        exact rec1313 6 150 (by decide) (by decide)
      · right
        exact rec1320 6 150 (by decide) (by decide)
      · right
        exact rec1327 6 150 (by decide) (by decide)
      · right
        exact rec1334 6 150 (by decide) (by decide)
      · right
        exact rec1341 6 150 (by decide) (by decide)
      · right
        exact rec1348 6 150 (by decide) (by decide)
      · right
        exact rec1355 6 150 (by decide) (by decide)
      · right
        exact rec1362 6 150 (by decide) (by decide)
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
        exact rec1370 6 150 (by decide) (by decide)
      · right
        exact rec1405 6 150 (by decide) (by decide)
      · right
        exact rec1429 6 150 (by decide) (by decide)
      · right
        exact rec1453 6 150 (by decide) (by decide)
      · right
        exact rec1477 6 150 (by decide) (by decide)
      · right
        exact rec1487 6 150 (by decide) (by decide)
      · right
        exact rec1522 6 150 (by decide) (by decide)
      · right
        exact rec1546 6 150 (by decide) (by decide)
      · right
        exact rec1570 6 150 (by decide) (by decide)
      · right
        exact rec1594 6 150 (by decide) (by decide)
      · right
        exact rec1604 6 150 (by decide) (by decide)
      · right
        exact rec1639 6 150 (by decide) (by decide)
      · right
        exact rec1663 6 150 (by decide) (by decide)
      · right
        exact rec1687 6 150 (by decide) (by decide)
      · right
        exact rec1711 6 150 (by decide) (by decide)
      · right
        exact rec1721 6 150 (by decide) (by decide)
      · right
        exact rec1756 6 150 (by decide) (by decide)
      · right
        exact rec1780 6 150 (by decide) (by decide)
      · right
        exact rec1804 6 150 (by decide) (by decide)
      · right
        exact rec1828 6 150 (by decide) (by decide)
      · right
        exact rec1838 6 150 (by decide) (by decide)
      · right
        exact rec1873 6 150 (by decide) (by decide)
      · right
        exact rec1897 6 150 (by decide) (by decide)
      · right
        exact rec1921 6 150 (by decide) (by decide)
      · right
        exact rec1945 6 150 (by decide) (by decide)
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
        exact rec1958 6 150 (by decide) (by decide)
      · right
        exact rec1974 6 150 (by decide) (by decide)
      · right
        exact rec1990 6 150 (by decide) (by decide)
      · right
        exact rec2006 6 150 (by decide) (by decide)
      · right
        exact rec2022 6 150 (by decide) (by decide)
      · right
        exact rec2038 6 150 (by decide) (by decide)
      · right
        exact rec2054 6 150 (by decide) (by decide)
      · right
        exact rec2070 6 150 (by decide) (by decide)
      · right
        exact rec2086 6 150 (by decide) (by decide)
      · right
        exact rec2102 6 150 (by decide) (by decide)
      · right
        exact rec2118 6 150 (by decide) (by decide)
      · right
        exact rec2134 6 150 (by decide) (by decide)
      · right
        exact rec2150 6 150 (by decide) (by decide)
      · right
        exact rec2166 6 150 (by decide) (by decide)
      · right
        exact rec2182 6 150 (by decide) (by decide)
      · right
        exact rec2198 6 150 (by decide) (by decide)
      · right
        exact rec2214 6 150 (by decide) (by decide)
      · right
        exact rec2230 6 150 (by decide) (by decide)
      · right
        exact rec2246 6 150 (by decide) (by decide)
      · right
        exact rec2262 6 150 (by decide) (by decide)
      · right
        exact rec2278 6 150 (by decide) (by decide)
      · right
        exact rec2294 6 150 (by decide) (by decide)
      · right
        exact rec2310 6 150 (by decide) (by decide)
      · right
        exact rec2326 6 150 (by decide) (by decide)
      · right
        exact rec2342 6 150 (by decide) (by decide)
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
        exact rec2358 6 150 (by decide) (by decide)
      · right
        exact rec2374 6 150 (by decide) (by decide)
      · right
        exact rec2389 6 150 (by decide) (by decide)
      · right
        exact rec2420 6 150 (by decide) (by decide)
      · right
        exact rec2444 6 150 (by decide) (by decide)
      · right
        exact rec2468 6 150 (by decide) (by decide)
      · right
        exact rec2492 6 150 (by decide) (by decide)
      · right
        exact rec2516 6 150 (by decide) (by decide)
      · right
        exact rec2540 6 150 (by decide) (by decide)
      · right
        exact rec2564 6 150 (by decide) (by decide)
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
        exact rec2576 6 150 (by decide) (by decide)
      · right
        exact rec2589 6 150 (by decide) (by decide)
      · right
        exact rec2598 6 150 (by decide) (by decide)
      · right
        exact rec2612 6 150 (by decide) (by decide)
      · right
        exact rec2624 6 150 (by decide) (by decide)
      · right
        exact rec2633 6 150 (by decide) (by decide)
      · right
        exact rec2648 6 150 (by decide) (by decide)
      · right
        exact rec2659 6 150 (by decide) (by decide)
      · right
        exact rec2668 6 150 (by decide) (by decide)
      · right
        exact rec2678 6 150 (by decide) (by decide)
      · right
        exact rec2688 6 150 (by decide) (by decide)
      · right
        exact rec2698 6 150 (by decide) (by decide)
      · right
        exact rec2707 6 150 (by decide) (by decide)
      · right
        exact rec2719 6 150 (by decide) (by decide)
      · right
        exact rec2737 6 150 (by decide) (by decide)
      · right
        exact rec2748 6 150 (by decide) (by decide)
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
        exact rec2753 6 150 (by decide) (by decide)
      · right
        exact rec2758 6 150 (by decide) (by decide)
      · right
        exact rec2766 6 150 (by decide) (by decide)
      · right
        exact rec2781 6 150 (by decide) (by decide)
      · right
        exact rec2790 6 150 (by decide) (by decide)
      · right
        exact rec2795 6 150 (by decide) (by decide)
      · right
        exact rec2803 6 150 (by decide) (by decide)
      · right
        exact rec2818 6 150 (by decide) (by decide)
      · right
        exact rec2827 6 150 (by decide) (by decide)
      · right
        exact rec2832 6 150 (by decide) (by decide)
      · right
        exact rec2840 6 150 (by decide) (by decide)
      · right
        exact rec2855 6 150 (by decide) (by decide)
      · right
        exact rec2864 6 150 (by decide) (by decide)
      · right
        exact rec2869 6 150 (by decide) (by decide)
      · right
        exact rec2877 6 150 (by decide) (by decide)
      · right
        exact rec2892 6 150 (by decide) (by decide)
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
        exact rec2900 6 150 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2910 6 150 (by decide) (by decide)
      · right
        exact rec2921 6 150 (by decide) (by decide)
      · right
        exact rec2935 6 150 (by decide) (by decide)
      · left
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
        exact rec2951 6 150 (by decide) (by decide)
      · right
        exact rec2958 6 150 (by decide) (by decide)
      · right
        exact rec2972 6 150 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2988 6 150 (by decide) (by decide)
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
    exact rec413 6 151 (by decide) (by decide)
  · left
    exact rec388 6 152 (by decide) (by decide)
  · left
    exact rec388 6 153 (by decide) (by decide)
  · left
    exact rec362 6 154 (by decide) (by decide)
  · left
    exact rec362 6 155 (by decide) (by decide)
  · left
    exact rec388 6 156 (by decide) (by decide)
  · left
    exact rec388 6 157 (by decide) (by decide)
  · left
    exact rec362 6 158 (by decide) (by decide)
  · left
    exact rec362 6 159 (by decide) (by decide)
end Section14Coverage_6_1_p144_160

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0144_0160


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0160_0176
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p160_176
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
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0160_0176 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 160).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 160).take 16 = [⟨1,160,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,161,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,162,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,163,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,164,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,165,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,166,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,167,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,168,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,169,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,170,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨1,171,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,172,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,173,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,174,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,175,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 6 160 (by decide) (by decide)
  · left
    exact rec388 6 161 (by decide) (by decide)
  · left
    exact rec362 6 162 (by decide) (by decide)
  · left
    exact rec362 6 163 (by decide) (by decide)
  · left
    exact rec388 6 164 (by decide) (by decide)
  · left
    exact rec388 6 165 (by decide) (by decide)
  · left
    exact rec362 6 166 (by decide) (by decide)
  · left
    exact rec362 6 167 (by decide) (by decide)
  · left
    exact rec361 6 168 (by decide) (by decide)
  · left
    exact rec361 6 169 (by decide) (by decide)
  · left
    exact rec403 6 170 (by decide) (by decide)
  · left
    exact rec378 6 171 (by decide) (by decide)
  · left
    exact rec361 6 172 (by decide) (by decide)
  · left
    exact rec361 6 173 (by decide) (by decide)
  · left
    exact rec377 6 174 (by decide) (by decide)
  · left
    exact rec379 6 175 (by decide) (by decide)
end Section14Coverage_6_1_p160_176

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0160_0176


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0176_0192
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p176_192
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
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0176_0192 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 176).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 176).take 16 = [⟨1,176,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,177,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,178,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,179,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,180,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,181,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,182,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,183,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,184,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,185,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,186,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,187,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,188,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,189,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,190,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,191,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 6 176 (by decide) (by decide)
  · left
    exact rec388 6 177 (by decide) (by decide)
  · left
    exact rec362 6 178 (by decide) (by decide)
  · left
    exact rec362 6 179 (by decide) (by decide)
  · left
    exact rec388 6 180 (by decide) (by decide)
  · left
    exact rec388 6 181 (by decide) (by decide)
  · left
    exact rec362 6 182 (by decide) (by decide)
  · left
    exact rec362 6 183 (by decide) (by decide)
  · left
    exact rec361 6 184 (by decide) (by decide)
  · left
    exact rec361 6 185 (by decide) (by decide)
  · left
    exact rec380 6 186 (by decide) (by decide)
  · left
    exact rec378 6 187 (by decide) (by decide)
  · left
    exact rec361 6 188 (by decide) (by decide)
  · left
    exact rec361 6 189 (by decide) (by decide)
  · left
    exact rec446 6 190 (by decide) (by decide)
  · left
    exact rec381 6 191 (by decide) (by decide)
end Section14Coverage_6_1_p176_192

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0176_0192


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0192_0208
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p192_208
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
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0192_0208 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 192).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 192).take 16 = [⟨1,192,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,193,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,194,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,195,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,196,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,197,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,198,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,199,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,200,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,201,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,202,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,203,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,204,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,205,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,206,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,207,[⟨true,true,1⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,true,2⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 6 192 (by decide) (by decide)
  · left
    exact rec361 6 193 (by decide) (by decide)
  · left
    exact rec382 6 194 (by decide) (by decide)
  · left
    exact rec382 6 195 (by decide) (by decide)
  · left
    exact rec361 6 196 (by decide) (by decide)
  · left
    exact rec361 6 197 (by decide) (by decide)
  · left
    exact rec383 6 198 (by decide) (by decide)
  · left
    exact rec383 6 199 (by decide) (by decide)
  · left
    exact rec388 6 200 (by decide) (by decide)
  · left
    exact rec388 6 201 (by decide) (by decide)
  · left
    exact rec362 6 202 (by decide) (by decide)
  · left
    exact rec362 6 203 (by decide) (by decide)
  · left
    exact rec388 6 204 (by decide) (by decide)
  · left
    exact rec388 6 205 (by decide) (by decide)
  · left
    exact rec362 6 206 (by decide) (by decide)
  · left
    exact rec362 6 207 (by decide) (by decide)
end Section14Coverage_6_1_p192_208

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0192_0208


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0208_0224
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p208_224
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
private theorem rec442 (si parent : ℕ) (hs : si ∈ ([5, 6] : List ℕ)) (hp : parent ∈ ([214, 215] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[5,6],[214,215],241⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[442]? = some (⟨16,(-1),[5,6],[214,215],241⟩) from rfl))
private theorem rec450 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([211] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[6],[211],1531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[450]? = some (⟨16,(-1),[6],[211],1531⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0208_0224 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 208).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 208).take 16 = [⟨1,208,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,209,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,210,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,211,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,212,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,213,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,214,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,215,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,216,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,217,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,218,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,219,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,220,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,221,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,222,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,223,[⟨true,true,1⟩,⟨true,false,2⟩,⟨true,false,20⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec361 6 208 (by decide) (by decide)
  · left
    exact rec361 6 209 (by decide) (by decide)
  · left
    exact rec384 6 210 (by decide) (by decide)
  · left
    exact rec450 6 211 (by decide) (by decide)
  · left
    exact rec361 6 212 (by decide) (by decide)
  · left
    exact rec361 6 213 (by decide) (by decide)
  · left
    exact rec442 6 214 (by decide) (by decide)
  · left
    exact rec442 6 215 (by decide) (by decide)
  · left
    exact rec388 6 216 (by decide) (by decide)
  · left
    exact rec388 6 217 (by decide) (by decide)
  · left
    exact rec362 6 218 (by decide) (by decide)
  · left
    exact rec362 6 219 (by decide) (by decide)
  · left
    exact rec388 6 220 (by decide) (by decide)
  · left
    exact rec388 6 221 (by decide) (by decide)
  · left
    exact rec362 6 222 (by decide) (by decide)
  · left
    exact rec362 6 223 (by decide) (by decide)
end Section14Coverage_6_1_p208_224

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0208_0224


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0224_0240
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p224_240
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
private theorem rec408 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([239] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[239],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[408]? = some (⟨16,(-1),[2,6,14],[239],207⟩) from rfl))
private theorem rec447 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([235, 251] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[6],[235,251],206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[447]? = some (⟨16,(-1),[6],[235,251],206⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0224_0240 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 224).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 224).take 16 = [⟨1,224,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,225,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,226,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,227,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,228,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,229,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,230,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,231,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,232,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,233,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,234,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,235,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,236,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,237,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,238,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,239,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,false,19⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 6 224 (by decide) (by decide)
  · left
    exact rec388 6 225 (by decide) (by decide)
  · left
    exact rec362 6 226 (by decide) (by decide)
  · left
    exact rec362 6 227 (by decide) (by decide)
  · left
    exact rec388 6 228 (by decide) (by decide)
  · left
    exact rec388 6 229 (by decide) (by decide)
  · left
    exact rec362 6 230 (by decide) (by decide)
  · left
    exact rec362 6 231 (by decide) (by decide)
  · left
    exact rec361 6 232 (by decide) (by decide)
  · left
    exact rec361 6 233 (by decide) (by decide)
  · left
    exact rec385 6 234 (by decide) (by decide)
  · left
    exact rec447 6 235 (by decide) (by decide)
  · left
    exact rec361 6 236 (by decide) (by decide)
  · left
    exact rec361 6 237 (by decide) (by decide)
  · left
    exact rec386 6 238 (by decide) (by decide)
  · left
    exact rec408 6 239 (by decide) (by decide)
end Section14Coverage_6_1_p224_240

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0224_0240


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0240_0256
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_6_1_p240_256
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
private theorem rec409 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([255] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[2,6,14],[255],239⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[409]? = some (⟨16,(-1),[2,6,14],[255],239⟩) from rfl))
private theorem rec447 (si parent : ℕ) (hs : si ∈ ([6] : List ℕ)) (hp : parent ∈ ([235, 251] : List ℕ)) : section14Recorded section14Catalog si parent 16 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨16,(-1),[6],[235,251],206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[447]? = some (⟨16,(-1),[6],[235,251],206⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0006_coverage0001_parents_0240_0256 : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 240).take 16, section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 6).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 6)).drop 240).take 16 = [⟨1,240,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,241,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,242,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,243,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,244,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,245,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,246,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,247,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,248,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,249,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,250,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,251,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,252,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,253,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,254,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩,⟨1,255,[⟨true,true,1⟩,⟨true,false,21⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,18⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 6 240 (by decide) (by decide)
  · left
    exact rec388 6 241 (by decide) (by decide)
  · left
    exact rec362 6 242 (by decide) (by decide)
  · left
    exact rec362 6 243 (by decide) (by decide)
  · left
    exact rec388 6 244 (by decide) (by decide)
  · left
    exact rec388 6 245 (by decide) (by decide)
  · left
    exact rec362 6 246 (by decide) (by decide)
  · left
    exact rec362 6 247 (by decide) (by decide)
  · left
    exact rec361 6 248 (by decide) (by decide)
  · left
    exact rec361 6 249 (by decide) (by decide)
  · left
    exact rec385 6 250 (by decide) (by decide)
  · left
    exact rec447 6 251 (by decide) (by decide)
  · left
    exact rec361 6 252 (by decide) (by decide)
  · left
    exact rec361 6 253 (by decide) (by decide)
  · left
    exact rec387 6 254 (by decide) (by decide)
  · left
    exact rec409 6 255 (by decide) (by decide)
end Section14Coverage_6_1_p240_256

end WorkReverseInterface_Freiman_workReverse20260919_s0006_coverage0001_parents_0240_0256

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
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 6).plans.drop 1).take 1, ∀ b ∈ section14Parents section14Catalog (section14State section14Catalog 6), section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j := by
  intro pl hpl
  let xs := section14Parents section14Catalog (section14State section14Catalog 6)
  let P := fun b : Section14Parent => section14Recorded section14Catalog 6 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 6 b.branch gs.1 j
  have h256 : ∀ x ∈ xs.drop 256, P x := by
    apply all_empty P _
    rfl
  have h240 : ∀ x ∈ xs.drop 240, P x := by
    apply all_of_chunks P xs 240 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0240_0256 pl hpl)
    exact h256
  have h224 : ∀ x ∈ xs.drop 224, P x := by
    apply all_of_chunks P xs 224 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0224_0240 pl hpl)
    exact h240
  have h208 : ∀ x ∈ xs.drop 208, P x := by
    apply all_of_chunks P xs 208 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0208_0224 pl hpl)
    exact h224
  have h192 : ∀ x ∈ xs.drop 192, P x := by
    apply all_of_chunks P xs 192 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0192_0208 pl hpl)
    exact h208
  have h176 : ∀ x ∈ xs.drop 176, P x := by
    apply all_of_chunks P xs 176 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0176_0192 pl hpl)
    exact h192
  have h160 : ∀ x ∈ xs.drop 160, P x := by
    apply all_of_chunks P xs 160 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0160_0176 pl hpl)
    exact h176
  have h144 : ∀ x ∈ xs.drop 144, P x := by
    apply all_of_chunks P xs 144 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0144_0160 pl hpl)
    exact h160
  have h128 : ∀ x ∈ xs.drop 128, P x := by
    apply all_of_chunks P xs 128 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0128_0144 pl hpl)
    exact h144
  have h112 : ∀ x ∈ xs.drop 112, P x := by
    apply all_of_chunks P xs 112 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0112_0128 pl hpl)
    exact h128
  have h96 : ∀ x ∈ xs.drop 96, P x := by
    apply all_of_chunks P xs 96 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0096_0112 pl hpl)
    exact h112
  have h80 : ∀ x ∈ xs.drop 80, P x := by
    apply all_of_chunks P xs 80 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0080_0096 pl hpl)
    exact h96
  have h64 : ∀ x ∈ xs.drop 64, P x := by
    apply all_of_chunks P xs 64 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0064_0080 pl hpl)
    exact h80
  have h48 : ∀ x ∈ xs.drop 48, P x := by
    apply all_of_chunks P xs 48 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0048_0064 pl hpl)
    exact h64
  have h32 : ∀ x ∈ xs.drop 32, P x := by
    apply all_of_chunks P xs 32 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0032_0048 pl hpl)
    exact h48
  have h16 : ∀ x ∈ xs.drop 16, P x := by
    apply all_of_chunks P xs 16 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0016_0032 pl hpl)
    exact h32
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 16 (Freiman.workReverse20260919_s0006_coverage0001_parents_0000_0016 pl hpl)
    exact h16
  simpa only [List.drop_zero] using h0

#print axioms solution
