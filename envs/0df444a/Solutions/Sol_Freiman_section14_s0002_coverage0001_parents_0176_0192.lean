-- Prove2me | solution 1 for Freiman.section14_s0002_coverage0001_parents_0176_0192
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:53:16.497528+00:00
-- url     : https://prove2.me/submissions/1b496e02-2c9e-4f42-a9cf-8ecf429ef2a5

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
namespace Section14Coverage_2_1_p176_192
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
private theorem rec495 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(0),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[495]? = some (⟨18,(0),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec512 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(1),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[512]? = some (⟨18,(1),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec529 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(2),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[529]? = some (⟨18,(2),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec546 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(3),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[546]? = some (⟨18,(3),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec563 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(4),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[563]? = some (⟨18,(4),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec580 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(5),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[580]? = some (⟨18,(5),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec597 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(6),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[597]? = some (⟨18,(6),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec614 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(7),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[614]? = some (⟨18,(7),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec631 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(8),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[631]? = some (⟨18,(8),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec648 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(9),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[648]? = some (⟨18,(9),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec665 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(10),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[665]? = some (⟨18,(10),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec682 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(11),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[682]? = some (⟨18,(11),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec699 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(12),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[699]? = some (⟨18,(12),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec716 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(13),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[716]? = some (⟨18,(13),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec733 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(14),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[733]? = some (⟨18,(14),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec750 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(15),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[750]? = some (⟨18,(15),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec767 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(16),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[767]? = some (⟨18,(16),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec784 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(17),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[784]? = some (⟨18,(17),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec801 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(18),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[801]? = some (⟨18,(18),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec818 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(19),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[818]? = some (⟨18,(19),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec835 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(20),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[835]? = some (⟨18,(20),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec852 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(21),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[852]? = some (⟨18,(21),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec869 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(22),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[869]? = some (⟨18,(22),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec886 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(23),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[886]? = some (⟨18,(23),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec903 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 18 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨18,(24),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[903]? = some (⟨18,(24),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec921 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(0),[1,2,13,14],[190],209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[921]? = some (⟨20,(0),[1,2,13,14],[190],209⟩) from rfl))
private theorem rec932 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(1),[1,2,13,14],[190],210⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[932]? = some (⟨20,(1),[1,2,13,14],[190],210⟩) from rfl))
private theorem rec943 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(2),[1,2,13,14],[190],209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[943]? = some (⟨20,(2),[1,2,13,14],[190],209⟩) from rfl))
private theorem rec954 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(3),[1,2,13,14],[190],211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[954]? = some (⟨20,(3),[1,2,13,14],[190],211⟩) from rfl))
private theorem rec965 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(4),[1,2,13,14],[190],212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[965]? = some (⟨20,(4),[1,2,13,14],[190],212⟩) from rfl))
private theorem rec976 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(5),[1,2,13,14],[190],209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[976]? = some (⟨20,(5),[1,2,13,14],[190],209⟩) from rfl))
private theorem rec987 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(6),[1,2,13,14],[190],210⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[987]? = some (⟨20,(6),[1,2,13,14],[190],210⟩) from rfl))
private theorem rec998 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(7),[1,2,13,14],[190],209⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[998]? = some (⟨20,(7),[1,2,13,14],[190],209⟩) from rfl))
private theorem rec1009 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(8),[1,2,13,14],[190],211⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1009]? = some (⟨20,(8),[1,2,13,14],[190],211⟩) from rfl))
private theorem rec1020 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(9),[1,2,13,14],[190],212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1020]? = some (⟨20,(9),[1,2,13,14],[190],212⟩) from rfl))
private theorem rec1031 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(10),[1,2,13,14],[190],213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1031]? = some (⟨20,(10),[1,2,13,14],[190],213⟩) from rfl))
private theorem rec1042 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(11),[1,2,13,14],[190],213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1042]? = some (⟨20,(11),[1,2,13,14],[190],213⟩) from rfl))
private theorem rec1053 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(12),[1,2,13,14],[190],213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1053]? = some (⟨20,(12),[1,2,13,14],[190],213⟩) from rfl))
private theorem rec1064 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(13),[1,2,13,14],[190],213⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1064]? = some (⟨20,(13),[1,2,13,14],[190],213⟩) from rfl))
private theorem rec1075 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(14),[1,2,13,14],[190],212⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1075]? = some (⟨20,(14),[1,2,13,14],[190],212⟩) from rfl))
private theorem rec1086 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(15),[1,2,13,14],[190],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1086]? = some (⟨20,(15),[1,2,13,14],[190],214⟩) from rfl))
private theorem rec1097 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(16),[1,2,13,14],[190],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1097]? = some (⟨20,(16),[1,2,13,14],[190],214⟩) from rfl))
private theorem rec1108 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(17),[1,2,13,14],[190],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1108]? = some (⟨20,(17),[1,2,13,14],[190],214⟩) from rfl))
private theorem rec1119 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(18),[1,2,13,14],[190],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1119]? = some (⟨20,(18),[1,2,13,14],[190],214⟩) from rfl))
private theorem rec1130 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(19),[1,2,13,14],[190],214⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1130]? = some (⟨20,(19),[1,2,13,14],[190],214⟩) from rfl))
private theorem rec1141 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(20),[1,2,13,14],[190],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1141]? = some (⟨20,(20),[1,2,13,14],[190],215⟩) from rfl))
private theorem rec1152 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(21),[1,2,13,14],[190],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1152]? = some (⟨20,(21),[1,2,13,14],[190],215⟩) from rfl))
private theorem rec1163 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(22),[1,2,13,14],[190],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part0 (List.mem_of_getElem? (show section14DataRecords1Part1[1163]? = some (⟨20,(22),[1,2,13,14],[190],215⟩) from rfl))
private theorem rec1174 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(23),[1,2,13,14],[190],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[5]? = some (⟨20,(23),[1,2,13,14],[190],215⟩) from rfl))
private theorem rec1185 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 20 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨20,(24),[1,2,13,14],[190],215⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[16]? = some (⟨20,(24),[1,2,13,14],[190],215⟩) from rfl))
private theorem rec1195 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(0),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[26]? = some (⟨23,(0),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1202 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(1),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[33]? = some (⟨23,(1),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1209 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(2),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[40]? = some (⟨23,(2),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1216 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(3),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[47]? = some (⟨23,(3),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1223 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(4),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[54]? = some (⟨23,(4),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1230 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(5),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[61]? = some (⟨23,(5),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1237 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(6),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[68]? = some (⟨23,(6),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1244 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(7),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[75]? = some (⟨23,(7),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1251 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(8),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[82]? = some (⟨23,(8),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1258 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(9),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[89]? = some (⟨23,(9),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1265 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(10),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[96]? = some (⟨23,(10),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1272 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(11),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[103]? = some (⟨23,(11),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1279 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(12),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[110]? = some (⟨23,(12),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1286 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(13),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[117]? = some (⟨23,(13),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1293 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(14),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[124]? = some (⟨23,(14),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1300 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(15),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[131]? = some (⟨23,(15),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1307 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(16),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[138]? = some (⟨23,(16),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1314 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(17),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[145]? = some (⟨23,(17),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1321 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(18),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[152]? = some (⟨23,(18),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1328 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(19),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[159]? = some (⟨23,(19),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1335 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(20),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[166]? = some (⟨23,(20),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1342 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(21),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[173]? = some (⟨23,(21),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1349 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(22),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[180]? = some (⟨23,(22),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1356 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(23),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[187]? = some (⟨23,(23),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1363 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 23 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨23,(24),[1,2,13,14],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[194]? = some (⟨23,(24),[1,2,13,14],[147,190],2⟩) from rfl))
private theorem rec1373 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(0),[1,2,13,14],[190],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[204]? = some (⟨25,(0),[1,2,13,14],[190],189⟩) from rfl))
private theorem rec1394 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(1),[1,2,13,14],[190],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[225]? = some (⟨25,(1),[1,2,13,14],[190],216⟩) from rfl))
private theorem rec1418 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(2),[1,2,13,14],[190],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[249]? = some (⟨25,(2),[1,2,13,14],[190],217⟩) from rfl))
private theorem rec1442 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(3),[1,2,13,14],[190],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[273]? = some (⟨25,(3),[1,2,13,14],[190],218⟩) from rfl))
private theorem rec1466 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(4),[1,2,13,14],[190],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[297]? = some (⟨25,(4),[1,2,13,14],[190],219⟩) from rfl))
private theorem rec1490 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(5),[1,2,13,14],[190],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[321]? = some (⟨25,(5),[1,2,13,14],[190],189⟩) from rfl))
private theorem rec1511 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(6),[1,2,13,14],[190],216⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[342]? = some (⟨25,(6),[1,2,13,14],[190],216⟩) from rfl))
private theorem rec1535 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(7),[1,2,13,14],[190],217⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[366]? = some (⟨25,(7),[1,2,13,14],[190],217⟩) from rfl))
private theorem rec1559 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(8),[1,2,13,14],[190],218⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[390]? = some (⟨25,(8),[1,2,13,14],[190],218⟩) from rfl))
private theorem rec1583 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(9),[1,2,13,14],[190],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[414]? = some (⟨25,(9),[1,2,13,14],[190],219⟩) from rfl))
private theorem rec1607 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(10),[1,2,13,14],[190],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[438]? = some (⟨25,(10),[1,2,13,14],[190],194⟩) from rfl))
private theorem rec1628 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(11),[1,2,13,14],[190],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[459]? = some (⟨25,(11),[1,2,13,14],[190],220⟩) from rfl))
private theorem rec1652 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(12),[1,2,13,14],[190],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[483]? = some (⟨25,(12),[1,2,13,14],[190],220⟩) from rfl))
private theorem rec1676 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(13),[1,2,13,14],[190],220⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[507]? = some (⟨25,(13),[1,2,13,14],[190],220⟩) from rfl))
private theorem rec1700 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(14),[1,2,13,14],[190],219⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[531]? = some (⟨25,(14),[1,2,13,14],[190],219⟩) from rfl))
private theorem rec1724 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(15),[1,2,13,14],[190],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[555]? = some (⟨25,(15),[1,2,13,14],[190],196⟩) from rfl))
private theorem rec1745 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(16),[1,2,13,14],[190],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[576]? = some (⟨25,(16),[1,2,13,14],[190],221⟩) from rfl))
private theorem rec1769 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(17),[1,2,13,14],[190],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[600]? = some (⟨25,(17),[1,2,13,14],[190],221⟩) from rfl))
private theorem rec1793 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(18),[1,2,13,14],[190],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[624]? = some (⟨25,(18),[1,2,13,14],[190],221⟩) from rfl))
private theorem rec1817 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(19),[1,2,13,14],[190],221⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[648]? = some (⟨25,(19),[1,2,13,14],[190],221⟩) from rfl))
private theorem rec1841 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(20),[1,2,13,14],[190],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[672]? = some (⟨25,(20),[1,2,13,14],[190],198⟩) from rfl))
private theorem rec1862 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(21),[1,2,13,14],[190],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[693]? = some (⟨25,(21),[1,2,13,14],[190],222⟩) from rfl))
private theorem rec1886 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(22),[1,2,13,14],[190],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[717]? = some (⟨25,(22),[1,2,13,14],[190],222⟩) from rfl))
private theorem rec1910 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(23),[1,2,13,14],[190],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[741]? = some (⟨25,(23),[1,2,13,14],[190],222⟩) from rfl))
private theorem rec1934 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 25 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨25,(24),[1,2,13,14],[190],222⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[765]? = some (⟨25,(24),[1,2,13,14],[190],222⟩) from rfl))
private theorem rec1956 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(0),[1,2],[190],223⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[787]? = some (⟨28,(0),[1,2],[190],223⟩) from rfl))
private theorem rec1972 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(1),[1,2],[190],223⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[803]? = some (⟨28,(1),[1,2],[190],223⟩) from rfl))
private theorem rec1988 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(2),[1,2],[190],223⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[819]? = some (⟨28,(2),[1,2],[190],223⟩) from rfl))
private theorem rec2004 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(3),[1,2],[190],223⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[835]? = some (⟨28,(3),[1,2],[190],223⟩) from rfl))
private theorem rec2020 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(4),[1,2],[190],223⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[851]? = some (⟨28,(4),[1,2],[190],223⟩) from rfl))
private theorem rec2036 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(5),[1,2],[190],224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[867]? = some (⟨28,(5),[1,2],[190],224⟩) from rfl))
private theorem rec2052 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(6),[1,2],[190],224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[883]? = some (⟨28,(6),[1,2],[190],224⟩) from rfl))
private theorem rec2068 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(7),[1,2],[190],224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[899]? = some (⟨28,(7),[1,2],[190],224⟩) from rfl))
private theorem rec2084 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(8),[1,2],[190],224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[915]? = some (⟨28,(8),[1,2],[190],224⟩) from rfl))
private theorem rec2100 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(9),[1,2],[190],224⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[931]? = some (⟨28,(9),[1,2],[190],224⟩) from rfl))
private theorem rec2116 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(10),[1,2],[190],225⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[947]? = some (⟨28,(10),[1,2],[190],225⟩) from rfl))
private theorem rec2132 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(11),[1,2],[190],226⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[963]? = some (⟨28,(11),[1,2],[190],226⟩) from rfl))
private theorem rec2148 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(12),[1,2],[190],227⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[979]? = some (⟨28,(12),[1,2],[190],227⟩) from rfl))
private theorem rec2164 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(13),[1,2],[190],226⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[995]? = some (⟨28,(13),[1,2],[190],226⟩) from rfl))
private theorem rec2180 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(14),[1,2],[190],228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1011]? = some (⟨28,(14),[1,2],[190],228⟩) from rfl))
private theorem rec2196 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(15),[1,2],[190],225⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1027]? = some (⟨28,(15),[1,2],[190],225⟩) from rfl))
private theorem rec2212 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(16),[1,2],[190],229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1043]? = some (⟨28,(16),[1,2],[190],229⟩) from rfl))
private theorem rec2228 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(17),[1,2],[190],229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1059]? = some (⟨28,(17),[1,2],[190],229⟩) from rfl))
private theorem rec2244 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(18),[1,2],[190],229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1075]? = some (⟨28,(18),[1,2],[190],229⟩) from rfl))
private theorem rec2260 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(19),[1,2],[190],229⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1091]? = some (⟨28,(19),[1,2],[190],229⟩) from rfl))
private theorem rec2276 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(20),[1,2],[190],225⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1107]? = some (⟨28,(20),[1,2],[190],225⟩) from rfl))
private theorem rec2292 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(21),[1,2],[190],226⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1123]? = some (⟨28,(21),[1,2],[190],226⟩) from rfl))
private theorem rec2308 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(22),[1,2],[190],227⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1139]? = some (⟨28,(22),[1,2],[190],227⟩) from rfl))
private theorem rec2324 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(23),[1,2],[190],226⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1155]? = some (⟨28,(23),[1,2],[190],226⟩) from rfl))
private theorem rec2340 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 28 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨28,(24),[1,2],[190],228⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1171]? = some (⟨28,(24),[1,2],[190],228⟩) from rfl))
private theorem rec2357 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(0),[1,2],[190],152⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1188]? = some (⟨30,(0),[1,2],[190],152⟩) from rfl))
private theorem rec2372 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(1),[1,2],[190],153⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1203]? = some (⟨30,(1),[1,2],[190],153⟩) from rfl))
private theorem rec2386 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(2),[1,2],[190],200⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1217]? = some (⟨30,(2),[1,2],[190],200⟩) from rfl))
private theorem rec2409 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(3),[1,2],[190],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1240]? = some (⟨30,(3),[1,2],[190],230⟩) from rfl))
private theorem rec2433 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(4),[1,2],[190],231⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part1 (List.mem_of_getElem? (show section14DataRecords1Part2[1264]? = some (⟨30,(4),[1,2],[190],231⟩) from rfl))
private theorem rec2457 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(5),[1,2],[190],230⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[14]? = some (⟨30,(5),[1,2],[190],230⟩) from rfl))
private theorem rec2481 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(6),[1,2],[190],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[38]? = some (⟨30,(6),[1,2],[190],232⟩) from rfl))
private theorem rec2505 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(7),[1,2],[190],232⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[62]? = some (⟨30,(7),[1,2],[190],232⟩) from rfl))
private theorem rec2529 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(8),[1,2],[190],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[86]? = some (⟨30,(8),[1,2],[190],233⟩) from rfl))
private theorem rec2553 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 30 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨30,(9),[1,2],[190],233⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[110]? = some (⟨30,(9),[1,2],[190],233⟩) from rfl))
private theorem rec2578 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(0),[2],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[135]? = some (⟨33,(0),[2],[190],2⟩) from rfl))
private theorem rec2588 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([130, 190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(1),[2],[130,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[145]? = some (⟨33,(1),[2],[130,190],2⟩) from rfl))
private theorem rec2604 (si parent : ℕ) (hs : si ∈ ([2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(2),[2,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[161]? = some (⟨33,(2),[2,13,14],[190],2⟩) from rfl))
private theorem rec2609 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(3),[1,2,14],[190],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[166]? = some (⟨33,(3),[1,2,14],[190],234⟩) from rfl))
private theorem rec2627 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(4),[2],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[184]? = some (⟨33,(4),[2],[190],2⟩) from rfl))
private theorem rec2639 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([130, 190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(5),[2],[130,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[196]? = some (⟨33,(5),[2],[130,190],2⟩) from rfl))
private theorem rec2653 (si parent : ℕ) (hs : si ∈ ([2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(6),[2,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[210]? = some (⟨33,(6),[2,13,14],[190],2⟩) from rfl))
private theorem rec2656 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(7),[1,2,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[213]? = some (⟨33,(7),[1,2,13,14],[190],2⟩) from rfl))
private theorem rec2669 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(8),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[226]? = some (⟨33,(8),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec2679 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(9),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[236]? = some (⟨33,(9),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec2690 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(10),[1,2,13,14],[190],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[247]? = some (⟨33,(10),[1,2,13,14],[190],29⟩) from rfl))
private theorem rec2700 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(11),[1,2,13,14],[190],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[257]? = some (⟨33,(11),[1,2,13,14],[190],234⟩) from rfl))
private theorem rec2709 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(12),[1,2,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[266]? = some (⟨33,(12),[1,2,14],[190],3⟩) from rfl))
private theorem rec2721 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(13),[1,2,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[278]? = some (⟨33,(13),[1,2,14],[190],3⟩) from rfl))
private theorem rec2733 (si parent : ℕ) (hs : si ∈ ([1, 2, 13] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(14),[1,2,13],[190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[290]? = some (⟨33,(14),[1,2,13],[190],99⟩) from rfl))
private theorem rec2744 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 33 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨33,(15),[1,2,13,14],[190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[301]? = some (⟨33,(15),[1,2,13,14],[190],99⟩) from rfl))
private theorem rec2752 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(0),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[309]? = some (⟨35,(0),[1,2],[147,190],2⟩) from rfl))
private theorem rec2757 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(1),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[314]? = some (⟨35,(1),[1,2],[147,190],2⟩) from rfl))
private theorem rec2764 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(2),[1,2],[190],235⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[321]? = some (⟨35,(2),[1,2],[190],235⟩) from rfl))
private theorem rec2780 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(3),[1,2],[190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[337]? = some (⟨35,(3),[1,2],[190],101⟩) from rfl))
private theorem rec2789 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(4),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[346]? = some (⟨35,(4),[1,2],[147,190],2⟩) from rfl))
private theorem rec2794 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(5),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[351]? = some (⟨35,(5),[1,2],[147,190],2⟩) from rfl))
private theorem rec2801 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(6),[1,2],[190],236⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[358]? = some (⟨35,(6),[1,2],[190],236⟩) from rfl))
private theorem rec2817 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(7),[1,2],[190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[374]? = some (⟨35,(7),[1,2],[190],101⟩) from rfl))
private theorem rec2826 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(8),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[383]? = some (⟨35,(8),[1,2],[147,190],2⟩) from rfl))
private theorem rec2831 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(9),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[388]? = some (⟨35,(9),[1,2],[147,190],2⟩) from rfl))
private theorem rec2838 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(10),[1,2],[190],237⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[395]? = some (⟨35,(10),[1,2],[190],237⟩) from rfl))
private theorem rec2854 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(11),[1,2],[190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[411]? = some (⟨35,(11),[1,2],[190],101⟩) from rfl))
private theorem rec2863 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(12),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[420]? = some (⟨35,(12),[1,2],[147,190],2⟩) from rfl))
private theorem rec2868 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(13),[1,2],[147,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[425]? = some (⟨35,(13),[1,2],[147,190],2⟩) from rfl))
private theorem rec2875 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(14),[1,2],[190],238⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[432]? = some (⟨35,(14),[1,2],[190],238⟩) from rfl))
private theorem rec2891 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 35 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨35,(15),[1,2],[190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[448]? = some (⟨35,(15),[1,2],[190],101⟩) from rfl))
private theorem rec2902 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(5),[1,2,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[459]? = some (⟨36,(5),[1,2,14],[190],3⟩) from rfl))
private theorem rec2912 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(7),[1,2,14],[147,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[469]? = some (⟨36,(7),[1,2,14],[147,190],3⟩) from rfl))
private theorem rec2922 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(8),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[479]? = some (⟨36,(8),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec2934 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(9),[1,2],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[491]? = some (⟨36,(9),[1,2],[190],3⟩) from rfl))
private theorem rec2952 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(15),[1,2,13,14],[147,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[509]? = some (⟨36,(15),[1,2,13,14],[147,190],3⟩) from rfl))
private theorem rec2959 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(16),[1,2,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[516]? = some (⟨36,(16),[1,2,13,14],[190],3⟩) from rfl))
private theorem rec2973 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(17),[1,2,13,14],[190],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[530]? = some (⟨36,(17),[1,2,13,14],[190],48⟩) from rfl))
private theorem rec2983 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 36 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨36,(19),[1,2,13,14],[190],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[540]? = some (⟨36,(19),[1,2,13,14],[190],143⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 1).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 176).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 2).plans.drop 1).take 1 = [⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(17,⟨([1],[]),true,([1],[]),false,false,[]⟩),(18,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(19,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(22,⟨([2],[]),true,([2],[]),false,false,[]⟩),(23,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(24,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(27,⟨([3],[]),true,([3],[]),false,false,[]⟩),(28,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(29,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(32,⟨([1],[]),true,([2],[]),false,false,[]⟩),(33,⟨([2],[]),true,([1],[]),false,false,[]⟩),(34,⟨([2],[]),true,([3],[]),false,false,[]⟩),(35,⟨([3],[]),true,([2],[]),false,false,[]⟩),(36,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 176).take 16 = [⟨1,176,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,177,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,178,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,179,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,180,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,181,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,182,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,183,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,184,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,185,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,186,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,187,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,188,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,189,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,190,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,191,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec388 2 176 (by decide) (by decide)
  · left
    exact rec388 2 177 (by decide) (by decide)
  · left
    exact rec362 2 178 (by decide) (by decide)
  · left
    exact rec362 2 179 (by decide) (by decide)
  · left
    exact rec388 2 180 (by decide) (by decide)
  · left
    exact rec388 2 181 (by decide) (by decide)
  · left
    exact rec362 2 182 (by decide) (by decide)
  · left
    exact rec362 2 183 (by decide) (by decide)
  · left
    exact rec361 2 184 (by decide) (by decide)
  · left
    exact rec361 2 185 (by decide) (by decide)
  · left
    exact rec380 2 186 (by decide) (by decide)
  · left
    exact rec378 2 187 (by decide) (by decide)
  · left
    exact rec361 2 188 (by decide) (by decide)
  · left
    exact rec361 2 189 (by decide) (by decide)
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
        exact rec495 2 190 (by decide) (by decide)
      · right
        exact rec512 2 190 (by decide) (by decide)
      · right
        exact rec529 2 190 (by decide) (by decide)
      · right
        exact rec546 2 190 (by decide) (by decide)
      · right
        exact rec563 2 190 (by decide) (by decide)
      · right
        exact rec580 2 190 (by decide) (by decide)
      · right
        exact rec597 2 190 (by decide) (by decide)
      · right
        exact rec614 2 190 (by decide) (by decide)
      · right
        exact rec631 2 190 (by decide) (by decide)
      · right
        exact rec648 2 190 (by decide) (by decide)
      · right
        exact rec665 2 190 (by decide) (by decide)
      · right
        exact rec682 2 190 (by decide) (by decide)
      · right
        exact rec699 2 190 (by decide) (by decide)
      · right
        exact rec716 2 190 (by decide) (by decide)
      · right
        exact rec733 2 190 (by decide) (by decide)
      · right
        exact rec750 2 190 (by decide) (by decide)
      · right
        exact rec767 2 190 (by decide) (by decide)
      · right
        exact rec784 2 190 (by decide) (by decide)
      · right
        exact rec801 2 190 (by decide) (by decide)
      · right
        exact rec818 2 190 (by decide) (by decide)
      · right
        exact rec835 2 190 (by decide) (by decide)
      · right
        exact rec852 2 190 (by decide) (by decide)
      · right
        exact rec869 2 190 (by decide) (by decide)
      · right
        exact rec886 2 190 (by decide) (by decide)
      · right
        exact rec903 2 190 (by decide) (by decide)
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
        exact rec921 2 190 (by decide) (by decide)
      · right
        exact rec932 2 190 (by decide) (by decide)
      · right
        exact rec943 2 190 (by decide) (by decide)
      · right
        exact rec954 2 190 (by decide) (by decide)
      · right
        exact rec965 2 190 (by decide) (by decide)
      · right
        exact rec976 2 190 (by decide) (by decide)
      · right
        exact rec987 2 190 (by decide) (by decide)
      · right
        exact rec998 2 190 (by decide) (by decide)
      · right
        exact rec1009 2 190 (by decide) (by decide)
      · right
        exact rec1020 2 190 (by decide) (by decide)
      · right
        exact rec1031 2 190 (by decide) (by decide)
      · right
        exact rec1042 2 190 (by decide) (by decide)
      · right
        exact rec1053 2 190 (by decide) (by decide)
      · right
        exact rec1064 2 190 (by decide) (by decide)
      · right
        exact rec1075 2 190 (by decide) (by decide)
      · right
        exact rec1086 2 190 (by decide) (by decide)
      · right
        exact rec1097 2 190 (by decide) (by decide)
      · right
        exact rec1108 2 190 (by decide) (by decide)
      · right
        exact rec1119 2 190 (by decide) (by decide)
      · right
        exact rec1130 2 190 (by decide) (by decide)
      · right
        exact rec1141 2 190 (by decide) (by decide)
      · right
        exact rec1152 2 190 (by decide) (by decide)
      · right
        exact rec1163 2 190 (by decide) (by decide)
      · right
        exact rec1174 2 190 (by decide) (by decide)
      · right
        exact rec1185 2 190 (by decide) (by decide)
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
        exact rec1195 2 190 (by decide) (by decide)
      · right
        exact rec1202 2 190 (by decide) (by decide)
      · right
        exact rec1209 2 190 (by decide) (by decide)
      · right
        exact rec1216 2 190 (by decide) (by decide)
      · right
        exact rec1223 2 190 (by decide) (by decide)
      · right
        exact rec1230 2 190 (by decide) (by decide)
      · right
        exact rec1237 2 190 (by decide) (by decide)
      · right
        exact rec1244 2 190 (by decide) (by decide)
      · right
        exact rec1251 2 190 (by decide) (by decide)
      · right
        exact rec1258 2 190 (by decide) (by decide)
      · right
        exact rec1265 2 190 (by decide) (by decide)
      · right
        exact rec1272 2 190 (by decide) (by decide)
      · right
        exact rec1279 2 190 (by decide) (by decide)
      · right
        exact rec1286 2 190 (by decide) (by decide)
      · right
        exact rec1293 2 190 (by decide) (by decide)
      · right
        exact rec1300 2 190 (by decide) (by decide)
      · right
        exact rec1307 2 190 (by decide) (by decide)
      · right
        exact rec1314 2 190 (by decide) (by decide)
      · right
        exact rec1321 2 190 (by decide) (by decide)
      · right
        exact rec1328 2 190 (by decide) (by decide)
      · right
        exact rec1335 2 190 (by decide) (by decide)
      · right
        exact rec1342 2 190 (by decide) (by decide)
      · right
        exact rec1349 2 190 (by decide) (by decide)
      · right
        exact rec1356 2 190 (by decide) (by decide)
      · right
        exact rec1363 2 190 (by decide) (by decide)
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
        exact rec1373 2 190 (by decide) (by decide)
      · right
        exact rec1394 2 190 (by decide) (by decide)
      · right
        exact rec1418 2 190 (by decide) (by decide)
      · right
        exact rec1442 2 190 (by decide) (by decide)
      · right
        exact rec1466 2 190 (by decide) (by decide)
      · right
        exact rec1490 2 190 (by decide) (by decide)
      · right
        exact rec1511 2 190 (by decide) (by decide)
      · right
        exact rec1535 2 190 (by decide) (by decide)
      · right
        exact rec1559 2 190 (by decide) (by decide)
      · right
        exact rec1583 2 190 (by decide) (by decide)
      · right
        exact rec1607 2 190 (by decide) (by decide)
      · right
        exact rec1628 2 190 (by decide) (by decide)
      · right
        exact rec1652 2 190 (by decide) (by decide)
      · right
        exact rec1676 2 190 (by decide) (by decide)
      · right
        exact rec1700 2 190 (by decide) (by decide)
      · right
        exact rec1724 2 190 (by decide) (by decide)
      · right
        exact rec1745 2 190 (by decide) (by decide)
      · right
        exact rec1769 2 190 (by decide) (by decide)
      · right
        exact rec1793 2 190 (by decide) (by decide)
      · right
        exact rec1817 2 190 (by decide) (by decide)
      · right
        exact rec1841 2 190 (by decide) (by decide)
      · right
        exact rec1862 2 190 (by decide) (by decide)
      · right
        exact rec1886 2 190 (by decide) (by decide)
      · right
        exact rec1910 2 190 (by decide) (by decide)
      · right
        exact rec1934 2 190 (by decide) (by decide)
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
        exact rec1956 2 190 (by decide) (by decide)
      · right
        exact rec1972 2 190 (by decide) (by decide)
      · right
        exact rec1988 2 190 (by decide) (by decide)
      · right
        exact rec2004 2 190 (by decide) (by decide)
      · right
        exact rec2020 2 190 (by decide) (by decide)
      · right
        exact rec2036 2 190 (by decide) (by decide)
      · right
        exact rec2052 2 190 (by decide) (by decide)
      · right
        exact rec2068 2 190 (by decide) (by decide)
      · right
        exact rec2084 2 190 (by decide) (by decide)
      · right
        exact rec2100 2 190 (by decide) (by decide)
      · right
        exact rec2116 2 190 (by decide) (by decide)
      · right
        exact rec2132 2 190 (by decide) (by decide)
      · right
        exact rec2148 2 190 (by decide) (by decide)
      · right
        exact rec2164 2 190 (by decide) (by decide)
      · right
        exact rec2180 2 190 (by decide) (by decide)
      · right
        exact rec2196 2 190 (by decide) (by decide)
      · right
        exact rec2212 2 190 (by decide) (by decide)
      · right
        exact rec2228 2 190 (by decide) (by decide)
      · right
        exact rec2244 2 190 (by decide) (by decide)
      · right
        exact rec2260 2 190 (by decide) (by decide)
      · right
        exact rec2276 2 190 (by decide) (by decide)
      · right
        exact rec2292 2 190 (by decide) (by decide)
      · right
        exact rec2308 2 190 (by decide) (by decide)
      · right
        exact rec2324 2 190 (by decide) (by decide)
      · right
        exact rec2340 2 190 (by decide) (by decide)
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
        exact rec2357 2 190 (by decide) (by decide)
      · right
        exact rec2372 2 190 (by decide) (by decide)
      · right
        exact rec2386 2 190 (by decide) (by decide)
      · right
        exact rec2409 2 190 (by decide) (by decide)
      · right
        exact rec2433 2 190 (by decide) (by decide)
      · right
        exact rec2457 2 190 (by decide) (by decide)
      · right
        exact rec2481 2 190 (by decide) (by decide)
      · right
        exact rec2505 2 190 (by decide) (by decide)
      · right
        exact rec2529 2 190 (by decide) (by decide)
      · right
        exact rec2553 2 190 (by decide) (by decide)
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
        exact rec2578 2 190 (by decide) (by decide)
      · right
        exact rec2588 2 190 (by decide) (by decide)
      · right
        exact rec2604 2 190 (by decide) (by decide)
      · right
        exact rec2609 2 190 (by decide) (by decide)
      · right
        exact rec2627 2 190 (by decide) (by decide)
      · right
        exact rec2639 2 190 (by decide) (by decide)
      · right
        exact rec2653 2 190 (by decide) (by decide)
      · right
        exact rec2656 2 190 (by decide) (by decide)
      · right
        exact rec2669 2 190 (by decide) (by decide)
      · right
        exact rec2679 2 190 (by decide) (by decide)
      · right
        exact rec2690 2 190 (by decide) (by decide)
      · right
        exact rec2700 2 190 (by decide) (by decide)
      · right
        exact rec2709 2 190 (by decide) (by decide)
      · right
        exact rec2721 2 190 (by decide) (by decide)
      · right
        exact rec2733 2 190 (by decide) (by decide)
      · right
        exact rec2744 2 190 (by decide) (by decide)
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
        exact rec2752 2 190 (by decide) (by decide)
      · right
        exact rec2757 2 190 (by decide) (by decide)
      · right
        exact rec2764 2 190 (by decide) (by decide)
      · right
        exact rec2780 2 190 (by decide) (by decide)
      · right
        exact rec2789 2 190 (by decide) (by decide)
      · right
        exact rec2794 2 190 (by decide) (by decide)
      · right
        exact rec2801 2 190 (by decide) (by decide)
      · right
        exact rec2817 2 190 (by decide) (by decide)
      · right
        exact rec2826 2 190 (by decide) (by decide)
      · right
        exact rec2831 2 190 (by decide) (by decide)
      · right
        exact rec2838 2 190 (by decide) (by decide)
      · right
        exact rec2854 2 190 (by decide) (by decide)
      · right
        exact rec2863 2 190 (by decide) (by decide)
      · right
        exact rec2868 2 190 (by decide) (by decide)
      · right
        exact rec2875 2 190 (by decide) (by decide)
      · right
        exact rec2891 2 190 (by decide) (by decide)
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
        exact rec2902 2 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2912 2 190 (by decide) (by decide)
      · right
        exact rec2922 2 190 (by decide) (by decide)
      · right
        exact rec2934 2 190 (by decide) (by decide)
      · left
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
        exact rec2952 2 190 (by decide) (by decide)
      · right
        exact rec2959 2 190 (by decide) (by decide)
      · right
        exact rec2973 2 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec2983 2 190 (by decide) (by decide)
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
    exact rec381 2 191 (by decide) (by decide)
end Section14Coverage_2_1_p176_192

#print axioms solution
