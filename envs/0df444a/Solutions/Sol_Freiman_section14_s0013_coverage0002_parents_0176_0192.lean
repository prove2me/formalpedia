-- Prove2me | solution 1 for Freiman.section14_s0013_coverage0002_parents_0176_0192
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T10:14:26.395636+00:00
-- url     : https://prove2.me/submissions/114c9533-6c43-45a6-adff-e6a909356cf0

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
namespace Section14Coverage_13_2_p176_192
private theorem rec2996 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[553]? = some (⟨38,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec2997 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[554]? = some (⟨38,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec3004 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([171, 187] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,13,14],[171,187],206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[561]? = some (⟨38,(-1),[1,2,5,6,13,14],[171,187],206⟩) from rfl))
private theorem rec3013 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 191] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,13,14],[147,151,191],251⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[570]? = some (⟨38,(-1),[1,2,5,6,13,14],[147,151,191],251⟩) from rfl))
private theorem rec3085 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[642]? = some (⟨38,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) from rfl))
private theorem rec3086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(0),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[643]? = some (⟨40,(0),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3087 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(0),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[644]? = some (⟨40,(0),[1,5,13],[186],3⟩) from rfl))
private theorem rec3091 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(1),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[648]? = some (⟨40,(1),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3092 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(1),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[649]? = some (⟨40,(1),[1,5,13],[186],3⟩) from rfl))
private theorem rec3096 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(2),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[653]? = some (⟨40,(2),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3097 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(2),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[654]? = some (⟨40,(2),[1,5,13],[186],3⟩) from rfl))
private theorem rec3101 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(3),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[658]? = some (⟨40,(3),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3102 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(3),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[659]? = some (⟨40,(3),[1,5,13],[186],3⟩) from rfl))
private theorem rec3106 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(4),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[663]? = some (⟨40,(4),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3107 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(4),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[664]? = some (⟨40,(4),[1,5,13],[186],3⟩) from rfl))
private theorem rec3111 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(5),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[668]? = some (⟨40,(5),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3112 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(5),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[669]? = some (⟨40,(5),[1,5,13],[186],3⟩) from rfl))
private theorem rec3116 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(6),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[673]? = some (⟨40,(6),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3117 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(6),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[674]? = some (⟨40,(6),[1,5,13],[186],3⟩) from rfl))
private theorem rec3121 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(7),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[678]? = some (⟨40,(7),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3122 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(7),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[679]? = some (⟨40,(7),[1,5,13],[186],3⟩) from rfl))
private theorem rec3126 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(8),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[683]? = some (⟨40,(8),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3127 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(8),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[684]? = some (⟨40,(8),[1,5,13],[186],3⟩) from rfl))
private theorem rec3131 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(9),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[688]? = some (⟨40,(9),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3132 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(9),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[689]? = some (⟨40,(9),[1,5,13],[186],3⟩) from rfl))
private theorem rec3136 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(10),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[693]? = some (⟨40,(10),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3137 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(10),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[694]? = some (⟨40,(10),[1,5,13],[186],3⟩) from rfl))
private theorem rec3141 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(11),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[698]? = some (⟨40,(11),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3142 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(11),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[699]? = some (⟨40,(11),[1,5,13],[186],3⟩) from rfl))
private theorem rec3146 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(12),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[703]? = some (⟨40,(12),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3147 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(12),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[704]? = some (⟨40,(12),[1,5,13],[186],3⟩) from rfl))
private theorem rec3151 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(13),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[708]? = some (⟨40,(13),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3152 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(13),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[709]? = some (⟨40,(13),[1,5,13],[186],3⟩) from rfl))
private theorem rec3156 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(14),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[713]? = some (⟨40,(14),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3157 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(14),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[714]? = some (⟨40,(14),[1,5,13],[186],3⟩) from rfl))
private theorem rec3161 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(15),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[718]? = some (⟨40,(15),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3162 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(15),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[719]? = some (⟨40,(15),[1,5,13],[186],3⟩) from rfl))
private theorem rec3166 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(16),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[723]? = some (⟨40,(16),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3167 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(16),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[724]? = some (⟨40,(16),[1,5,13],[186],3⟩) from rfl))
private theorem rec3171 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(17),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[728]? = some (⟨40,(17),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3172 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(17),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[729]? = some (⟨40,(17),[1,5,13],[186],3⟩) from rfl))
private theorem rec3176 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(18),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[733]? = some (⟨40,(18),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3177 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(18),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[734]? = some (⟨40,(18),[1,5,13],[186],3⟩) from rfl))
private theorem rec3181 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(19),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[738]? = some (⟨40,(19),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3182 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(19),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[739]? = some (⟨40,(19),[1,5,13],[186],3⟩) from rfl))
private theorem rec3186 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(20),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[743]? = some (⟨40,(20),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3187 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(20),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[744]? = some (⟨40,(20),[1,5,13],[186],3⟩) from rfl))
private theorem rec3191 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(21),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[748]? = some (⟨40,(21),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3192 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(21),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[749]? = some (⟨40,(21),[1,5,13],[186],3⟩) from rfl))
private theorem rec3196 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(22),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[753]? = some (⟨40,(22),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3197 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(22),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[754]? = some (⟨40,(22),[1,5,13],[186],3⟩) from rfl))
private theorem rec3201 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(23),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[758]? = some (⟨40,(23),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3202 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(23),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[759]? = some (⟨40,(23),[1,5,13],[186],3⟩) from rfl))
private theorem rec3206 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(24),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[763]? = some (⟨40,(24),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3207 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 40 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(24),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[764]? = some (⟨40,(24),[1,5,13],[186],3⟩) from rfl))
private theorem rec3213 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[1,2,5,6,13,14],[190],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[770]? = some (⟨42,(0),[1,2,5,6,13,14],[190],312⟩) from rfl))
private theorem rec3214 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[1,5,13],[186],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[771]? = some (⟨42,(0),[1,5,13],[186],312⟩) from rfl))
private theorem rec3224 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[1,2,5,6,13,14],[190],313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[781]? = some (⟨42,(1),[1,2,5,6,13,14],[190],313⟩) from rfl))
private theorem rec3225 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[1,5,13],[186],313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[782]? = some (⟨42,(1),[1,5,13],[186],313⟩) from rfl))
private theorem rec3234 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[1,2,5,6,13,14],[190],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[791]? = some (⟨42,(2),[1,2,5,6,13,14],[190],312⟩) from rfl))
private theorem rec3235 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[1,5,13],[186],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[792]? = some (⟨42,(2),[1,5,13],[186],312⟩) from rfl))
private theorem rec3244 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[1,2,5,6,13,14],[190],314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[801]? = some (⟨42,(3),[1,2,5,6,13,14],[190],314⟩) from rfl))
private theorem rec3245 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[1,5,13],[186],314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[802]? = some (⟨42,(3),[1,5,13],[186],314⟩) from rfl))
private theorem rec3254 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[1,2,5,6,13,14],[190],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[811]? = some (⟨42,(4),[1,2,5,6,13,14],[190],315⟩) from rfl))
private theorem rec3255 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[1,5,13],[186],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[812]? = some (⟨42,(4),[1,5,13],[186],315⟩) from rfl))
private theorem rec3264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[1,2,5,6,13,14],[190],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[821]? = some (⟨42,(5),[1,2,5,6,13,14],[190],312⟩) from rfl))
private theorem rec3265 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[1,5,13],[186],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[822]? = some (⟨42,(5),[1,5,13],[186],312⟩) from rfl))
private theorem rec3275 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[1,2,5,6,13,14],[190],313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[832]? = some (⟨42,(6),[1,2,5,6,13,14],[190],313⟩) from rfl))
private theorem rec3276 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[1,5,13],[186],313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[833]? = some (⟨42,(6),[1,5,13],[186],313⟩) from rfl))
private theorem rec3285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[1,2,5,6,13,14],[190],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[842]? = some (⟨42,(7),[1,2,5,6,13,14],[190],312⟩) from rfl))
private theorem rec3286 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[1,5,13],[186],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[843]? = some (⟨42,(7),[1,5,13],[186],312⟩) from rfl))
private theorem rec3295 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[1,2,5,6,13,14],[190],314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[852]? = some (⟨42,(8),[1,2,5,6,13,14],[190],314⟩) from rfl))
private theorem rec3296 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[1,5,13],[186],314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[853]? = some (⟨42,(8),[1,5,13],[186],314⟩) from rfl))
private theorem rec3305 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[1,2,5,6,13,14],[190],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[862]? = some (⟨42,(9),[1,2,5,6,13,14],[190],315⟩) from rfl))
private theorem rec3306 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[1,5,13],[186],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[863]? = some (⟨42,(9),[1,5,13],[186],315⟩) from rfl))
private theorem rec3315 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[1,2,5,6,13,14],[190],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[872]? = some (⟨42,(10),[1,2,5,6,13,14],[190],316⟩) from rfl))
private theorem rec3316 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[1,5,13],[186],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[873]? = some (⟨42,(10),[1,5,13],[186],316⟩) from rfl))
private theorem rec3326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[1,2,5,6,13,14],[190],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[883]? = some (⟨42,(11),[1,2,5,6,13,14],[190],316⟩) from rfl))
private theorem rec3327 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[1,5,13],[186],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[884]? = some (⟨42,(11),[1,5,13],[186],316⟩) from rfl))
private theorem rec3336 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[1,2,5,6,13,14],[190],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[893]? = some (⟨42,(12),[1,2,5,6,13,14],[190],316⟩) from rfl))
private theorem rec3337 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[1,5,13],[186],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[894]? = some (⟨42,(12),[1,5,13],[186],316⟩) from rfl))
private theorem rec3346 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[1,2,5,6,13,14],[190],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[903]? = some (⟨42,(13),[1,2,5,6,13,14],[190],316⟩) from rfl))
private theorem rec3347 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[1,5,13],[186],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[904]? = some (⟨42,(13),[1,5,13],[186],316⟩) from rfl))
private theorem rec3356 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[1,2,5,6,13,14],[190],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[913]? = some (⟨42,(14),[1,2,5,6,13,14],[190],315⟩) from rfl))
private theorem rec3357 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[1,5,13],[186],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[914]? = some (⟨42,(14),[1,5,13],[186],315⟩) from rfl))
private theorem rec3366 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[923]? = some (⟨42,(15),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3367 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[1,5,13],[186],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[924]? = some (⟨42,(15),[1,5,13],[186],317⟩) from rfl))
private theorem rec3377 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[934]? = some (⟨42,(16),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3378 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[1,5,13],[186],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[935]? = some (⟨42,(16),[1,5,13],[186],317⟩) from rfl))
private theorem rec3387 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[944]? = some (⟨42,(17),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3388 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[1,5,13],[186],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[945]? = some (⟨42,(17),[1,5,13],[186],317⟩) from rfl))
private theorem rec3397 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[954]? = some (⟨42,(18),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3398 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[1,5,13],[186],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[955]? = some (⟨42,(18),[1,5,13],[186],317⟩) from rfl))
private theorem rec3407 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[964]? = some (⟨42,(19),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3408 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[1,5,13],[186],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[965]? = some (⟨42,(19),[1,5,13],[186],317⟩) from rfl))
private theorem rec3417 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[974]? = some (⟨42,(20),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3418 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[1,5,13],[186],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[975]? = some (⟨42,(20),[1,5,13],[186],318⟩) from rfl))
private theorem rec3428 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[985]? = some (⟨42,(21),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3429 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[1,5,13],[186],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[986]? = some (⟨42,(21),[1,5,13],[186],318⟩) from rfl))
private theorem rec3438 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[995]? = some (⟨42,(22),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3439 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[1,5,13],[186],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[996]? = some (⟨42,(22),[1,5,13],[186],318⟩) from rfl))
private theorem rec3448 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1005]? = some (⟨42,(23),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3449 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[1,5,13],[186],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1006]? = some (⟨42,(23),[1,5,13],[186],318⟩) from rfl))
private theorem rec3458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1015]? = some (⟨42,(24),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3459 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[1,5,13],[186],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1016]? = some (⟨42,(24),[1,5,13],[186],318⟩) from rfl))
private theorem rec3466 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(0),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1023]? = some (⟨45,(0),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3467 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(0),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1024]? = some (⟨45,(0),[1,5,13],[186],2⟩) from rfl))
private theorem rec3470 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(1),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1027]? = some (⟨45,(1),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3471 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(1),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1028]? = some (⟨45,(1),[1,5,13],[186],2⟩) from rfl))
private theorem rec3474 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(2),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1031]? = some (⟨45,(2),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3475 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(2),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1032]? = some (⟨45,(2),[1,5,13],[186],2⟩) from rfl))
private theorem rec3478 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(3),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1035]? = some (⟨45,(3),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3479 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(3),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1036]? = some (⟨45,(3),[1,5,13],[186],2⟩) from rfl))
private theorem rec3482 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(4),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1039]? = some (⟨45,(4),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3483 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(4),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1040]? = some (⟨45,(4),[1,5,13],[186],2⟩) from rfl))
private theorem rec3486 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(5),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1043]? = some (⟨45,(5),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3487 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(5),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1044]? = some (⟨45,(5),[1,5,13],[186],2⟩) from rfl))
private theorem rec3490 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(6),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1047]? = some (⟨45,(6),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3491 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(6),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1048]? = some (⟨45,(6),[1,5,13],[186],2⟩) from rfl))
private theorem rec3494 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(7),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1051]? = some (⟨45,(7),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3495 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(7),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1052]? = some (⟨45,(7),[1,5,13],[186],2⟩) from rfl))
private theorem rec3498 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(8),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1055]? = some (⟨45,(8),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3499 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(8),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1056]? = some (⟨45,(8),[1,5,13],[186],2⟩) from rfl))
private theorem rec3502 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(9),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1059]? = some (⟨45,(9),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3503 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(9),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1060]? = some (⟨45,(9),[1,5,13],[186],2⟩) from rfl))
private theorem rec3506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(10),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1063]? = some (⟨45,(10),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3507 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(10),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1064]? = some (⟨45,(10),[1,5,13],[186],2⟩) from rfl))
private theorem rec3510 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(11),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1067]? = some (⟨45,(11),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3511 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(11),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1068]? = some (⟨45,(11),[1,5,13],[186],2⟩) from rfl))
private theorem rec3514 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(12),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1071]? = some (⟨45,(12),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3515 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(12),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1072]? = some (⟨45,(12),[1,5,13],[186],2⟩) from rfl))
private theorem rec3518 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(13),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1075]? = some (⟨45,(13),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3519 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(13),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1076]? = some (⟨45,(13),[1,5,13],[186],2⟩) from rfl))
private theorem rec3522 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(14),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1079]? = some (⟨45,(14),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3523 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(14),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1080]? = some (⟨45,(14),[1,5,13],[186],2⟩) from rfl))
private theorem rec3526 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1083]? = some (⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3527 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(15),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1084]? = some (⟨45,(15),[1,5,13],[186],2⟩) from rfl))
private theorem rec3530 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1087]? = some (⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3531 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(16),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1088]? = some (⟨45,(16),[1,5,13],[186],2⟩) from rfl))
private theorem rec3534 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1091]? = some (⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3535 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(17),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1092]? = some (⟨45,(17),[1,5,13],[186],2⟩) from rfl))
private theorem rec3538 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1095]? = some (⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3539 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(18),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1096]? = some (⟨45,(18),[1,5,13],[186],2⟩) from rfl))
private theorem rec3542 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1099]? = some (⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3543 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(19),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1100]? = some (⟨45,(19),[1,5,13],[186],2⟩) from rfl))
private theorem rec3546 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1103]? = some (⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3547 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(20),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1104]? = some (⟨45,(20),[1,5,13],[186],2⟩) from rfl))
private theorem rec3550 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1107]? = some (⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3551 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(21),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1108]? = some (⟨45,(21),[1,5,13],[186],2⟩) from rfl))
private theorem rec3554 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1111]? = some (⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3555 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(22),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1112]? = some (⟨45,(22),[1,5,13],[186],2⟩) from rfl))
private theorem rec3558 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1115]? = some (⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3559 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(23),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1116]? = some (⟨45,(23),[1,5,13],[186],2⟩) from rfl))
private theorem rec3562 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1119]? = some (⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3563 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 45 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(24),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1120]? = some (⟨45,(24),[1,5,13],[186],2⟩) from rfl))
private theorem rec3566 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1123]? = some (⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩) from rfl))
private theorem rec3567 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[1,5,13],[186],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1124]? = some (⟨47,(0),[1,5,13],[186],189⟩) from rfl))
private theorem rec3576 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1133]? = some (⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩) from rfl))
private theorem rec3577 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[1,5,13],[186],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1134]? = some (⟨47,(1),[1,5,13],[186],260⟩) from rfl))
private theorem rec3586 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1143]? = some (⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩) from rfl))
private theorem rec3587 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[1,5,13],[186],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1144]? = some (⟨47,(2),[1,5,13],[186],261⟩) from rfl))
private theorem rec3597 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1154]? = some (⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩) from rfl))
private theorem rec3598 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[1,5,13],[186],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1155]? = some (⟨47,(3),[1,5,13],[186],262⟩) from rfl))
private theorem rec3608 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1165]? = some (⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩) from rfl))
private theorem rec3609 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[1,5,13],[186],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1166]? = some (⟨47,(4),[1,5,13],[186],263⟩) from rfl))
private theorem rec3619 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1176]? = some (⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩) from rfl))
private theorem rec3620 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[1,5,13],[186],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1177]? = some (⟨47,(5),[1,5,13],[186],189⟩) from rfl))
private theorem rec3629 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1186]? = some (⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩) from rfl))
private theorem rec3630 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[1,5,13],[186],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1187]? = some (⟨47,(6),[1,5,13],[186],260⟩) from rfl))
private theorem rec3640 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[1,2,5,6,13,14],[190],319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[1]? = some (⟨47,(7),[1,2,5,6,13,14],[190],319⟩) from rfl))
private theorem rec3642 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[1,5,13],[186],319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[3]? = some (⟨47,(7),[1,5,13],[186],319⟩) from rfl))
private theorem rec3656 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[1,2,5,6,13,14],[190],320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[17]? = some (⟨47,(8),[1,2,5,6,13,14],[190],320⟩) from rfl))
private theorem rec3658 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[1,5,13],[186],320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[19]? = some (⟨47,(8),[1,5,13],[186],320⟩) from rfl))
private theorem rec3674 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[1,2,5,6,13,14],[190],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[35]? = some (⟨47,(9),[1,2,5,6,13,14],[190],321⟩) from rfl))
private theorem rec3676 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[1,5,13],[186],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[37]? = some (⟨47,(9),[1,5,13],[186],321⟩) from rfl))
private theorem rec3689 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[50]? = some (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) from rfl))
private theorem rec3690 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[1,5,13],[186],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[51]? = some (⟨47,(10),[1,5,13],[186],194⟩) from rfl))
private theorem rec3699 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[60]? = some (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) from rfl))
private theorem rec3700 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[1,5,13],[186],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[61]? = some (⟨47,(11),[1,5,13],[186],267⟩) from rfl))
private theorem rec3710 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[1,2,5,6,13,14],[190],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[71]? = some (⟨47,(12),[1,2,5,6,13,14],[190],322⟩) from rfl))
private theorem rec3712 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[1,5,13],[186],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[73]? = some (⟨47,(12),[1,5,13],[186],322⟩) from rfl))
private theorem rec3726 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[1,2,5,6,13,14],[190],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[87]? = some (⟨47,(13),[1,2,5,6,13,14],[190],322⟩) from rfl))
private theorem rec3728 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[1,5,13],[186],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[89]? = some (⟨47,(13),[1,5,13],[186],322⟩) from rfl))
private theorem rec3744 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[1,2,5,6,13,14],[190],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[105]? = some (⟨47,(14),[1,2,5,6,13,14],[190],321⟩) from rfl))
private theorem rec3746 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[1,5,13],[186],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[107]? = some (⟨47,(14),[1,5,13],[186],321⟩) from rfl))
private theorem rec3759 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[120]? = some (⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩) from rfl))
private theorem rec3760 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[1,5,13],[186],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[121]? = some (⟨47,(15),[1,5,13],[186],196⟩) from rfl))
private theorem rec3769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[130]? = some (⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩) from rfl))
private theorem rec3770 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[1,5,13],[186],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[131]? = some (⟨47,(16),[1,5,13],[186],269⟩) from rfl))
private theorem rec3781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[1,2,5,6,13,14],[190],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[142]? = some (⟨47,(17),[1,2,5,6,13,14],[190],323⟩) from rfl))
private theorem rec3782 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[1,5,13],[186],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[143]? = some (⟨47,(17),[1,5,13],[186],323⟩) from rfl))
private theorem rec3796 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[1,2,5,6,13,14],[190],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[157]? = some (⟨47,(18),[1,2,5,6,13,14],[190],323⟩) from rfl))
private theorem rec3797 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[1,5,13],[186],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[158]? = some (⟨47,(18),[1,5,13],[186],323⟩) from rfl))
private theorem rec3813 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[1,2,5,6,13,14],[190],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[174]? = some (⟨47,(19),[1,2,5,6,13,14],[190],323⟩) from rfl))
private theorem rec3814 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[1,5,13],[186],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[175]? = some (⟨47,(19),[1,5,13],[186],323⟩) from rfl))
private theorem rec3826 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[187]? = some (⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩) from rfl))
private theorem rec3827 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[1,5,13],[186],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[188]? = some (⟨47,(20),[1,5,13],[186],198⟩) from rfl))
private theorem rec3836 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[197]? = some (⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩) from rfl))
private theorem rec3837 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[1,5,13],[186],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[198]? = some (⟨47,(21),[1,5,13],[186],271⟩) from rfl))
private theorem rec3848 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[1,2,5,6,13,14],[190],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[209]? = some (⟨47,(22),[1,2,5,6,13,14],[190],324⟩) from rfl))
private theorem rec3849 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[1,5,13],[186],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[210]? = some (⟨47,(22),[1,5,13],[186],324⟩) from rfl))
private theorem rec3863 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[1,2,5,6,13,14],[190],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[224]? = some (⟨47,(23),[1,2,5,6,13,14],[190],324⟩) from rfl))
private theorem rec3864 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[1,5,13],[186],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[225]? = some (⟨47,(23),[1,5,13],[186],324⟩) from rfl))
private theorem rec3880 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[1,2,5,6,13,14],[190],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[241]? = some (⟨47,(24),[1,2,5,6,13,14],[190],324⟩) from rfl))
private theorem rec3881 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[1,5,13],[186],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[242]? = some (⟨47,(24),[1,5,13],[186],324⟩) from rfl))
private theorem rec4149 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(0),[1,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[0]? = some (⟨55,(0),[1,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4150 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(0),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1]? = some (⟨55,(0),[1,5,13],[186],3⟩) from rfl))
private theorem rec4158 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[9]? = some (⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4159 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(1),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[10]? = some (⟨55,(1),[1,5,13],[186],3⟩) from rfl))
private theorem rec4169 (si parent : ℕ) (hs : si ∈ ([6, 13] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(2),[6,13],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[20]? = some (⟨55,(2),[6,13],[190],2⟩) from rfl))
private theorem rec4174 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([170, 174, 186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(2),[13],[170,174,186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[25]? = some (⟨55,(2),[13],[170,174,186],2⟩) from rfl))
private theorem rec4184 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([186, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(3),[13],[186,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[35]? = some (⟨55,(3),[13],[186,190],2⟩) from rfl))
private theorem rec4185 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[36]? = some (⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4186 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(4),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[37]? = some (⟨55,(4),[1,5,13],[186],3⟩) from rfl))
private theorem rec4193 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[44]? = some (⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4194 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(5),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[45]? = some (⟨55,(5),[1,5,13],[186],3⟩) from rfl))
private theorem rec4204 (si parent : ℕ) (hs : si ∈ ([6, 13] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(6),[6,13],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[55]? = some (⟨55,(6),[6,13],[190],2⟩) from rfl))
private theorem rec4209 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(6),[13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[60]? = some (⟨55,(6),[13],[186],2⟩) from rfl))
private theorem rec4210 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(7),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[61]? = some (⟨55,(7),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4211 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(7),[1,5,13],[186],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[62]? = some (⟨55,(7),[1,5,13],[186],2⟩) from rfl))
private theorem rec4220 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(8),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[71]? = some (⟨55,(8),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4221 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(8),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[72]? = some (⟨55,(8),[1,5,13],[186],3⟩) from rfl))
private theorem rec4226 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[77]? = some (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4227 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(9),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[78]? = some (⟨55,(9),[1,5,13],[186],3⟩) from rfl))
private theorem rec4231 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(10),[1,2,5,6,13,14],[190],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[82]? = some (⟨55,(10),[1,2,5,6,13,14],[190],29⟩) from rfl))
private theorem rec4233 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(10),[1,5,13],[186],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[84]? = some (⟨55,(10),[1,5,13],[186],29⟩) from rfl))
private theorem rec4239 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(11),[1,2,5,6,13,14],[190],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[90]? = some (⟨55,(11),[1,2,5,6,13,14],[190],234⟩) from rfl))
private theorem rec4240 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(11),[1,5,13],[186],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[91]? = some (⟨55,(11),[1,5,13],[186],234⟩) from rfl))
private theorem rec4247 (si parent : ℕ) (hs : si ∈ ([5, 6, 13] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(12),[5,6,13],[170,174,190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[98]? = some (⟨55,(12),[5,6,13],[170,174,190],99⟩) from rfl))
private theorem rec4248 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(12),[5,13],[186],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[99]? = some (⟨55,(12),[5,13],[186],99⟩) from rfl))
private theorem rec4256 (si parent : ℕ) (hs : si ∈ ([5, 6, 13] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(13),[5,6,13],[170,174,190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[107]? = some (⟨55,(13),[5,6,13],[170,174,190],99⟩) from rfl))
private theorem rec4257 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(13),[5,13],[186],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[108]? = some (⟨55,(13),[5,13],[186],99⟩) from rfl))
private theorem rec4262 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(14),[1,2,5,6,13],[190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[113]? = some (⟨55,(14),[1,2,5,6,13],[190],99⟩) from rfl))
private theorem rec4264 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(14),[1,5,13],[186],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[115]? = some (⟨55,(14),[1,5,13],[186],99⟩) from rfl))
private theorem rec4271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(15),[1,2,5,6,13,14],[190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[122]? = some (⟨55,(15),[1,2,5,6,13,14],[190],99⟩) from rfl))
private theorem rec4272 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 55 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(15),[1,5,13],[186],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[123]? = some (⟨55,(15),[1,5,13],[186],99⟩) from rfl))
private theorem rec4425 (si parent : ℕ) (hs : si ∈ ([13] : List ℕ)) (hp : parent ∈ ([170, 174, 186, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(5),[13],[170,174,186,190],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[276]? = some (⟨58,(5),[13],[170,174,186,190],105⟩) from rfl))
private theorem rec4428 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 58 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(7),[1,5,13],[186],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[279]? = some (⟨58,(7),[1,5,13],[186],3⟩) from rfl))
private theorem rec4431 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(7),[5,13],[174,190],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[282]? = some (⟨58,(7),[5,13],[174,190],48⟩) from rfl))
private theorem rec4436 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(8),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[287]? = some (⟨58,(8),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4440 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([170, 186] : List ℕ)) : section14Recorded section14Catalog si parent 58 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(8),[5,13],[170,186],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[291]? = some (⟨58,(8),[5,13],[170,186],48⟩) from rfl))
private theorem rec4447 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(9),[5,6,13,14],[170,174,190],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[298]? = some (⟨58,(9),[5,6,13,14],[170,174,190],143⟩) from rfl))
private theorem rec4448 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 58 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(9),[5,13],[186],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[299]? = some (⟨58,(9),[5,13],[186],143⟩) from rfl))
private theorem rec4453 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(15),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[304]? = some (⟨58,(15),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4457 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([170, 186] : List ℕ)) : section14Recorded section14Catalog si parent 58 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(15),[5,13],[170,186],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[308]? = some (⟨58,(15),[5,13],[170,186],48⟩) from rfl))
private theorem rec4462 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(16),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[313]? = some (⟨58,(16),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4466 (si parent : ℕ) (hs : si ∈ ([5, 13] : List ℕ)) (hp : parent ∈ ([170, 186] : List ℕ)) : section14Recorded section14Catalog si parent 58 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(16),[5,13],[170,186],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[317]? = some (⟨58,(16),[5,13],[170,186],48⟩) from rfl))
private theorem rec4470 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(17),[1,2,5,6,13,14],[170,174,190],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[321]? = some (⟨58,(17),[1,2,5,6,13,14],[170,174,190],48⟩) from rfl))
private theorem rec4471 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 58 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(17),[1,5,13],[186],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[322]? = some (⟨58,(17),[1,5,13],[186],48⟩) from rfl))
private theorem rec4475 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(19),[1,2,5,6,13,14],[174,190],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[326]? = some (⟨58,(19),[1,2,5,6,13,14],[174,190],143⟩) from rfl))
private theorem rec4476 (si parent : ℕ) (hs : si ∈ ([1, 13] : List ℕ)) (hp : parent ∈ ([170, 186] : List ℕ)) : section14Recorded section14Catalog si parent 58 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(19),[1,13],[170,186],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[327]? = some (⟨58,(19),[1,13],[170,186],48⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 13).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 176).take 16, section14Recorded section14Catalog 13 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 13 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 13).plans.drop 2).take 1 = [⟨3,38,[([1],[]),([2],[])],true,[(39,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(54,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 13)).drop 176).take 16 = [⟨1,176,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,177,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,178,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,179,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,180,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,181,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,182,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,183,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,184,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,185,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,186,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,187,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,188,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,189,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,190,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩,⟨1,191,[⟨true,true,1⟩,⟨true,false,14⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,13⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec3085 13 176 (by decide) (by decide)
  · left
    exact rec3085 13 177 (by decide) (by decide)
  · left
    exact rec2997 13 178 (by decide) (by decide)
  · left
    exact rec2997 13 179 (by decide) (by decide)
  · left
    exact rec3085 13 180 (by decide) (by decide)
  · left
    exact rec3085 13 181 (by decide) (by decide)
  · left
    exact rec2997 13 182 (by decide) (by decide)
  · left
    exact rec2997 13 183 (by decide) (by decide)
  · left
    exact rec2996 13 184 (by decide) (by decide)
  · left
    exact rec2996 13 185 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(39,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(54,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 39)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 40)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3087 13 186 (by decide) (by decide)
      · right
        exact rec3092 13 186 (by decide) (by decide)
      · right
        exact rec3097 13 186 (by decide) (by decide)
      · right
        exact rec3102 13 186 (by decide) (by decide)
      · right
        exact rec3107 13 186 (by decide) (by decide)
      · right
        exact rec3112 13 186 (by decide) (by decide)
      · right
        exact rec3117 13 186 (by decide) (by decide)
      · right
        exact rec3122 13 186 (by decide) (by decide)
      · right
        exact rec3127 13 186 (by decide) (by decide)
      · right
        exact rec3132 13 186 (by decide) (by decide)
      · right
        exact rec3137 13 186 (by decide) (by decide)
      · right
        exact rec3142 13 186 (by decide) (by decide)
      · right
        exact rec3147 13 186 (by decide) (by decide)
      · right
        exact rec3152 13 186 (by decide) (by decide)
      · right
        exact rec3157 13 186 (by decide) (by decide)
      · right
        exact rec3162 13 186 (by decide) (by decide)
      · right
        exact rec3167 13 186 (by decide) (by decide)
      · right
        exact rec3172 13 186 (by decide) (by decide)
      · right
        exact rec3177 13 186 (by decide) (by decide)
      · right
        exact rec3182 13 186 (by decide) (by decide)
      · right
        exact rec3187 13 186 (by decide) (by decide)
      · right
        exact rec3192 13 186 (by decide) (by decide)
      · right
        exact rec3197 13 186 (by decide) (by decide)
      · right
        exact rec3202 13 186 (by decide) (by decide)
      · right
        exact rec3207 13 186 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 41)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 42)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3214 13 186 (by decide) (by decide)
      · right
        exact rec3225 13 186 (by decide) (by decide)
      · right
        exact rec3235 13 186 (by decide) (by decide)
      · right
        exact rec3245 13 186 (by decide) (by decide)
      · right
        exact rec3255 13 186 (by decide) (by decide)
      · right
        exact rec3265 13 186 (by decide) (by decide)
      · right
        exact rec3276 13 186 (by decide) (by decide)
      · right
        exact rec3286 13 186 (by decide) (by decide)
      · right
        exact rec3296 13 186 (by decide) (by decide)
      · right
        exact rec3306 13 186 (by decide) (by decide)
      · right
        exact rec3316 13 186 (by decide) (by decide)
      · right
        exact rec3327 13 186 (by decide) (by decide)
      · right
        exact rec3337 13 186 (by decide) (by decide)
      · right
        exact rec3347 13 186 (by decide) (by decide)
      · right
        exact rec3357 13 186 (by decide) (by decide)
      · right
        exact rec3367 13 186 (by decide) (by decide)
      · right
        exact rec3378 13 186 (by decide) (by decide)
      · right
        exact rec3388 13 186 (by decide) (by decide)
      · right
        exact rec3398 13 186 (by decide) (by decide)
      · right
        exact rec3408 13 186 (by decide) (by decide)
      · right
        exact rec3418 13 186 (by decide) (by decide)
      · right
        exact rec3429 13 186 (by decide) (by decide)
      · right
        exact rec3439 13 186 (by decide) (by decide)
      · right
        exact rec3449 13 186 (by decide) (by decide)
      · right
        exact rec3459 13 186 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 43)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 44)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 45)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3467 13 186 (by decide) (by decide)
      · right
        exact rec3471 13 186 (by decide) (by decide)
      · right
        exact rec3475 13 186 (by decide) (by decide)
      · right
        exact rec3479 13 186 (by decide) (by decide)
      · right
        exact rec3483 13 186 (by decide) (by decide)
      · right
        exact rec3487 13 186 (by decide) (by decide)
      · right
        exact rec3491 13 186 (by decide) (by decide)
      · right
        exact rec3495 13 186 (by decide) (by decide)
      · right
        exact rec3499 13 186 (by decide) (by decide)
      · right
        exact rec3503 13 186 (by decide) (by decide)
      · right
        exact rec3507 13 186 (by decide) (by decide)
      · right
        exact rec3511 13 186 (by decide) (by decide)
      · right
        exact rec3515 13 186 (by decide) (by decide)
      · right
        exact rec3519 13 186 (by decide) (by decide)
      · right
        exact rec3523 13 186 (by decide) (by decide)
      · right
        exact rec3527 13 186 (by decide) (by decide)
      · right
        exact rec3531 13 186 (by decide) (by decide)
      · right
        exact rec3535 13 186 (by decide) (by decide)
      · right
        exact rec3539 13 186 (by decide) (by decide)
      · right
        exact rec3543 13 186 (by decide) (by decide)
      · right
        exact rec3547 13 186 (by decide) (by decide)
      · right
        exact rec3551 13 186 (by decide) (by decide)
      · right
        exact rec3555 13 186 (by decide) (by decide)
      · right
        exact rec3559 13 186 (by decide) (by decide)
      · right
        exact rec3563 13 186 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 46)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 47)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3567 13 186 (by decide) (by decide)
      · right
        exact rec3577 13 186 (by decide) (by decide)
      · right
        exact rec3587 13 186 (by decide) (by decide)
      · right
        exact rec3598 13 186 (by decide) (by decide)
      · right
        exact rec3609 13 186 (by decide) (by decide)
      · right
        exact rec3620 13 186 (by decide) (by decide)
      · right
        exact rec3630 13 186 (by decide) (by decide)
      · right
        exact rec3642 13 186 (by decide) (by decide)
      · right
        exact rec3658 13 186 (by decide) (by decide)
      · right
        exact rec3676 13 186 (by decide) (by decide)
      · right
        exact rec3690 13 186 (by decide) (by decide)
      · right
        exact rec3700 13 186 (by decide) (by decide)
      · right
        exact rec3712 13 186 (by decide) (by decide)
      · right
        exact rec3728 13 186 (by decide) (by decide)
      · right
        exact rec3746 13 186 (by decide) (by decide)
      · right
        exact rec3760 13 186 (by decide) (by decide)
      · right
        exact rec3770 13 186 (by decide) (by decide)
      · right
        exact rec3782 13 186 (by decide) (by decide)
      · right
        exact rec3797 13 186 (by decide) (by decide)
      · right
        exact rec3814 13 186 (by decide) (by decide)
      · right
        exact rec3827 13 186 (by decide) (by decide)
      · right
        exact rec3837 13 186 (by decide) (by decide)
      · right
        exact rec3849 13 186 (by decide) (by decide)
      · right
        exact rec3864 13 186 (by decide) (by decide)
      · right
        exact rec3881 13 186 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 48)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 54)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 55)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4150 13 186 (by decide) (by decide)
      · right
        exact rec4159 13 186 (by decide) (by decide)
      · right
        exact rec4174 13 186 (by decide) (by decide)
      · right
        exact rec4184 13 186 (by decide) (by decide)
      · right
        exact rec4186 13 186 (by decide) (by decide)
      · right
        exact rec4194 13 186 (by decide) (by decide)
      · right
        exact rec4209 13 186 (by decide) (by decide)
      · right
        exact rec4211 13 186 (by decide) (by decide)
      · right
        exact rec4221 13 186 (by decide) (by decide)
      · right
        exact rec4227 13 186 (by decide) (by decide)
      · right
        exact rec4233 13 186 (by decide) (by decide)
      · right
        exact rec4240 13 186 (by decide) (by decide)
      · right
        exact rec4248 13 186 (by decide) (by decide)
      · right
        exact rec4257 13 186 (by decide) (by decide)
      · right
        exact rec4264 13 186 (by decide) (by decide)
      · right
        exact rec4272 13 186 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 58)).length = 20 := by decide +kernel
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
        exact rec4425 13 186 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4428 13 186 (by decide) (by decide)
      · right
        exact rec4440 13 186 (by decide) (by decide)
      · right
        exact rec4448 13 186 (by decide) (by decide)
      · left
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
        exact rec4457 13 186 (by decide) (by decide)
      · right
        exact rec4466 13 186 (by decide) (by decide)
      · right
        exact rec4471 13 186 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4476 13 186 (by decide) (by decide)
  · left
    exact rec3004 13 187 (by decide) (by decide)
  · left
    exact rec2996 13 188 (by decide) (by decide)
  · left
    exact rec2996 13 189 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(39,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(54,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 39)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 40)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3086 13 190 (by decide) (by decide)
      · right
        exact rec3091 13 190 (by decide) (by decide)
      · right
        exact rec3096 13 190 (by decide) (by decide)
      · right
        exact rec3101 13 190 (by decide) (by decide)
      · right
        exact rec3106 13 190 (by decide) (by decide)
      · right
        exact rec3111 13 190 (by decide) (by decide)
      · right
        exact rec3116 13 190 (by decide) (by decide)
      · right
        exact rec3121 13 190 (by decide) (by decide)
      · right
        exact rec3126 13 190 (by decide) (by decide)
      · right
        exact rec3131 13 190 (by decide) (by decide)
      · right
        exact rec3136 13 190 (by decide) (by decide)
      · right
        exact rec3141 13 190 (by decide) (by decide)
      · right
        exact rec3146 13 190 (by decide) (by decide)
      · right
        exact rec3151 13 190 (by decide) (by decide)
      · right
        exact rec3156 13 190 (by decide) (by decide)
      · right
        exact rec3161 13 190 (by decide) (by decide)
      · right
        exact rec3166 13 190 (by decide) (by decide)
      · right
        exact rec3171 13 190 (by decide) (by decide)
      · right
        exact rec3176 13 190 (by decide) (by decide)
      · right
        exact rec3181 13 190 (by decide) (by decide)
      · right
        exact rec3186 13 190 (by decide) (by decide)
      · right
        exact rec3191 13 190 (by decide) (by decide)
      · right
        exact rec3196 13 190 (by decide) (by decide)
      · right
        exact rec3201 13 190 (by decide) (by decide)
      · right
        exact rec3206 13 190 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 41)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 42)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3213 13 190 (by decide) (by decide)
      · right
        exact rec3224 13 190 (by decide) (by decide)
      · right
        exact rec3234 13 190 (by decide) (by decide)
      · right
        exact rec3244 13 190 (by decide) (by decide)
      · right
        exact rec3254 13 190 (by decide) (by decide)
      · right
        exact rec3264 13 190 (by decide) (by decide)
      · right
        exact rec3275 13 190 (by decide) (by decide)
      · right
        exact rec3285 13 190 (by decide) (by decide)
      · right
        exact rec3295 13 190 (by decide) (by decide)
      · right
        exact rec3305 13 190 (by decide) (by decide)
      · right
        exact rec3315 13 190 (by decide) (by decide)
      · right
        exact rec3326 13 190 (by decide) (by decide)
      · right
        exact rec3336 13 190 (by decide) (by decide)
      · right
        exact rec3346 13 190 (by decide) (by decide)
      · right
        exact rec3356 13 190 (by decide) (by decide)
      · right
        exact rec3366 13 190 (by decide) (by decide)
      · right
        exact rec3377 13 190 (by decide) (by decide)
      · right
        exact rec3387 13 190 (by decide) (by decide)
      · right
        exact rec3397 13 190 (by decide) (by decide)
      · right
        exact rec3407 13 190 (by decide) (by decide)
      · right
        exact rec3417 13 190 (by decide) (by decide)
      · right
        exact rec3428 13 190 (by decide) (by decide)
      · right
        exact rec3438 13 190 (by decide) (by decide)
      · right
        exact rec3448 13 190 (by decide) (by decide)
      · right
        exact rec3458 13 190 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 43)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 44)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 45)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3466 13 190 (by decide) (by decide)
      · right
        exact rec3470 13 190 (by decide) (by decide)
      · right
        exact rec3474 13 190 (by decide) (by decide)
      · right
        exact rec3478 13 190 (by decide) (by decide)
      · right
        exact rec3482 13 190 (by decide) (by decide)
      · right
        exact rec3486 13 190 (by decide) (by decide)
      · right
        exact rec3490 13 190 (by decide) (by decide)
      · right
        exact rec3494 13 190 (by decide) (by decide)
      · right
        exact rec3498 13 190 (by decide) (by decide)
      · right
        exact rec3502 13 190 (by decide) (by decide)
      · right
        exact rec3506 13 190 (by decide) (by decide)
      · right
        exact rec3510 13 190 (by decide) (by decide)
      · right
        exact rec3514 13 190 (by decide) (by decide)
      · right
        exact rec3518 13 190 (by decide) (by decide)
      · right
        exact rec3522 13 190 (by decide) (by decide)
      · right
        exact rec3526 13 190 (by decide) (by decide)
      · right
        exact rec3530 13 190 (by decide) (by decide)
      · right
        exact rec3534 13 190 (by decide) (by decide)
      · right
        exact rec3538 13 190 (by decide) (by decide)
      · right
        exact rec3542 13 190 (by decide) (by decide)
      · right
        exact rec3546 13 190 (by decide) (by decide)
      · right
        exact rec3550 13 190 (by decide) (by decide)
      · right
        exact rec3554 13 190 (by decide) (by decide)
      · right
        exact rec3558 13 190 (by decide) (by decide)
      · right
        exact rec3562 13 190 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 46)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 47)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3566 13 190 (by decide) (by decide)
      · right
        exact rec3576 13 190 (by decide) (by decide)
      · right
        exact rec3586 13 190 (by decide) (by decide)
      · right
        exact rec3597 13 190 (by decide) (by decide)
      · right
        exact rec3608 13 190 (by decide) (by decide)
      · right
        exact rec3619 13 190 (by decide) (by decide)
      · right
        exact rec3629 13 190 (by decide) (by decide)
      · right
        exact rec3640 13 190 (by decide) (by decide)
      · right
        exact rec3656 13 190 (by decide) (by decide)
      · right
        exact rec3674 13 190 (by decide) (by decide)
      · right
        exact rec3689 13 190 (by decide) (by decide)
      · right
        exact rec3699 13 190 (by decide) (by decide)
      · right
        exact rec3710 13 190 (by decide) (by decide)
      · right
        exact rec3726 13 190 (by decide) (by decide)
      · right
        exact rec3744 13 190 (by decide) (by decide)
      · right
        exact rec3759 13 190 (by decide) (by decide)
      · right
        exact rec3769 13 190 (by decide) (by decide)
      · right
        exact rec3781 13 190 (by decide) (by decide)
      · right
        exact rec3796 13 190 (by decide) (by decide)
      · right
        exact rec3813 13 190 (by decide) (by decide)
      · right
        exact rec3826 13 190 (by decide) (by decide)
      · right
        exact rec3836 13 190 (by decide) (by decide)
      · right
        exact rec3848 13 190 (by decide) (by decide)
      · right
        exact rec3863 13 190 (by decide) (by decide)
      · right
        exact rec3880 13 190 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 48)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 54)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 55)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4149 13 190 (by decide) (by decide)
      · right
        exact rec4158 13 190 (by decide) (by decide)
      · right
        exact rec4169 13 190 (by decide) (by decide)
      · right
        exact rec4184 13 190 (by decide) (by decide)
      · right
        exact rec4185 13 190 (by decide) (by decide)
      · right
        exact rec4193 13 190 (by decide) (by decide)
      · right
        exact rec4204 13 190 (by decide) (by decide)
      · right
        exact rec4210 13 190 (by decide) (by decide)
      · right
        exact rec4220 13 190 (by decide) (by decide)
      · right
        exact rec4226 13 190 (by decide) (by decide)
      · right
        exact rec4231 13 190 (by decide) (by decide)
      · right
        exact rec4239 13 190 (by decide) (by decide)
      · right
        exact rec4247 13 190 (by decide) (by decide)
      · right
        exact rec4256 13 190 (by decide) (by decide)
      · right
        exact rec4262 13 190 (by decide) (by decide)
      · right
        exact rec4271 13 190 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 58)).length = 20 := by decide +kernel
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
        exact rec4425 13 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4431 13 190 (by decide) (by decide)
      · right
        exact rec4436 13 190 (by decide) (by decide)
      · right
        exact rec4447 13 190 (by decide) (by decide)
      · left
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
        exact rec4453 13 190 (by decide) (by decide)
      · right
        exact rec4462 13 190 (by decide) (by decide)
      · right
        exact rec4470 13 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4475 13 190 (by decide) (by decide)
  · left
    exact rec3013 13 191 (by decide) (by decide)
end Section14Coverage_13_2_p176_192

#print axioms solution
