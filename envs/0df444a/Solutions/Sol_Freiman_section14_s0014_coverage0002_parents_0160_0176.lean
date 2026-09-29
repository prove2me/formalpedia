-- Prove2me | solution 1 for Freiman.section14_s0014_coverage0002_parents_0160_0176
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T23:47:11.721948+00:00
-- url     : https://prove2.me/submissions/d92bc833-ee8a-4d2b-9d5c-d313fe57ca5a

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
namespace Section14Coverage_14_2_p160_176
private theorem rec2996 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[553]? = some (⟨38,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec2997 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[554]? = some (⟨38,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec3004 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([171, 187] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,13,14],[171,187],206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[561]? = some (⟨38,(-1),[1,2,5,6,13,14],[171,187],206⟩) from rfl))
private theorem rec3005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([175] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,13,14],[175],207⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[562]? = some (⟨38,(-1),[1,2,5,6,13,14],[175],207⟩) from rfl))
private theorem rec3015 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[572]? = some (⟨38,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec3086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(0),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[643]? = some (⟨40,(0),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3091 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(1),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[648]? = some (⟨40,(1),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3096 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(2),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[653]? = some (⟨40,(2),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3101 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(3),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[658]? = some (⟨40,(3),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3106 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(4),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[663]? = some (⟨40,(4),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3111 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(5),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[668]? = some (⟨40,(5),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3116 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(6),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[673]? = some (⟨40,(6),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3121 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(7),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[678]? = some (⟨40,(7),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3126 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(8),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[683]? = some (⟨40,(8),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3131 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(9),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[688]? = some (⟨40,(9),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3136 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(10),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[693]? = some (⟨40,(10),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3141 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(11),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[698]? = some (⟨40,(11),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3146 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(12),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[703]? = some (⟨40,(12),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3151 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(13),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[708]? = some (⟨40,(13),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3156 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(14),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[713]? = some (⟨40,(14),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3161 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(15),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[718]? = some (⟨40,(15),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3166 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(16),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[723]? = some (⟨40,(16),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3171 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(17),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[728]? = some (⟨40,(17),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3176 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(18),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[733]? = some (⟨40,(18),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3181 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(19),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[738]? = some (⟨40,(19),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3186 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(20),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[743]? = some (⟨40,(20),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3191 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(21),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[748]? = some (⟨40,(21),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3196 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(22),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[753]? = some (⟨40,(22),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3201 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(23),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[758]? = some (⟨40,(23),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3206 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 40 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨40,(24),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[763]? = some (⟨40,(24),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec3211 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[1,2,5,6,13,14],[170],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[768]? = some (⟨42,(0),[1,2,5,6,13,14],[170],253⟩) from rfl))
private theorem rec3212 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[1,2,5,6,13,14],[174],288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[769]? = some (⟨42,(0),[1,2,5,6,13,14],[174],288⟩) from rfl))
private theorem rec3222 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[1,2,5,6,13,14],[170],254⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[779]? = some (⟨42,(1),[1,2,5,6,13,14],[170],254⟩) from rfl))
private theorem rec3223 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[1,2,5,6,13,14],[174],289⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[780]? = some (⟨42,(1),[1,2,5,6,13,14],[174],289⟩) from rfl))
private theorem rec3232 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[1,2,5,6,13,14],[170],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[789]? = some (⟨42,(2),[1,2,5,6,13,14],[170],253⟩) from rfl))
private theorem rec3233 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[1,2,5,6,13,14],[174],288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[790]? = some (⟨42,(2),[1,2,5,6,13,14],[174],288⟩) from rfl))
private theorem rec3242 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[1,2,5,6,13,14],[170],255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[799]? = some (⟨42,(3),[1,2,5,6,13,14],[170],255⟩) from rfl))
private theorem rec3243 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[1,2,5,6,13,14],[174],290⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[800]? = some (⟨42,(3),[1,2,5,6,13,14],[174],290⟩) from rfl))
private theorem rec3252 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[1,2,5,6,13,14],[170],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[809]? = some (⟨42,(4),[1,2,5,6,13,14],[170],256⟩) from rfl))
private theorem rec3253 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[1,2,5,6,13,14],[174],291⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[810]? = some (⟨42,(4),[1,2,5,6,13,14],[174],291⟩) from rfl))
private theorem rec3262 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[1,2,5,6,13,14],[170],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[819]? = some (⟨42,(5),[1,2,5,6,13,14],[170],253⟩) from rfl))
private theorem rec3263 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[1,2,5,6,13,14],[174],288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[820]? = some (⟨42,(5),[1,2,5,6,13,14],[174],288⟩) from rfl))
private theorem rec3273 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[1,2,5,6,13,14],[170],254⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[830]? = some (⟨42,(6),[1,2,5,6,13,14],[170],254⟩) from rfl))
private theorem rec3274 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[1,2,5,6,13,14],[174],289⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[831]? = some (⟨42,(6),[1,2,5,6,13,14],[174],289⟩) from rfl))
private theorem rec3283 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[1,2,5,6,13,14],[170],253⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[840]? = some (⟨42,(7),[1,2,5,6,13,14],[170],253⟩) from rfl))
private theorem rec3284 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[1,2,5,6,13,14],[174],288⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[841]? = some (⟨42,(7),[1,2,5,6,13,14],[174],288⟩) from rfl))
private theorem rec3293 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[1,2,5,6,13,14],[170],255⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[850]? = some (⟨42,(8),[1,2,5,6,13,14],[170],255⟩) from rfl))
private theorem rec3294 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[1,2,5,6,13,14],[174],290⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[851]? = some (⟨42,(8),[1,2,5,6,13,14],[174],290⟩) from rfl))
private theorem rec3303 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[1,2,5,6,13,14],[170],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[860]? = some (⟨42,(9),[1,2,5,6,13,14],[170],256⟩) from rfl))
private theorem rec3304 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[1,2,5,6,13,14],[174],291⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[861]? = some (⟨42,(9),[1,2,5,6,13,14],[174],291⟩) from rfl))
private theorem rec3313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[1,2,5,6,13,14],[170],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[870]? = some (⟨42,(10),[1,2,5,6,13,14],[170],257⟩) from rfl))
private theorem rec3314 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[1,2,5,6,13,14],[174],292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[871]? = some (⟨42,(10),[1,2,5,6,13,14],[174],292⟩) from rfl))
private theorem rec3324 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[1,2,5,6,13,14],[170],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[881]? = some (⟨42,(11),[1,2,5,6,13,14],[170],257⟩) from rfl))
private theorem rec3325 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[1,2,5,6,13,14],[174],292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[882]? = some (⟨42,(11),[1,2,5,6,13,14],[174],292⟩) from rfl))
private theorem rec3334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[1,2,5,6,13,14],[170],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[891]? = some (⟨42,(12),[1,2,5,6,13,14],[170],257⟩) from rfl))
private theorem rec3335 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[1,2,5,6,13,14],[174],292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[892]? = some (⟨42,(12),[1,2,5,6,13,14],[174],292⟩) from rfl))
private theorem rec3344 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[1,2,5,6,13,14],[170],257⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[901]? = some (⟨42,(13),[1,2,5,6,13,14],[170],257⟩) from rfl))
private theorem rec3345 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[1,2,5,6,13,14],[174],292⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[902]? = some (⟨42,(13),[1,2,5,6,13,14],[174],292⟩) from rfl))
private theorem rec3354 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[1,2,5,6,13,14],[170],256⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[911]? = some (⟨42,(14),[1,2,5,6,13,14],[170],256⟩) from rfl))
private theorem rec3355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[1,2,5,6,13,14],[174],291⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[912]? = some (⟨42,(14),[1,2,5,6,13,14],[174],291⟩) from rfl))
private theorem rec3364 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[1,2,5,6,13,14],[170],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[921]? = some (⟨42,(15),[1,2,5,6,13,14],[170],258⟩) from rfl))
private theorem rec3365 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[1,2,5,6,13,14],[174],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[922]? = some (⟨42,(15),[1,2,5,6,13,14],[174],293⟩) from rfl))
private theorem rec3375 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[1,2,5,6,13,14],[170],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[932]? = some (⟨42,(16),[1,2,5,6,13,14],[170],258⟩) from rfl))
private theorem rec3376 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[1,2,5,6,13,14],[174],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[933]? = some (⟨42,(16),[1,2,5,6,13,14],[174],293⟩) from rfl))
private theorem rec3385 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[1,2,5,6,13,14],[170],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[942]? = some (⟨42,(17),[1,2,5,6,13,14],[170],258⟩) from rfl))
private theorem rec3386 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[1,2,5,6,13,14],[174],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[943]? = some (⟨42,(17),[1,2,5,6,13,14],[174],293⟩) from rfl))
private theorem rec3395 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[1,2,5,6,13,14],[170],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[952]? = some (⟨42,(18),[1,2,5,6,13,14],[170],258⟩) from rfl))
private theorem rec3396 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[1,2,5,6,13,14],[174],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[953]? = some (⟨42,(18),[1,2,5,6,13,14],[174],293⟩) from rfl))
private theorem rec3405 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[1,2,5,6,13,14],[170],258⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[962]? = some (⟨42,(19),[1,2,5,6,13,14],[170],258⟩) from rfl))
private theorem rec3406 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[1,2,5,6,13,14],[174],293⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[963]? = some (⟨42,(19),[1,2,5,6,13,14],[174],293⟩) from rfl))
private theorem rec3415 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[1,2,5,6,13,14],[170],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[972]? = some (⟨42,(20),[1,2,5,6,13,14],[170],259⟩) from rfl))
private theorem rec3416 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[1,2,5,6,13,14],[174],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[973]? = some (⟨42,(20),[1,2,5,6,13,14],[174],294⟩) from rfl))
private theorem rec3426 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[1,2,5,6,13,14],[170],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[983]? = some (⟨42,(21),[1,2,5,6,13,14],[170],259⟩) from rfl))
private theorem rec3427 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[1,2,5,6,13,14],[174],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[984]? = some (⟨42,(21),[1,2,5,6,13,14],[174],294⟩) from rfl))
private theorem rec3436 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[1,2,5,6,13,14],[170],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[993]? = some (⟨42,(22),[1,2,5,6,13,14],[170],259⟩) from rfl))
private theorem rec3437 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[1,2,5,6,13,14],[174],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[994]? = some (⟨42,(22),[1,2,5,6,13,14],[174],294⟩) from rfl))
private theorem rec3446 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[1,2,5,6,13,14],[170],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1003]? = some (⟨42,(23),[1,2,5,6,13,14],[170],259⟩) from rfl))
private theorem rec3447 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[1,2,5,6,13,14],[174],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1004]? = some (⟨42,(23),[1,2,5,6,13,14],[174],294⟩) from rfl))
private theorem rec3456 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[1,2,5,6,13,14],[170],259⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1013]? = some (⟨42,(24),[1,2,5,6,13,14],[170],259⟩) from rfl))
private theorem rec3457 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[1,2,5,6,13,14],[174],294⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1014]? = some (⟨42,(24),[1,2,5,6,13,14],[174],294⟩) from rfl))
private theorem rec3466 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(0),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1023]? = some (⟨45,(0),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3470 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(1),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1027]? = some (⟨45,(1),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3474 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(2),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1031]? = some (⟨45,(2),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3478 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(3),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1035]? = some (⟨45,(3),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3482 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(4),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1039]? = some (⟨45,(4),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3486 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(5),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1043]? = some (⟨45,(5),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3490 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(6),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1047]? = some (⟨45,(6),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3494 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(7),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1051]? = some (⟨45,(7),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3498 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(8),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1055]? = some (⟨45,(8),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3502 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(9),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1059]? = some (⟨45,(9),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(10),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1063]? = some (⟨45,(10),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3510 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(11),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1067]? = some (⟨45,(11),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3514 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(12),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1071]? = some (⟨45,(12),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3518 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(13),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1075]? = some (⟨45,(13),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3522 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(14),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1079]? = some (⟨45,(14),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3526 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1083]? = some (⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3530 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1087]? = some (⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3534 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1091]? = some (⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3538 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1095]? = some (⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3542 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1099]? = some (⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3546 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1103]? = some (⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3550 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1107]? = some (⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3554 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1111]? = some (⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3558 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1115]? = some (⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3562 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 45 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1119]? = some (⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩) from rfl))
private theorem rec3566 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1123]? = some (⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩) from rfl))
private theorem rec3576 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1133]? = some (⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩) from rfl))
private theorem rec3586 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1143]? = some (⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩) from rfl))
private theorem rec3597 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1154]? = some (⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩) from rfl))
private theorem rec3608 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1165]? = some (⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩) from rfl))
private theorem rec3619 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1176]? = some (⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩) from rfl))
private theorem rec3629 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1186]? = some (⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩) from rfl))
private theorem rec3639 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[1,2,5,6,13,14],[170],264⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[0]? = some (⟨47,(7),[1,2,5,6,13,14],[170],264⟩) from rfl))
private theorem rec3641 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[1,2,5,13,14],[174],295⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[2]? = some (⟨47,(7),[1,2,5,13,14],[174],295⟩) from rfl))
private theorem rec3655 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[1,2,5,6,13,14],[170],265⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[16]? = some (⟨47,(8),[1,2,5,6,13,14],[170],265⟩) from rfl))
private theorem rec3657 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[1,2,13,14],[174],296⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[18]? = some (⟨47,(8),[1,2,13,14],[174],296⟩) from rfl))
private theorem rec3673 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[1,2,5,6,13,14],[170],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[34]? = some (⟨47,(9),[1,2,5,6,13,14],[170],266⟩) from rfl))
private theorem rec3675 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[1,2,5,13,14],[174],297⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[36]? = some (⟨47,(9),[1,2,5,13,14],[174],297⟩) from rfl))
private theorem rec3689 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[50]? = some (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) from rfl))
private theorem rec3699 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[60]? = some (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) from rfl))
private theorem rec3709 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[1,2,5,6,13,14],[170],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[70]? = some (⟨47,(12),[1,2,5,6,13,14],[170],268⟩) from rfl))
private theorem rec3711 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[1,2,5,13,14],[174],298⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[72]? = some (⟨47,(12),[1,2,5,13,14],[174],298⟩) from rfl))
private theorem rec3725 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[1,2,5,6,13,14],[170],268⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[86]? = some (⟨47,(13),[1,2,5,6,13,14],[170],268⟩) from rfl))
private theorem rec3727 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[1,2,5,13,14],[174],298⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[88]? = some (⟨47,(13),[1,2,5,13,14],[174],298⟩) from rfl))
private theorem rec3743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[1,2,5,6,13,14],[170],266⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[104]? = some (⟨47,(14),[1,2,5,6,13,14],[170],266⟩) from rfl))
private theorem rec3745 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[1,2,5,13,14],[174],297⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[106]? = some (⟨47,(14),[1,2,5,13,14],[174],297⟩) from rfl))
private theorem rec3759 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[120]? = some (⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩) from rfl))
private theorem rec3769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[130]? = some (⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩) from rfl))
private theorem rec3779 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[1,2,5,6,13,14],[170],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[140]? = some (⟨47,(17),[1,2,5,6,13,14],[170],270⟩) from rfl))
private theorem rec3780 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[1,2,5,6,13,14],[174],299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[141]? = some (⟨47,(17),[1,2,5,6,13,14],[174],299⟩) from rfl))
private theorem rec3794 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[1,2,5,6,13,14],[170],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[155]? = some (⟨47,(18),[1,2,5,6,13,14],[170],270⟩) from rfl))
private theorem rec3795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[1,2,5,6,13,14],[174],299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[156]? = some (⟨47,(18),[1,2,5,6,13,14],[174],299⟩) from rfl))
private theorem rec3811 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[1,2,5,6,13,14],[170],270⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[172]? = some (⟨47,(19),[1,2,5,6,13,14],[170],270⟩) from rfl))
private theorem rec3812 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[1,2,5,6,13,14],[174],299⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[173]? = some (⟨47,(19),[1,2,5,6,13,14],[174],299⟩) from rfl))
private theorem rec3826 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[187]? = some (⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩) from rfl))
private theorem rec3836 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[197]? = some (⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩) from rfl))
private theorem rec3846 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[1,2,5,6,13,14],[170],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[207]? = some (⟨47,(22),[1,2,5,6,13,14],[170],272⟩) from rfl))
private theorem rec3847 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[1,2,5,6,13,14],[174],300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[208]? = some (⟨47,(22),[1,2,5,6,13,14],[174],300⟩) from rfl))
private theorem rec3861 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[1,2,5,6,13,14],[170],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[222]? = some (⟨47,(23),[1,2,5,6,13,14],[170],272⟩) from rfl))
private theorem rec3862 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[1,2,5,6,13,14],[174],300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[223]? = some (⟨47,(23),[1,2,5,6,13,14],[174],300⟩) from rfl))
private theorem rec3878 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[1,2,5,6,13,14],[170],272⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[239]? = some (⟨47,(24),[1,2,5,6,13,14],[170],272⟩) from rfl))
private theorem rec3879 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[1,2,5,6,13,14],[174],300⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[240]? = some (⟨47,(24),[1,2,5,6,13,14],[174],300⟩) from rfl))
private theorem rec4152 (si parent : ℕ) (hs : si ∈ ([2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(0),[2,6,13,14],[170,174],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[3]? = some (⟨55,(0),[2,6,13,14],[170,174],97⟩) from rfl))
private theorem rec4158 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[9]? = some (⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4165 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(2),[1,2,5,6,14],[170,174],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[16]? = some (⟨55,(2),[1,2,5,6,14],[170,174],97⟩) from rfl))
private theorem rec4178 (si parent : ℕ) (hs : si ∈ ([2, 5, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(3),[2,5,14],[170,174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[29]? = some (⟨55,(3),[2,5,14],[170,174],29⟩) from rfl))
private theorem rec4185 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[36]? = some (⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4193 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[44]? = some (⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4200 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(6),[1,2,5,6,13,14],[170,174],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[51]? = some (⟨55,(6),[1,2,5,6,13,14],[170,174],2⟩) from rfl))
private theorem rec4213 (si parent : ℕ) (hs : si ∈ ([2, 5, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(7),[2,5,14],[170,174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[64]? = some (⟨55,(7),[2,5,14],[170,174],29⟩) from rfl))
private theorem rec4222 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(8),[5,6,13,14],[170,174],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[73]? = some (⟨55,(8),[5,6,13,14],[170,174],97⟩) from rfl))
private theorem rec4226 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[77]? = some (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4232 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(10),[1,2,5,6,13,14],[170,174],97⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[83]? = some (⟨55,(10),[1,2,5,6,13,14],[170,174],97⟩) from rfl))
private theorem rec4238 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(11),[1,2,5,6,13,14],[170,174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[89]? = some (⟨55,(11),[1,2,5,6,13,14],[170,174],29⟩) from rfl))
private theorem rec4246 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(12),[1,2,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[97]? = some (⟨55,(12),[1,2,14],[170,174,190],3⟩) from rfl))
private theorem rec4255 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(13),[1,2,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[106]? = some (⟨55,(13),[1,2,14],[170,174,190],3⟩) from rfl))
private theorem rec4263 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(14),[1,2,5,6,13,14],[170,174],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[114]? = some (⟨55,(14),[1,2,5,6,13,14],[170,174],99⟩) from rfl))
private theorem rec4277 (si parent : ℕ) (hs : si ∈ ([14] : List ℕ)) (hp : parent ∈ ([170, 174] : List ℕ)) : section14Recorded section14Catalog si parent 55 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(15),[14],[170,174],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[128]? = some (⟨55,(15),[14],[170,174],29⟩) from rfl))
private theorem rec4418 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(5),[1,2,5,6,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[269]? = some (⟨58,(5),[1,2,5,6,14],[170,174,190],3⟩) from rfl))
private theorem rec4426 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 58 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[277]? = some (⟨58,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec4427 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(7),[1,2,6,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[278]? = some (⟨58,(7),[1,2,6,14],[174,190],3⟩) from rfl))
private theorem rec4436 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(8),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[287]? = some (⟨58,(8),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4437 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 58 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(8),[1,2,6,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[288]? = some (⟨58,(8),[1,2,6,14],[170],3⟩) from rfl))
private theorem rec4447 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(9),[5,6,13,14],[170,174,190],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[298]? = some (⟨58,(9),[5,6,13,14],[170,174,190],143⟩) from rfl))
private theorem rec4453 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(15),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[304]? = some (⟨58,(15),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4454 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 58 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(15),[1,2,6,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[305]? = some (⟨58,(15),[1,2,6,14],[170],3⟩) from rfl))
private theorem rec4462 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(16),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[313]? = some (⟨58,(16),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4463 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 58 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(16),[1,2,6,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[314]? = some (⟨58,(16),[1,2,6,14],[170],3⟩) from rfl))
private theorem rec4470 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(17),[1,2,5,6,13,14],[170,174,190],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[321]? = some (⟨58,(17),[1,2,5,6,13,14],[170,174,190],48⟩) from rfl))
private theorem rec4475 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(19),[1,2,5,6,13,14],[174,190],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[326]? = some (⟨58,(19),[1,2,5,6,13,14],[174,190],143⟩) from rfl))
private theorem rec4477 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 58 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(19),[2,5,6,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[328]? = some (⟨58,(19),[2,5,6,14],[170],143⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 160).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 14).plans.drop 2).take 1 = [⟨3,38,[([1],[]),([2],[])],true,[(39,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(54,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 160).take 16 = [⟨1,160,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,161,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,162,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,163,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,164,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,165,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,166,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,167,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,168,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,169,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩]⟩,⟨1,170,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,3⟩]⟩,⟨1,171,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩]⟩,⟨1,172,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,true,5⟩]⟩,⟨1,173,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,174,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩,⟨1,175,[⟨true,true,1⟩,⟨true,true,13⟩,⟨true,true,18⟩,⟨true,true,4⟩,⟨true,false,6⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec3015 14 160 (by decide) (by decide)
  · left
    exact rec3015 14 161 (by decide) (by decide)
  · left
    exact rec2997 14 162 (by decide) (by decide)
  · left
    exact rec2997 14 163 (by decide) (by decide)
  · left
    exact rec3015 14 164 (by decide) (by decide)
  · left
    exact rec3015 14 165 (by decide) (by decide)
  · left
    exact rec2997 14 166 (by decide) (by decide)
  · left
    exact rec2997 14 167 (by decide) (by decide)
  · left
    exact rec2996 14 168 (by decide) (by decide)
  · left
    exact rec2996 14 169 (by decide) (by decide)
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
        exact rec3086 14 170 (by decide) (by decide)
      · right
        exact rec3091 14 170 (by decide) (by decide)
      · right
        exact rec3096 14 170 (by decide) (by decide)
      · right
        exact rec3101 14 170 (by decide) (by decide)
      · right
        exact rec3106 14 170 (by decide) (by decide)
      · right
        exact rec3111 14 170 (by decide) (by decide)
      · right
        exact rec3116 14 170 (by decide) (by decide)
      · right
        exact rec3121 14 170 (by decide) (by decide)
      · right
        exact rec3126 14 170 (by decide) (by decide)
      · right
        exact rec3131 14 170 (by decide) (by decide)
      · right
        exact rec3136 14 170 (by decide) (by decide)
      · right
        exact rec3141 14 170 (by decide) (by decide)
      · right
        exact rec3146 14 170 (by decide) (by decide)
      · right
        exact rec3151 14 170 (by decide) (by decide)
      · right
        exact rec3156 14 170 (by decide) (by decide)
      · right
        exact rec3161 14 170 (by decide) (by decide)
      · right
        exact rec3166 14 170 (by decide) (by decide)
      · right
        exact rec3171 14 170 (by decide) (by decide)
      · right
        exact rec3176 14 170 (by decide) (by decide)
      · right
        exact rec3181 14 170 (by decide) (by decide)
      · right
        exact rec3186 14 170 (by decide) (by decide)
      · right
        exact rec3191 14 170 (by decide) (by decide)
      · right
        exact rec3196 14 170 (by decide) (by decide)
      · right
        exact rec3201 14 170 (by decide) (by decide)
      · right
        exact rec3206 14 170 (by decide) (by decide)
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
        exact rec3211 14 170 (by decide) (by decide)
      · right
        exact rec3222 14 170 (by decide) (by decide)
      · right
        exact rec3232 14 170 (by decide) (by decide)
      · right
        exact rec3242 14 170 (by decide) (by decide)
      · right
        exact rec3252 14 170 (by decide) (by decide)
      · right
        exact rec3262 14 170 (by decide) (by decide)
      · right
        exact rec3273 14 170 (by decide) (by decide)
      · right
        exact rec3283 14 170 (by decide) (by decide)
      · right
        exact rec3293 14 170 (by decide) (by decide)
      · right
        exact rec3303 14 170 (by decide) (by decide)
      · right
        exact rec3313 14 170 (by decide) (by decide)
      · right
        exact rec3324 14 170 (by decide) (by decide)
      · right
        exact rec3334 14 170 (by decide) (by decide)
      · right
        exact rec3344 14 170 (by decide) (by decide)
      · right
        exact rec3354 14 170 (by decide) (by decide)
      · right
        exact rec3364 14 170 (by decide) (by decide)
      · right
        exact rec3375 14 170 (by decide) (by decide)
      · right
        exact rec3385 14 170 (by decide) (by decide)
      · right
        exact rec3395 14 170 (by decide) (by decide)
      · right
        exact rec3405 14 170 (by decide) (by decide)
      · right
        exact rec3415 14 170 (by decide) (by decide)
      · right
        exact rec3426 14 170 (by decide) (by decide)
      · right
        exact rec3436 14 170 (by decide) (by decide)
      · right
        exact rec3446 14 170 (by decide) (by decide)
      · right
        exact rec3456 14 170 (by decide) (by decide)
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
        exact rec3466 14 170 (by decide) (by decide)
      · right
        exact rec3470 14 170 (by decide) (by decide)
      · right
        exact rec3474 14 170 (by decide) (by decide)
      · right
        exact rec3478 14 170 (by decide) (by decide)
      · right
        exact rec3482 14 170 (by decide) (by decide)
      · right
        exact rec3486 14 170 (by decide) (by decide)
      · right
        exact rec3490 14 170 (by decide) (by decide)
      · right
        exact rec3494 14 170 (by decide) (by decide)
      · right
        exact rec3498 14 170 (by decide) (by decide)
      · right
        exact rec3502 14 170 (by decide) (by decide)
      · right
        exact rec3506 14 170 (by decide) (by decide)
      · right
        exact rec3510 14 170 (by decide) (by decide)
      · right
        exact rec3514 14 170 (by decide) (by decide)
      · right
        exact rec3518 14 170 (by decide) (by decide)
      · right
        exact rec3522 14 170 (by decide) (by decide)
      · right
        exact rec3526 14 170 (by decide) (by decide)
      · right
        exact rec3530 14 170 (by decide) (by decide)
      · right
        exact rec3534 14 170 (by decide) (by decide)
      · right
        exact rec3538 14 170 (by decide) (by decide)
      · right
        exact rec3542 14 170 (by decide) (by decide)
      · right
        exact rec3546 14 170 (by decide) (by decide)
      · right
        exact rec3550 14 170 (by decide) (by decide)
      · right
        exact rec3554 14 170 (by decide) (by decide)
      · right
        exact rec3558 14 170 (by decide) (by decide)
      · right
        exact rec3562 14 170 (by decide) (by decide)
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
        exact rec3566 14 170 (by decide) (by decide)
      · right
        exact rec3576 14 170 (by decide) (by decide)
      · right
        exact rec3586 14 170 (by decide) (by decide)
      · right
        exact rec3597 14 170 (by decide) (by decide)
      · right
        exact rec3608 14 170 (by decide) (by decide)
      · right
        exact rec3619 14 170 (by decide) (by decide)
      · right
        exact rec3629 14 170 (by decide) (by decide)
      · right
        exact rec3639 14 170 (by decide) (by decide)
      · right
        exact rec3655 14 170 (by decide) (by decide)
      · right
        exact rec3673 14 170 (by decide) (by decide)
      · right
        exact rec3689 14 170 (by decide) (by decide)
      · right
        exact rec3699 14 170 (by decide) (by decide)
      · right
        exact rec3709 14 170 (by decide) (by decide)
      · right
        exact rec3725 14 170 (by decide) (by decide)
      · right
        exact rec3743 14 170 (by decide) (by decide)
      · right
        exact rec3759 14 170 (by decide) (by decide)
      · right
        exact rec3769 14 170 (by decide) (by decide)
      · right
        exact rec3779 14 170 (by decide) (by decide)
      · right
        exact rec3794 14 170 (by decide) (by decide)
      · right
        exact rec3811 14 170 (by decide) (by decide)
      · right
        exact rec3826 14 170 (by decide) (by decide)
      · right
        exact rec3836 14 170 (by decide) (by decide)
      · right
        exact rec3846 14 170 (by decide) (by decide)
      · right
        exact rec3861 14 170 (by decide) (by decide)
      · right
        exact rec3878 14 170 (by decide) (by decide)
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
        exact rec4152 14 170 (by decide) (by decide)
      · right
        exact rec4158 14 170 (by decide) (by decide)
      · right
        exact rec4165 14 170 (by decide) (by decide)
      · right
        exact rec4178 14 170 (by decide) (by decide)
      · right
        exact rec4185 14 170 (by decide) (by decide)
      · right
        exact rec4193 14 170 (by decide) (by decide)
      · right
        exact rec4200 14 170 (by decide) (by decide)
      · right
        exact rec4213 14 170 (by decide) (by decide)
      · right
        exact rec4222 14 170 (by decide) (by decide)
      · right
        exact rec4226 14 170 (by decide) (by decide)
      · right
        exact rec4232 14 170 (by decide) (by decide)
      · right
        exact rec4238 14 170 (by decide) (by decide)
      · right
        exact rec4246 14 170 (by decide) (by decide)
      · right
        exact rec4255 14 170 (by decide) (by decide)
      · right
        exact rec4263 14 170 (by decide) (by decide)
      · right
        exact rec4277 14 170 (by decide) (by decide)
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
        exact rec4418 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4426 14 170 (by decide) (by decide)
      · right
        exact rec4437 14 170 (by decide) (by decide)
      · right
        exact rec4447 14 170 (by decide) (by decide)
      · left
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
        exact rec4454 14 170 (by decide) (by decide)
      · right
        exact rec4463 14 170 (by decide) (by decide)
      · right
        exact rec4470 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4477 14 170 (by decide) (by decide)
  · left
    exact rec3004 14 171 (by decide) (by decide)
  · left
    exact rec2996 14 172 (by decide) (by decide)
  · left
    exact rec2996 14 173 (by decide) (by decide)
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
        exact rec3086 14 174 (by decide) (by decide)
      · right
        exact rec3091 14 174 (by decide) (by decide)
      · right
        exact rec3096 14 174 (by decide) (by decide)
      · right
        exact rec3101 14 174 (by decide) (by decide)
      · right
        exact rec3106 14 174 (by decide) (by decide)
      · right
        exact rec3111 14 174 (by decide) (by decide)
      · right
        exact rec3116 14 174 (by decide) (by decide)
      · right
        exact rec3121 14 174 (by decide) (by decide)
      · right
        exact rec3126 14 174 (by decide) (by decide)
      · right
        exact rec3131 14 174 (by decide) (by decide)
      · right
        exact rec3136 14 174 (by decide) (by decide)
      · right
        exact rec3141 14 174 (by decide) (by decide)
      · right
        exact rec3146 14 174 (by decide) (by decide)
      · right
        exact rec3151 14 174 (by decide) (by decide)
      · right
        exact rec3156 14 174 (by decide) (by decide)
      · right
        exact rec3161 14 174 (by decide) (by decide)
      · right
        exact rec3166 14 174 (by decide) (by decide)
      · right
        exact rec3171 14 174 (by decide) (by decide)
      · right
        exact rec3176 14 174 (by decide) (by decide)
      · right
        exact rec3181 14 174 (by decide) (by decide)
      · right
        exact rec3186 14 174 (by decide) (by decide)
      · right
        exact rec3191 14 174 (by decide) (by decide)
      · right
        exact rec3196 14 174 (by decide) (by decide)
      · right
        exact rec3201 14 174 (by decide) (by decide)
      · right
        exact rec3206 14 174 (by decide) (by decide)
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
        exact rec3212 14 174 (by decide) (by decide)
      · right
        exact rec3223 14 174 (by decide) (by decide)
      · right
        exact rec3233 14 174 (by decide) (by decide)
      · right
        exact rec3243 14 174 (by decide) (by decide)
      · right
        exact rec3253 14 174 (by decide) (by decide)
      · right
        exact rec3263 14 174 (by decide) (by decide)
      · right
        exact rec3274 14 174 (by decide) (by decide)
      · right
        exact rec3284 14 174 (by decide) (by decide)
      · right
        exact rec3294 14 174 (by decide) (by decide)
      · right
        exact rec3304 14 174 (by decide) (by decide)
      · right
        exact rec3314 14 174 (by decide) (by decide)
      · right
        exact rec3325 14 174 (by decide) (by decide)
      · right
        exact rec3335 14 174 (by decide) (by decide)
      · right
        exact rec3345 14 174 (by decide) (by decide)
      · right
        exact rec3355 14 174 (by decide) (by decide)
      · right
        exact rec3365 14 174 (by decide) (by decide)
      · right
        exact rec3376 14 174 (by decide) (by decide)
      · right
        exact rec3386 14 174 (by decide) (by decide)
      · right
        exact rec3396 14 174 (by decide) (by decide)
      · right
        exact rec3406 14 174 (by decide) (by decide)
      · right
        exact rec3416 14 174 (by decide) (by decide)
      · right
        exact rec3427 14 174 (by decide) (by decide)
      · right
        exact rec3437 14 174 (by decide) (by decide)
      · right
        exact rec3447 14 174 (by decide) (by decide)
      · right
        exact rec3457 14 174 (by decide) (by decide)
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
        exact rec3466 14 174 (by decide) (by decide)
      · right
        exact rec3470 14 174 (by decide) (by decide)
      · right
        exact rec3474 14 174 (by decide) (by decide)
      · right
        exact rec3478 14 174 (by decide) (by decide)
      · right
        exact rec3482 14 174 (by decide) (by decide)
      · right
        exact rec3486 14 174 (by decide) (by decide)
      · right
        exact rec3490 14 174 (by decide) (by decide)
      · right
        exact rec3494 14 174 (by decide) (by decide)
      · right
        exact rec3498 14 174 (by decide) (by decide)
      · right
        exact rec3502 14 174 (by decide) (by decide)
      · right
        exact rec3506 14 174 (by decide) (by decide)
      · right
        exact rec3510 14 174 (by decide) (by decide)
      · right
        exact rec3514 14 174 (by decide) (by decide)
      · right
        exact rec3518 14 174 (by decide) (by decide)
      · right
        exact rec3522 14 174 (by decide) (by decide)
      · right
        exact rec3526 14 174 (by decide) (by decide)
      · right
        exact rec3530 14 174 (by decide) (by decide)
      · right
        exact rec3534 14 174 (by decide) (by decide)
      · right
        exact rec3538 14 174 (by decide) (by decide)
      · right
        exact rec3542 14 174 (by decide) (by decide)
      · right
        exact rec3546 14 174 (by decide) (by decide)
      · right
        exact rec3550 14 174 (by decide) (by decide)
      · right
        exact rec3554 14 174 (by decide) (by decide)
      · right
        exact rec3558 14 174 (by decide) (by decide)
      · right
        exact rec3562 14 174 (by decide) (by decide)
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
        exact rec3566 14 174 (by decide) (by decide)
      · right
        exact rec3576 14 174 (by decide) (by decide)
      · right
        exact rec3586 14 174 (by decide) (by decide)
      · right
        exact rec3597 14 174 (by decide) (by decide)
      · right
        exact rec3608 14 174 (by decide) (by decide)
      · right
        exact rec3619 14 174 (by decide) (by decide)
      · right
        exact rec3629 14 174 (by decide) (by decide)
      · right
        exact rec3641 14 174 (by decide) (by decide)
      · right
        exact rec3657 14 174 (by decide) (by decide)
      · right
        exact rec3675 14 174 (by decide) (by decide)
      · right
        exact rec3689 14 174 (by decide) (by decide)
      · right
        exact rec3699 14 174 (by decide) (by decide)
      · right
        exact rec3711 14 174 (by decide) (by decide)
      · right
        exact rec3727 14 174 (by decide) (by decide)
      · right
        exact rec3745 14 174 (by decide) (by decide)
      · right
        exact rec3759 14 174 (by decide) (by decide)
      · right
        exact rec3769 14 174 (by decide) (by decide)
      · right
        exact rec3780 14 174 (by decide) (by decide)
      · right
        exact rec3795 14 174 (by decide) (by decide)
      · right
        exact rec3812 14 174 (by decide) (by decide)
      · right
        exact rec3826 14 174 (by decide) (by decide)
      · right
        exact rec3836 14 174 (by decide) (by decide)
      · right
        exact rec3847 14 174 (by decide) (by decide)
      · right
        exact rec3862 14 174 (by decide) (by decide)
      · right
        exact rec3879 14 174 (by decide) (by decide)
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
        exact rec4152 14 174 (by decide) (by decide)
      · right
        exact rec4158 14 174 (by decide) (by decide)
      · right
        exact rec4165 14 174 (by decide) (by decide)
      · right
        exact rec4178 14 174 (by decide) (by decide)
      · right
        exact rec4185 14 174 (by decide) (by decide)
      · right
        exact rec4193 14 174 (by decide) (by decide)
      · right
        exact rec4200 14 174 (by decide) (by decide)
      · right
        exact rec4213 14 174 (by decide) (by decide)
      · right
        exact rec4222 14 174 (by decide) (by decide)
      · right
        exact rec4226 14 174 (by decide) (by decide)
      · right
        exact rec4232 14 174 (by decide) (by decide)
      · right
        exact rec4238 14 174 (by decide) (by decide)
      · right
        exact rec4246 14 174 (by decide) (by decide)
      · right
        exact rec4255 14 174 (by decide) (by decide)
      · right
        exact rec4263 14 174 (by decide) (by decide)
      · right
        exact rec4277 14 174 (by decide) (by decide)
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
        exact rec4418 14 174 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4427 14 174 (by decide) (by decide)
      · right
        exact rec4436 14 174 (by decide) (by decide)
      · right
        exact rec4447 14 174 (by decide) (by decide)
      · left
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
        exact rec4453 14 174 (by decide) (by decide)
      · right
        exact rec4462 14 174 (by decide) (by decide)
      · right
        exact rec4470 14 174 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4475 14 174 (by decide) (by decide)
  · left
    exact rec3005 14 175 (by decide) (by decide)
end Section14Coverage_14_2_p160_176

#print axioms solution
