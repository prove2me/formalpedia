-- Prove2me | solution 1 for Freiman.section14_s0002_coverage0002_parents_0176_0192
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T04:04:33.7871+00:00
-- url     : https://prove2.me/submissions/f028a05f-5fc4-466c-9ef5-8f8e33a30a12

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
namespace Section14Coverage_2_2_p176_192
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
private theorem rec3015 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[572]? = some (⟨38,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec3034 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 38 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨38,(-1),[2,6,14],[186],918⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[591]? = some (⟨38,(-1),[2,6,14],[186],918⟩) from rfl))
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
private theorem rec3213 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(0),[1,2,5,6,13,14],[190],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[770]? = some (⟨42,(0),[1,2,5,6,13,14],[190],312⟩) from rfl))
private theorem rec3224 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(1),[1,2,5,6,13,14],[190],313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[781]? = some (⟨42,(1),[1,2,5,6,13,14],[190],313⟩) from rfl))
private theorem rec3234 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(2),[1,2,5,6,13,14],[190],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[791]? = some (⟨42,(2),[1,2,5,6,13,14],[190],312⟩) from rfl))
private theorem rec3244 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(3),[1,2,5,6,13,14],[190],314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[801]? = some (⟨42,(3),[1,2,5,6,13,14],[190],314⟩) from rfl))
private theorem rec3254 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(4),[1,2,5,6,13,14],[190],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[811]? = some (⟨42,(4),[1,2,5,6,13,14],[190],315⟩) from rfl))
private theorem rec3264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(5),[1,2,5,6,13,14],[190],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[821]? = some (⟨42,(5),[1,2,5,6,13,14],[190],312⟩) from rfl))
private theorem rec3275 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(6),[1,2,5,6,13,14],[190],313⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[832]? = some (⟨42,(6),[1,2,5,6,13,14],[190],313⟩) from rfl))
private theorem rec3285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(7),[1,2,5,6,13,14],[190],312⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[842]? = some (⟨42,(7),[1,2,5,6,13,14],[190],312⟩) from rfl))
private theorem rec3295 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(8),[1,2,5,6,13,14],[190],314⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[852]? = some (⟨42,(8),[1,2,5,6,13,14],[190],314⟩) from rfl))
private theorem rec3305 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(9),[1,2,5,6,13,14],[190],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[862]? = some (⟨42,(9),[1,2,5,6,13,14],[190],315⟩) from rfl))
private theorem rec3315 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(10),[1,2,5,6,13,14],[190],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[872]? = some (⟨42,(10),[1,2,5,6,13,14],[190],316⟩) from rfl))
private theorem rec3326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(11),[1,2,5,6,13,14],[190],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[883]? = some (⟨42,(11),[1,2,5,6,13,14],[190],316⟩) from rfl))
private theorem rec3336 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(12),[1,2,5,6,13,14],[190],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[893]? = some (⟨42,(12),[1,2,5,6,13,14],[190],316⟩) from rfl))
private theorem rec3346 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(13),[1,2,5,6,13,14],[190],316⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[903]? = some (⟨42,(13),[1,2,5,6,13,14],[190],316⟩) from rfl))
private theorem rec3356 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(14),[1,2,5,6,13,14],[190],315⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[913]? = some (⟨42,(14),[1,2,5,6,13,14],[190],315⟩) from rfl))
private theorem rec3366 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(15),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[923]? = some (⟨42,(15),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3377 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(16),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[934]? = some (⟨42,(16),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3387 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(17),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[944]? = some (⟨42,(17),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3397 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(18),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[954]? = some (⟨42,(18),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3407 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(19),[1,2,5,6,13,14],[190],317⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[964]? = some (⟨42,(19),[1,2,5,6,13,14],[190],317⟩) from rfl))
private theorem rec3417 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(20),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[974]? = some (⟨42,(20),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3428 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(21),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[985]? = some (⟨42,(21),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3438 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(22),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[995]? = some (⟨42,(22),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3448 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(23),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1005]? = some (⟨42,(23),[1,2,5,6,13,14],[190],318⟩) from rfl))
private theorem rec3458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 42 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨42,(24),[1,2,5,6,13,14],[190],318⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part2 (List.mem_of_getElem? (show section14DataRecords1Part3[1015]? = some (⟨42,(24),[1,2,5,6,13,14],[190],318⟩) from rfl))
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
private theorem rec3640 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(7),[1,2,5,6,13,14],[190],319⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[1]? = some (⟨47,(7),[1,2,5,6,13,14],[190],319⟩) from rfl))
private theorem rec3656 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(8),[1,2,5,6,13,14],[190],320⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[17]? = some (⟨47,(8),[1,2,5,6,13,14],[190],320⟩) from rfl))
private theorem rec3674 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(9),[1,2,5,6,13,14],[190],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[35]? = some (⟨47,(9),[1,2,5,6,13,14],[190],321⟩) from rfl))
private theorem rec3689 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[50]? = some (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) from rfl))
private theorem rec3699 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[60]? = some (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) from rfl))
private theorem rec3710 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(12),[1,2,5,6,13,14],[190],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[71]? = some (⟨47,(12),[1,2,5,6,13,14],[190],322⟩) from rfl))
private theorem rec3726 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(13),[1,2,5,6,13,14],[190],322⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[87]? = some (⟨47,(13),[1,2,5,6,13,14],[190],322⟩) from rfl))
private theorem rec3744 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(14),[1,2,5,6,13,14],[190],321⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[105]? = some (⟨47,(14),[1,2,5,6,13,14],[190],321⟩) from rfl))
private theorem rec3759 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[120]? = some (⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩) from rfl))
private theorem rec3769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[130]? = some (⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩) from rfl))
private theorem rec3781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(17),[1,2,5,6,13,14],[190],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[142]? = some (⟨47,(17),[1,2,5,6,13,14],[190],323⟩) from rfl))
private theorem rec3796 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(18),[1,2,5,6,13,14],[190],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[157]? = some (⟨47,(18),[1,2,5,6,13,14],[190],323⟩) from rfl))
private theorem rec3813 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(19),[1,2,5,6,13,14],[190],323⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[174]? = some (⟨47,(19),[1,2,5,6,13,14],[190],323⟩) from rfl))
private theorem rec3826 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[187]? = some (⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩) from rfl))
private theorem rec3836 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[197]? = some (⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩) from rfl))
private theorem rec3848 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(22),[1,2,5,6,13,14],[190],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[209]? = some (⟨47,(22),[1,2,5,6,13,14],[190],324⟩) from rfl))
private theorem rec3863 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(23),[1,2,5,6,13,14],[190],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[224]? = some (⟨47,(23),[1,2,5,6,13,14],[190],324⟩) from rfl))
private theorem rec3880 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 47 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨47,(24),[1,2,5,6,13,14],[190],324⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[241]? = some (⟨47,(24),[1,2,5,6,13,14],[190],324⟩) from rfl))
private theorem rec3895 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(0),[1,2,5,6],[190],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[256]? = some (⟨50,(0),[1,2,5,6],[190],331⟩) from rfl))
private theorem rec3907 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(1),[1,2,5,6],[190],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[268]? = some (⟨50,(1),[1,2,5,6],[190],332⟩) from rfl))
private theorem rec3919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(2),[1,2,5,6],[190],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[280]? = some (⟨50,(2),[1,2,5,6],[190],333⟩) from rfl))
private theorem rec3931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(3),[1,2,5,6],[190],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[292]? = some (⟨50,(3),[1,2,5,6],[190],334⟩) from rfl))
private theorem rec3943 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(4),[1,2,5,6],[190],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[304]? = some (⟨50,(4),[1,2,5,6],[190],331⟩) from rfl))
private theorem rec3955 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(5),[1,2,5,6],[190],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[316]? = some (⟨50,(5),[1,2,5,6],[190],332⟩) from rfl))
private theorem rec3967 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(6),[1,2,5,6],[190],335⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[328]? = some (⟨50,(6),[1,2,5,6],[190],335⟩) from rfl))
private theorem rec3979 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(7),[1,2,5,6],[190],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[340]? = some (⟨50,(7),[1,2,5,6],[190],334⟩) from rfl))
private theorem rec3991 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(8),[1,2,5,6],[190],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[352]? = some (⟨50,(8),[1,2,5,6],[190],331⟩) from rfl))
private theorem rec4003 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(9),[1,2,5,6],[190],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[364]? = some (⟨50,(9),[1,2,5,6],[190],332⟩) from rfl))
private theorem rec4015 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(10),[1,2,5,6],[190],333⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[376]? = some (⟨50,(10),[1,2,5,6],[190],333⟩) from rfl))
private theorem rec4027 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(11),[1,2,5,6],[190],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[388]? = some (⟨50,(11),[1,2,5,6],[190],334⟩) from rfl))
private theorem rec4039 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(12),[1,2,5,6],[190],331⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[400]? = some (⟨50,(12),[1,2,5,6],[190],331⟩) from rfl))
private theorem rec4051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(13),[1,2,5,6],[190],332⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[412]? = some (⟨50,(13),[1,2,5,6],[190],332⟩) from rfl))
private theorem rec4063 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(14),[1,2,5,6],[190],336⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[424]? = some (⟨50,(14),[1,2,5,6],[190],336⟩) from rfl))
private theorem rec4075 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 50 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨50,(15),[1,2,5,6],[190],334⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[436]? = some (⟨50,(15),[1,2,5,6],[190],334⟩) from rfl))
private theorem rec4087 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 53 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(0),[1,2,5,6],[190],325⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[448]? = some (⟨53,(0),[1,2,5,6],[190],325⟩) from rfl))
private theorem rec4103 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 53 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(1),[1,2,5,6],[190],326⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[464]? = some (⟨53,(1),[1,2,5,6],[190],326⟩) from rfl))
private theorem rec4119 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 53 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(2),[1,2,5,6],[190],327⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[480]? = some (⟨53,(2),[1,2,5,6],[190],327⟩) from rfl))
private theorem rec4134 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 53 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨53,(3),[1,2,5,6],[190],328⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part3 (List.mem_of_getElem? (show section14DataRecords1Part4[495]? = some (⟨53,(3),[1,2,5,6],[190],328⟩) from rfl))
private theorem rec4151 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(0),[2],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[2]? = some (⟨55,(0),[2],[190],2⟩) from rfl))
private theorem rec4160 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(1),[2],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[11]? = some (⟨55,(1),[2],[170,174,190],2⟩) from rfl))
private theorem rec4166 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(2),[1,2,5,14],[190],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[17]? = some (⟨55,(2),[1,2,5,14],[190],29⟩) from rfl))
private theorem rec4175 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(3),[1,2,5,6,14],[190],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[26]? = some (⟨55,(3),[1,2,5,6,14],[190],234⟩) from rfl))
private theorem rec4187 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(4),[2],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[38]? = some (⟨55,(4),[2],[170,174,190],2⟩) from rfl))
private theorem rec4195 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(5),[2],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[46]? = some (⟨55,(5),[2],[170,174,190],2⟩) from rfl))
private theorem rec4201 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(6),[1,2,5,14],[190],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[52]? = some (⟨55,(6),[1,2,5,14],[190],29⟩) from rfl))
private theorem rec4210 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(7),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[61]? = some (⟨55,(7),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4220 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(8),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[71]? = some (⟨55,(8),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4226 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[77]? = some (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) from rfl))
private theorem rec4231 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(10),[1,2,5,6,13,14],[190],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[82]? = some (⟨55,(10),[1,2,5,6,13,14],[190],29⟩) from rfl))
private theorem rec4239 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(11),[1,2,5,6,13,14],[190],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[90]? = some (⟨55,(11),[1,2,5,6,13,14],[190],234⟩) from rfl))
private theorem rec4246 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(12),[1,2,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[97]? = some (⟨55,(12),[1,2,14],[170,174,190],3⟩) from rfl))
private theorem rec4255 (si parent : ℕ) (hs : si ∈ ([1, 2, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(13),[1,2,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[106]? = some (⟨55,(13),[1,2,14],[170,174,190],3⟩) from rfl))
private theorem rec4262 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(14),[1,2,5,6,13],[190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[113]? = some (⟨55,(14),[1,2,5,6,13],[190],99⟩) from rfl))
private theorem rec4271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 55 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨55,(15),[1,2,5,6,13,14],[190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[122]? = some (⟨55,(15),[1,2,5,6,13,14],[190],99⟩) from rfl))
private theorem rec4278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(0),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[129]? = some (⟨57,(0),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4284 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(1),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[135]? = some (⟨57,(1),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(2),[1,2,5,6],[190],337⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[143]? = some (⟨57,(2),[1,2,5,6],[190],337⟩) from rfl))
private theorem rec4302 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(3),[1,2,5,6],[170,174,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[153]? = some (⟨57,(3),[1,2,5,6],[170,174,190],101⟩) from rfl))
private theorem rec4308 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(4),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[159]? = some (⟨57,(4),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4314 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(5),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[165]? = some (⟨57,(5),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4322 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(6),[1,2,5,6],[190],338⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[173]? = some (⟨57,(6),[1,2,5,6],[190],338⟩) from rfl))
private theorem rec4333 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(7),[1,2,5,6],[170,174,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[184]? = some (⟨57,(7),[1,2,5,6],[170,174,190],101⟩) from rfl))
private theorem rec4339 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(8),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[190]? = some (⟨57,(8),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4345 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(9),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[196]? = some (⟨57,(9),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4353 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(10),[1,2,5,6],[190],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[204]? = some (⟨57,(10),[1,2,5,6],[190],339⟩) from rfl))
private theorem rec4364 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(11),[1,2,5,6],[170,174,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[215]? = some (⟨57,(11),[1,2,5,6],[170,174,190],101⟩) from rfl))
private theorem rec4370 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(12),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[221]? = some (⟨57,(12),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4376 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(13),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[227]? = some (⟨57,(13),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4382 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(14),[1,2,5,6],[170,174,190],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[233]? = some (⟨57,(14),[1,2,5,6],[170,174,190],286⟩) from rfl))
private theorem rec4388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(15),[1,2,5,6],[170,174,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[239]? = some (⟨57,(15),[1,2,5,6],[170,174,190],101⟩) from rfl))
private theorem rec4394 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(16),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[245]? = some (⟨57,(16),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4400 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(17),[1,2,5,6],[170,174,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[251]? = some (⟨57,(17),[1,2,5,6],[170,174,190],2⟩) from rfl))
private theorem rec4406 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(18),[1,2,5,6],[170,174,190],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[257]? = some (⟨57,(18),[1,2,5,6],[170,174,190],287⟩) from rfl))
private theorem rec4412 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 57 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨57,(19),[1,2,5,6],[170,174,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[263]? = some (⟨57,(19),[1,2,5,6],[170,174,190],101⟩) from rfl))
private theorem rec4418 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(5),[1,2,5,6,14],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[269]? = some (⟨58,(5),[1,2,5,6,14],[170,174,190],3⟩) from rfl))
private theorem rec4427 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(7),[1,2,6,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[278]? = some (⟨58,(7),[1,2,6,14],[174,190],3⟩) from rfl))
private theorem rec4436 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(8),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[287]? = some (⟨58,(8),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4445 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(9),[1,2],[170,174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[296]? = some (⟨58,(9),[1,2],[170,174,190],3⟩) from rfl))
private theorem rec4453 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(15),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[304]? = some (⟨58,(15),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4462 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(16),[1,2,5,6,13,14],[174,190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[313]? = some (⟨58,(16),[1,2,5,6,13,14],[174,190],3⟩) from rfl))
private theorem rec4470 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170, 174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(17),[1,2,5,6,13,14],[170,174,190],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[321]? = some (⟨58,(17),[1,2,5,6,13,14],[170,174,190],48⟩) from rfl))
private theorem rec4475 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174, 190] : List ℕ)) : section14Recorded section14Catalog si parent 58 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨58,(19),[1,2,5,6,13,14],[174,190],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[326]? = some (⟨58,(19),[1,2,5,6,13,14],[174,190],143⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 2).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 176).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 2).plans.drop 2).take 1 = [⟨3,38,[([1],[]),([2],[]),([3],[1])],false,[(39,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(54,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(56,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec3015 2 176 (by decide) (by decide)
  · left
    exact rec3015 2 177 (by decide) (by decide)
  · left
    exact rec2997 2 178 (by decide) (by decide)
  · left
    exact rec2997 2 179 (by decide) (by decide)
  · left
    exact rec3015 2 180 (by decide) (by decide)
  · left
    exact rec3015 2 181 (by decide) (by decide)
  · left
    exact rec2997 2 182 (by decide) (by decide)
  · left
    exact rec2997 2 183 (by decide) (by decide)
  · left
    exact rec2996 2 184 (by decide) (by decide)
  · left
    exact rec2996 2 185 (by decide) (by decide)
  · left
    exact rec3034 2 186 (by decide) (by decide)
  · left
    exact rec3004 2 187 (by decide) (by decide)
  · left
    exact rec2996 2 188 (by decide) (by decide)
  · left
    exact rec2996 2 189 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(39,⟨([1],[]),true,([1],[]),false,false,[]⟩),(40,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(41,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(44,⟨([2],[]),true,([2],[]),false,false,[]⟩),(45,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(46,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(54,⟨([1],[]),true,([2],[]),false,false,[]⟩),(55,⟨([2],[]),true,([1],[]),false,false,[]⟩),(56,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(58,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
        exact rec3086 2 190 (by decide) (by decide)
      · right
        exact rec3091 2 190 (by decide) (by decide)
      · right
        exact rec3096 2 190 (by decide) (by decide)
      · right
        exact rec3101 2 190 (by decide) (by decide)
      · right
        exact rec3106 2 190 (by decide) (by decide)
      · right
        exact rec3111 2 190 (by decide) (by decide)
      · right
        exact rec3116 2 190 (by decide) (by decide)
      · right
        exact rec3121 2 190 (by decide) (by decide)
      · right
        exact rec3126 2 190 (by decide) (by decide)
      · right
        exact rec3131 2 190 (by decide) (by decide)
      · right
        exact rec3136 2 190 (by decide) (by decide)
      · right
        exact rec3141 2 190 (by decide) (by decide)
      · right
        exact rec3146 2 190 (by decide) (by decide)
      · right
        exact rec3151 2 190 (by decide) (by decide)
      · right
        exact rec3156 2 190 (by decide) (by decide)
      · right
        exact rec3161 2 190 (by decide) (by decide)
      · right
        exact rec3166 2 190 (by decide) (by decide)
      · right
        exact rec3171 2 190 (by decide) (by decide)
      · right
        exact rec3176 2 190 (by decide) (by decide)
      · right
        exact rec3181 2 190 (by decide) (by decide)
      · right
        exact rec3186 2 190 (by decide) (by decide)
      · right
        exact rec3191 2 190 (by decide) (by decide)
      · right
        exact rec3196 2 190 (by decide) (by decide)
      · right
        exact rec3201 2 190 (by decide) (by decide)
      · right
        exact rec3206 2 190 (by decide) (by decide)
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
        exact rec3213 2 190 (by decide) (by decide)
      · right
        exact rec3224 2 190 (by decide) (by decide)
      · right
        exact rec3234 2 190 (by decide) (by decide)
      · right
        exact rec3244 2 190 (by decide) (by decide)
      · right
        exact rec3254 2 190 (by decide) (by decide)
      · right
        exact rec3264 2 190 (by decide) (by decide)
      · right
        exact rec3275 2 190 (by decide) (by decide)
      · right
        exact rec3285 2 190 (by decide) (by decide)
      · right
        exact rec3295 2 190 (by decide) (by decide)
      · right
        exact rec3305 2 190 (by decide) (by decide)
      · right
        exact rec3315 2 190 (by decide) (by decide)
      · right
        exact rec3326 2 190 (by decide) (by decide)
      · right
        exact rec3336 2 190 (by decide) (by decide)
      · right
        exact rec3346 2 190 (by decide) (by decide)
      · right
        exact rec3356 2 190 (by decide) (by decide)
      · right
        exact rec3366 2 190 (by decide) (by decide)
      · right
        exact rec3377 2 190 (by decide) (by decide)
      · right
        exact rec3387 2 190 (by decide) (by decide)
      · right
        exact rec3397 2 190 (by decide) (by decide)
      · right
        exact rec3407 2 190 (by decide) (by decide)
      · right
        exact rec3417 2 190 (by decide) (by decide)
      · right
        exact rec3428 2 190 (by decide) (by decide)
      · right
        exact rec3438 2 190 (by decide) (by decide)
      · right
        exact rec3448 2 190 (by decide) (by decide)
      · right
        exact rec3458 2 190 (by decide) (by decide)
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
        exact rec3466 2 190 (by decide) (by decide)
      · right
        exact rec3470 2 190 (by decide) (by decide)
      · right
        exact rec3474 2 190 (by decide) (by decide)
      · right
        exact rec3478 2 190 (by decide) (by decide)
      · right
        exact rec3482 2 190 (by decide) (by decide)
      · right
        exact rec3486 2 190 (by decide) (by decide)
      · right
        exact rec3490 2 190 (by decide) (by decide)
      · right
        exact rec3494 2 190 (by decide) (by decide)
      · right
        exact rec3498 2 190 (by decide) (by decide)
      · right
        exact rec3502 2 190 (by decide) (by decide)
      · right
        exact rec3506 2 190 (by decide) (by decide)
      · right
        exact rec3510 2 190 (by decide) (by decide)
      · right
        exact rec3514 2 190 (by decide) (by decide)
      · right
        exact rec3518 2 190 (by decide) (by decide)
      · right
        exact rec3522 2 190 (by decide) (by decide)
      · right
        exact rec3526 2 190 (by decide) (by decide)
      · right
        exact rec3530 2 190 (by decide) (by decide)
      · right
        exact rec3534 2 190 (by decide) (by decide)
      · right
        exact rec3538 2 190 (by decide) (by decide)
      · right
        exact rec3542 2 190 (by decide) (by decide)
      · right
        exact rec3546 2 190 (by decide) (by decide)
      · right
        exact rec3550 2 190 (by decide) (by decide)
      · right
        exact rec3554 2 190 (by decide) (by decide)
      · right
        exact rec3558 2 190 (by decide) (by decide)
      · right
        exact rec3562 2 190 (by decide) (by decide)
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
        exact rec3566 2 190 (by decide) (by decide)
      · right
        exact rec3576 2 190 (by decide) (by decide)
      · right
        exact rec3586 2 190 (by decide) (by decide)
      · right
        exact rec3597 2 190 (by decide) (by decide)
      · right
        exact rec3608 2 190 (by decide) (by decide)
      · right
        exact rec3619 2 190 (by decide) (by decide)
      · right
        exact rec3629 2 190 (by decide) (by decide)
      · right
        exact rec3640 2 190 (by decide) (by decide)
      · right
        exact rec3656 2 190 (by decide) (by decide)
      · right
        exact rec3674 2 190 (by decide) (by decide)
      · right
        exact rec3689 2 190 (by decide) (by decide)
      · right
        exact rec3699 2 190 (by decide) (by decide)
      · right
        exact rec3710 2 190 (by decide) (by decide)
      · right
        exact rec3726 2 190 (by decide) (by decide)
      · right
        exact rec3744 2 190 (by decide) (by decide)
      · right
        exact rec3759 2 190 (by decide) (by decide)
      · right
        exact rec3769 2 190 (by decide) (by decide)
      · right
        exact rec3781 2 190 (by decide) (by decide)
      · right
        exact rec3796 2 190 (by decide) (by decide)
      · right
        exact rec3813 2 190 (by decide) (by decide)
      · right
        exact rec3826 2 190 (by decide) (by decide)
      · right
        exact rec3836 2 190 (by decide) (by decide)
      · right
        exact rec3848 2 190 (by decide) (by decide)
      · right
        exact rec3863 2 190 (by decide) (by decide)
      · right
        exact rec3880 2 190 (by decide) (by decide)
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 49)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 50)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec3895 2 190 (by decide) (by decide)
      · right
        exact rec3907 2 190 (by decide) (by decide)
      · right
        exact rec3919 2 190 (by decide) (by decide)
      · right
        exact rec3931 2 190 (by decide) (by decide)
      · right
        exact rec3943 2 190 (by decide) (by decide)
      · right
        exact rec3955 2 190 (by decide) (by decide)
      · right
        exact rec3967 2 190 (by decide) (by decide)
      · right
        exact rec3979 2 190 (by decide) (by decide)
      · right
        exact rec3991 2 190 (by decide) (by decide)
      · right
        exact rec4003 2 190 (by decide) (by decide)
      · right
        exact rec4015 2 190 (by decide) (by decide)
      · right
        exact rec4027 2 190 (by decide) (by decide)
      · right
        exact rec4039 2 190 (by decide) (by decide)
      · right
        exact rec4051 2 190 (by decide) (by decide)
      · right
        exact rec4063 2 190 (by decide) (by decide)
      · right
        exact rec4075 2 190 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 51)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 52)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 53)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4087 2 190 (by decide) (by decide)
      · right
        exact rec4103 2 190 (by decide) (by decide)
      · right
        exact rec4119 2 190 (by decide) (by decide)
      · right
        exact rec4134 2 190 (by decide) (by decide)
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
        exact rec4151 2 190 (by decide) (by decide)
      · right
        exact rec4160 2 190 (by decide) (by decide)
      · right
        exact rec4166 2 190 (by decide) (by decide)
      · right
        exact rec4175 2 190 (by decide) (by decide)
      · right
        exact rec4187 2 190 (by decide) (by decide)
      · right
        exact rec4195 2 190 (by decide) (by decide)
      · right
        exact rec4201 2 190 (by decide) (by decide)
      · right
        exact rec4210 2 190 (by decide) (by decide)
      · right
        exact rec4220 2 190 (by decide) (by decide)
      · right
        exact rec4226 2 190 (by decide) (by decide)
      · right
        exact rec4231 2 190 (by decide) (by decide)
      · right
        exact rec4239 2 190 (by decide) (by decide)
      · right
        exact rec4246 2 190 (by decide) (by decide)
      · right
        exact rec4255 2 190 (by decide) (by decide)
      · right
        exact rec4262 2 190 (by decide) (by decide)
      · right
        exact rec4271 2 190 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 56)).length = 8 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 57)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4278 2 190 (by decide) (by decide)
      · right
        exact rec4284 2 190 (by decide) (by decide)
      · right
        exact rec4292 2 190 (by decide) (by decide)
      · right
        exact rec4302 2 190 (by decide) (by decide)
      · right
        exact rec4308 2 190 (by decide) (by decide)
      · right
        exact rec4314 2 190 (by decide) (by decide)
      · right
        exact rec4322 2 190 (by decide) (by decide)
      · right
        exact rec4333 2 190 (by decide) (by decide)
      · right
        exact rec4339 2 190 (by decide) (by decide)
      · right
        exact rec4345 2 190 (by decide) (by decide)
      · right
        exact rec4353 2 190 (by decide) (by decide)
      · right
        exact rec4364 2 190 (by decide) (by decide)
      · right
        exact rec4370 2 190 (by decide) (by decide)
      · right
        exact rec4376 2 190 (by decide) (by decide)
      · right
        exact rec4382 2 190 (by decide) (by decide)
      · right
        exact rec4388 2 190 (by decide) (by decide)
      · right
        exact rec4394 2 190 (by decide) (by decide)
      · right
        exact rec4400 2 190 (by decide) (by decide)
      · right
        exact rec4406 2 190 (by decide) (by decide)
      · right
        exact rec4412 2 190 (by decide) (by decide)
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
        exact rec4418 2 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4427 2 190 (by decide) (by decide)
      · right
        exact rec4436 2 190 (by decide) (by decide)
      · right
        exact rec4445 2 190 (by decide) (by decide)
      · left
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
        exact rec4453 2 190 (by decide) (by decide)
      · right
        exact rec4462 2 190 (by decide) (by decide)
      · right
        exact rec4470 2 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec4475 2 190 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 59)).length = 10 := by decide +kernel
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
  · left
    exact rec3013 2 191 (by decide) (by decide)
end Section14Coverage_2_2_p176_192

#print axioms solution
