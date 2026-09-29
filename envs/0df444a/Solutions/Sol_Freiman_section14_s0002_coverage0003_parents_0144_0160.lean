-- Prove2me | solution 1 for Freiman.section14_s0002_coverage0003_parents_0144_0160
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T04:14:19.980281+00:00
-- url     : https://prove2.me/submissions/fbe28a30-7ef4-4432-ab2b-e2b81c565710

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
namespace Section14Coverage_2_3_p144_160
private theorem rec4487 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[338]? = some (⟨60,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec4488 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[339]? = some (⟨60,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec4503 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[147,151],345⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[354]? = some (⟨60,(-1),[1,2,5,6,13,14],[147,151],345⟩) from rfl))
private theorem rec4504 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([146] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[146],346⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[355]? = some (⟨60,(-1),[1,2,5,6,13,14],[146],346⟩) from rfl))
private theorem rec4508 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[359]? = some (⟨60,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec4608 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(0),[1,2,5,6],[150],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[459]? = some (⟨62,(0),[1,2,5,6],[150],347⟩) from rfl))
private theorem rec4612 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(1),[1,2,5,6],[150],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[463]? = some (⟨62,(1),[1,2,5,6],[150],347⟩) from rfl))
private theorem rec4616 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(2),[1,2,5,6],[150],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[467]? = some (⟨62,(2),[1,2,5,6],[150],347⟩) from rfl))
private theorem rec4620 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(3),[1,2,5,6],[150],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[471]? = some (⟨62,(3),[1,2,5,6],[150],347⟩) from rfl))
private theorem rec4624 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(4),[1,2,5,6],[150],347⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[475]? = some (⟨62,(4),[1,2,5,6],[150],347⟩) from rfl))
private theorem rec4628 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(5),[1,2,5,6],[150],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[479]? = some (⟨62,(5),[1,2,5,6],[150],348⟩) from rfl))
private theorem rec4632 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(6),[1,2,5,6],[150],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[483]? = some (⟨62,(6),[1,2,5,6],[150],348⟩) from rfl))
private theorem rec4636 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(7),[1,2,5,6],[150],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[487]? = some (⟨62,(7),[1,2,5,6],[150],348⟩) from rfl))
private theorem rec4640 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(8),[1,2,5,6],[150],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[491]? = some (⟨62,(8),[1,2,5,6],[150],348⟩) from rfl))
private theorem rec4644 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(9),[1,2,5,6],[150],348⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[495]? = some (⟨62,(9),[1,2,5,6],[150],348⟩) from rfl))
private theorem rec4648 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(10),[1,2,5,6],[150],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[499]? = some (⟨62,(10),[1,2,5,6],[150],349⟩) from rfl))
private theorem rec4652 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(11),[1,2,5,6],[150],350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[503]? = some (⟨62,(11),[1,2,5,6],[150],350⟩) from rfl))
private theorem rec4656 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(12),[1,2,5,6],[150],351⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[507]? = some (⟨62,(12),[1,2,5,6],[150],351⟩) from rfl))
private theorem rec4660 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(13),[1,2,5,6],[150],350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[511]? = some (⟨62,(13),[1,2,5,6],[150],350⟩) from rfl))
private theorem rec4664 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(14),[1,2,5,6],[150],352⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[515]? = some (⟨62,(14),[1,2,5,6],[150],352⟩) from rfl))
private theorem rec4668 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(15),[1,2,5,6],[150],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[519]? = some (⟨62,(15),[1,2,5,6],[150],349⟩) from rfl))
private theorem rec4672 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(16),[1,2,5,6],[150],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[523]? = some (⟨62,(16),[1,2,5,6],[150],353⟩) from rfl))
private theorem rec4676 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(17),[1,2,5,6],[150],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[527]? = some (⟨62,(17),[1,2,5,6],[150],353⟩) from rfl))
private theorem rec4680 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(18),[1,2,5,6],[150],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[531]? = some (⟨62,(18),[1,2,5,6],[150],353⟩) from rfl))
private theorem rec4684 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(19),[1,2,5,6],[150],353⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[535]? = some (⟨62,(19),[1,2,5,6],[150],353⟩) from rfl))
private theorem rec4688 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(20),[1,2,5,6],[150],349⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[539]? = some (⟨62,(20),[1,2,5,6],[150],349⟩) from rfl))
private theorem rec4692 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(21),[1,2,5,6],[150],350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[543]? = some (⟨62,(21),[1,2,5,6],[150],350⟩) from rfl))
private theorem rec4696 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(22),[1,2,5,6],[150],351⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[547]? = some (⟨62,(22),[1,2,5,6],[150],351⟩) from rfl))
private theorem rec4700 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(23),[1,2,5,6],[150],350⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[551]? = some (⟨62,(23),[1,2,5,6],[150],350⟩) from rfl))
private theorem rec4704 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 62 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(24),[1,2,5,6],[150],352⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[555]? = some (⟨62,(24),[1,2,5,6],[150],352⟩) from rfl))
private theorem rec4708 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(0),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[559]? = some (⟨64,(0),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4714 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(1),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[565]? = some (⟨64,(1),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4720 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(2),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[571]? = some (⟨64,(2),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4726 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(3),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[577]? = some (⟨64,(3),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(4),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[583]? = some (⟨64,(4),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4738 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(5),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[589]? = some (⟨64,(5),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4744 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(6),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[595]? = some (⟨64,(6),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4750 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(7),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[601]? = some (⟨64,(7),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4756 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(8),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[607]? = some (⟨64,(8),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4762 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(9),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[613]? = some (⟨64,(9),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4768 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(10),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[619]? = some (⟨64,(10),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4774 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(11),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[625]? = some (⟨64,(11),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4780 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(12),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[631]? = some (⟨64,(12),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4786 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(13),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[637]? = some (⟨64,(13),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4792 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(14),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[643]? = some (⟨64,(14),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4798 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(15),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[649]? = some (⟨64,(15),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4804 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(16),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[655]? = some (⟨64,(16),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4810 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(17),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[661]? = some (⟨64,(17),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4816 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(18),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[667]? = some (⟨64,(18),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4822 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(19),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[673]? = some (⟨64,(19),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4828 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(20),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[679]? = some (⟨64,(20),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4834 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(21),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[685]? = some (⟨64,(21),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4840 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(22),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[691]? = some (⟨64,(22),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4846 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(23),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[697]? = some (⟨64,(23),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4852 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 64 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(24),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[703]? = some (⟨64,(24),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec4858 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(0),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[709]? = some (⟨67,(0),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4861 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(1),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[712]? = some (⟨67,(1),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4864 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(2),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[715]? = some (⟨67,(2),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4867 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(3),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[718]? = some (⟨67,(3),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4870 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(4),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[721]? = some (⟨67,(4),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4873 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(5),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[724]? = some (⟨67,(5),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4876 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(6),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[727]? = some (⟨67,(6),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4879 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(7),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[730]? = some (⟨67,(7),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4882 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(8),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[733]? = some (⟨67,(8),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4885 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(9),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[736]? = some (⟨67,(9),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4888 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(10),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[739]? = some (⟨67,(10),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4891 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(11),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[742]? = some (⟨67,(11),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4894 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(12),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[745]? = some (⟨67,(12),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4897 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(13),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[748]? = some (⟨67,(13),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4900 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(14),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[751]? = some (⟨67,(14),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4903 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(15),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[754]? = some (⟨67,(15),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4906 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(16),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[757]? = some (⟨67,(16),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4909 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(17),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[760]? = some (⟨67,(17),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4912 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(18),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[763]? = some (⟨67,(18),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4915 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(19),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[766]? = some (⟨67,(19),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4918 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(20),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[769]? = some (⟨67,(20),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4921 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(21),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[772]? = some (⟨67,(21),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4924 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(22),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[775]? = some (⟨67,(22),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4927 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(23),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[778]? = some (⟨67,(23),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 67 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(24),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[781]? = some (⟨67,(24),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec4933 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(0),[1,2,5,6],[150],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[784]? = some (⟨69,(0),[1,2,5,6],[150],189⟩) from rfl))
private theorem rec4941 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(1),[1,2,5,6],[150],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[792]? = some (⟨69,(1),[1,2,5,6],[150],190⟩) from rfl))
private theorem rec4950 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[1,2,5,6],[150],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[801]? = some (⟨69,(2),[1,2,5,6],[150],191⟩) from rfl))
private theorem rec4962 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[1,2,5,6],[150],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[813]? = some (⟨69,(3),[1,2,5,6],[150],192⟩) from rfl))
private theorem rec4974 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[1,2,5,6],[150],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[825]? = some (⟨69,(4),[1,2,5,6],[150],193⟩) from rfl))
private theorem rec4986 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(5),[1,2,5,6],[150],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[837]? = some (⟨69,(5),[1,2,5,6],[150],189⟩) from rfl))
private theorem rec4994 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(6),[1,2,5,6],[150],190⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[845]? = some (⟨69,(6),[1,2,5,6],[150],190⟩) from rfl))
private theorem rec5003 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[1,2,5,6],[150],191⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[854]? = some (⟨69,(7),[1,2,5,6],[150],191⟩) from rfl))
private theorem rec5013 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[1,2,5,6],[150],192⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[864]? = some (⟨69,(8),[1,2,5,6],[150],192⟩) from rfl))
private theorem rec5023 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[1,2,5,6],[150],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[874]? = some (⟨69,(9),[1,2,5,6],[150],193⟩) from rfl))
private theorem rec5033 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(10),[1,2,5,6],[150],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[884]? = some (⟨69,(10),[1,2,5,6],[150],194⟩) from rfl))
private theorem rec5041 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(11),[1,2,5,6],[150],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[892]? = some (⟨69,(11),[1,2,5,6],[150],195⟩) from rfl))
private theorem rec5050 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[1,2,5,6],[150],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[901]? = some (⟨69,(12),[1,2,5,6],[150],195⟩) from rfl))
private theorem rec5060 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[1,2,5,6],[150],195⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[911]? = some (⟨69,(13),[1,2,5,6],[150],195⟩) from rfl))
private theorem rec5070 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[1,2,5,6],[150],193⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[921]? = some (⟨69,(14),[1,2,5,6],[150],193⟩) from rfl))
private theorem rec5080 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(15),[1,2,5,6],[150],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[931]? = some (⟨69,(15),[1,2,5,6],[150],196⟩) from rfl))
private theorem rec5088 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(16),[1,2,5,6],[150],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[939]? = some (⟨69,(16),[1,2,5,6],[150],197⟩) from rfl))
private theorem rec5097 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[1,2,5,6],[150],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[948]? = some (⟨69,(17),[1,2,5,6],[150],197⟩) from rfl))
private theorem rec5107 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[1,2,5,6],[150],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[958]? = some (⟨69,(18),[1,2,5,6],[150],197⟩) from rfl))
private theorem rec5117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[1,2,5,6],[150],197⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[968]? = some (⟨69,(19),[1,2,5,6],[150],197⟩) from rfl))
private theorem rec5127 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(20),[1,2,5,6],[150],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[978]? = some (⟨69,(20),[1,2,5,6],[150],198⟩) from rfl))
private theorem rec5135 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(21),[1,2,5,6],[150],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[986]? = some (⟨69,(21),[1,2,5,6],[150],199⟩) from rfl))
private theorem rec5144 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[1,2,5,6],[150],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[995]? = some (⟨69,(22),[1,2,5,6],[150],199⟩) from rfl))
private theorem rec5154 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[1,2,5,6],[150],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1005]? = some (⟨69,(23),[1,2,5,6],[150],199⟩) from rfl))
private theorem rec5164 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[1,2,5,6],[150],199⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1015]? = some (⟨69,(24),[1,2,5,6],[150],199⟩) from rfl))
private theorem rec5175 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(0),[1,2,5,6],[150],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1026]? = some (⟨72,(0),[1,2,5,6],[150],354⟩) from rfl))
private theorem rec5183 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(1),[1,2,5,6],[150],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1034]? = some (⟨72,(1),[1,2,5,6],[150],355⟩) from rfl))
private theorem rec5191 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(2),[1,2,5,6],[150],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1042]? = some (⟨72,(2),[1,2,5,6],[150],356⟩) from rfl))
private theorem rec5199 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(3),[1,2,5,6],[150],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1050]? = some (⟨72,(3),[1,2,5,6],[150],357⟩) from rfl))
private theorem rec5207 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(4),[1,2,5,6],[150],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1058]? = some (⟨72,(4),[1,2,5,6],[150],354⟩) from rfl))
private theorem rec5215 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(5),[1,2,5,6],[150],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1066]? = some (⟨72,(5),[1,2,5,6],[150],355⟩) from rfl))
private theorem rec5223 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(6),[1,2,5,6],[150],358⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1074]? = some (⟨72,(6),[1,2,5,6],[150],358⟩) from rfl))
private theorem rec5231 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(7),[1,2,5,6],[150],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1082]? = some (⟨72,(7),[1,2,5,6],[150],357⟩) from rfl))
private theorem rec5239 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(8),[1,2,5,6],[150],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1090]? = some (⟨72,(8),[1,2,5,6],[150],354⟩) from rfl))
private theorem rec5247 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(9),[1,2,5,6],[150],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1098]? = some (⟨72,(9),[1,2,5,6],[150],355⟩) from rfl))
private theorem rec5255 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(10),[1,2,5,6],[150],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1106]? = some (⟨72,(10),[1,2,5,6],[150],356⟩) from rfl))
private theorem rec5263 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(11),[1,2,5,6],[150],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1114]? = some (⟨72,(11),[1,2,5,6],[150],357⟩) from rfl))
private theorem rec5271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(12),[1,2,5,6],[150],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1122]? = some (⟨72,(12),[1,2,5,6],[150],354⟩) from rfl))
private theorem rec5279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(13),[1,2,5,6],[150],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1130]? = some (⟨72,(13),[1,2,5,6],[150],355⟩) from rfl))
private theorem rec5287 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(14),[1,2,5,6],[150],359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1138]? = some (⟨72,(14),[1,2,5,6],[150],359⟩) from rfl))
private theorem rec5295 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 72 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(15),[1,2,5,6],[150],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1146]? = some (⟨72,(15),[1,2,5,6],[150],357⟩) from rfl))
private theorem rec5302 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[1,2,5,6],[150],360⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1153]? = some (⟨75,(0),[1,2,5,6],[150],360⟩) from rfl))
private theorem rec5312 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[1,2,5,6],[150],361⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1163]? = some (⟨75,(1),[1,2,5,6],[150],361⟩) from rfl))
private theorem rec5322 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[1,2,5,6],[150],362⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1173]? = some (⟨75,(2),[1,2,5,6],[150],362⟩) from rfl))
private theorem rec5332 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[1,2,5,6],[150],363⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1183]? = some (⟨75,(3),[1,2,5,6],[150],363⟩) from rfl))
private theorem rec5344 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(0),[2],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1195]? = some (⟨77,(0),[2],[150,190],2⟩) from rfl))
private theorem rec5352 (si parent : ℕ) (hs : si ∈ ([2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(1),[2,5,6],[150],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1203]? = some (⟨77,(1),[2,5,6],[150],159⟩) from rfl))
private theorem rec5358 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(2),[2],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1209]? = some (⟨77,(2),[2],[150],2⟩) from rfl))
private theorem rec5366 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(3),[2],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1217]? = some (⟨77,(3),[2],[150],2⟩) from rfl))
private theorem rec5373 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(4),[2],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1224]? = some (⟨77,(4),[2],[150,190],2⟩) from rfl))
private theorem rec5378 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(5),[1,2,5,6],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[3]? = some (⟨77,(5),[1,2,5,6],[150],2⟩) from rfl))
private theorem rec5386 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(6),[2],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[11]? = some (⟨77,(6),[2],[150],2⟩) from rfl))
private theorem rec5394 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(7),[2],[150],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[19]? = some (⟨77,(7),[2],[150],2⟩) from rfl))
private theorem rec5398 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(8),[1,2,5,6],[150],98⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[23]? = some (⟨77,(8),[1,2,5,6],[150],98⟩) from rfl))
private theorem rec5402 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(9),[1,2,5,6],[150],159⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[27]? = some (⟨77,(9),[1,2,5,6],[150],159⟩) from rfl))
private theorem rec5406 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(10),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[31]? = some (⟨77,(10),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec5410 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(11),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[35]? = some (⟨77,(11),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec5414 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(12),[1,2,5,6],[150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[39]? = some (⟨77,(12),[1,2,5,6],[150],99⟩) from rfl))
private theorem rec5421 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(13),[1,2,5,6],[150],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[46]? = some (⟨77,(13),[1,2,5,6],[150],99⟩) from rfl))
private theorem rec5427 (si parent : ℕ) (hs : si ∈ ([1, 2, 5] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(14),[1,2,5],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[52]? = some (⟨77,(14),[1,2,5],[150],3⟩) from rfl))
private theorem rec5433 (si parent : ℕ) (hs : si ∈ ([1, 2, 5] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 77 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(15),[1,2,5],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[58]? = some (⟨77,(15),[1,2,5],[150],3⟩) from rfl))
private theorem rec5438 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(0),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[63]? = some (⟨79,(0),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5441 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(1),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[66]? = some (⟨79,(1),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5445 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 79 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(2),[1,2,5,6],[150],364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[70]? = some (⟨79,(2),[1,2,5,6],[150],364⟩) from rfl))
private theorem rec5452 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(3),[1,2,5,6],[150,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[77]? = some (⟨79,(3),[1,2,5,6],[150,190],101⟩) from rfl))
private theorem rec5455 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(4),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[80]? = some (⟨79,(4),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(5),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[83]? = some (⟨79,(5),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5462 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 79 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(6),[1,2,5,6],[150],365⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[87]? = some (⟨79,(6),[1,2,5,6],[150],365⟩) from rfl))
private theorem rec5469 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(7),[1,2,5,6],[150,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[94]? = some (⟨79,(7),[1,2,5,6],[150,190],101⟩) from rfl))
private theorem rec5472 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(8),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[97]? = some (⟨79,(8),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5475 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(9),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[100]? = some (⟨79,(9),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5478 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(10),[1,2,5,6],[150,190],339⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[103]? = some (⟨79,(10),[1,2,5,6],[150,190],339⟩) from rfl))
private theorem rec5483 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(11),[1,2,5,6],[150,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[108]? = some (⟨79,(11),[1,2,5,6],[150,190],101⟩) from rfl))
private theorem rec5486 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(12),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[111]? = some (⟨79,(12),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5489 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(13),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[114]? = some (⟨79,(13),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5492 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(14),[1,2,5,6],[150,190],286⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[117]? = some (⟨79,(14),[1,2,5,6],[150,190],286⟩) from rfl))
private theorem rec5495 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(15),[1,2,5,6],[150,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[120]? = some (⟨79,(15),[1,2,5,6],[150,190],101⟩) from rfl))
private theorem rec5498 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(16),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[123]? = some (⟨79,(16),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5501 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(17),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[126]? = some (⟨79,(17),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5504 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(18),[1,2,5,6],[150,190],287⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[129]? = some (⟨79,(18),[1,2,5,6],[150,190],287⟩) from rfl))
private theorem rec5509 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(19),[1,2,5,6],[150,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[134]? = some (⟨79,(19),[1,2,5,6],[150,190],101⟩) from rfl))
private theorem rec5512 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 80 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(5),[1,2,5,6],[150],105⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[137]? = some (⟨80,(5),[1,2,5,6],[150],105⟩) from rfl))
private theorem rec5517 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 80 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(7),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[142]? = some (⟨80,(7),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec5523 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 80 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(8),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[148]? = some (⟨80,(8),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec5528 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 80 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(9),[1,2,5,6],[150],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[153]? = some (⟨80,(9),[1,2,5,6],[150],143⟩) from rfl))
private theorem rec5533 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 80 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(15),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[158]? = some (⟨80,(15),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec5537 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 80 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(16),[1,2,5,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[162]? = some (⟨80,(16),[1,2,5,6],[150],3⟩) from rfl))
private theorem rec5542 (si parent : ℕ) (hs : si ∈ ([1, 2, 6] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 80 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(17),[1,2,6],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[167]? = some (⟨80,(17),[1,2,6],[150],3⟩) from rfl))
private theorem rec5547 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([150] : List ℕ)) : section14Recorded section14Catalog si parent 80 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(19),[1,2],[150],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[172]? = some (⟨80,(19),[1,2],[150],3⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 144).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 2).plans.drop 3).take 1 = [⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(61,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(76,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
  rw [hplan]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  have hparents : ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 144).take 16 = [⟨1,144,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩,⟨false,true,7⟩]⟩,⟨1,145,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,146,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,147,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,7⟩]⟩,⟨1,148,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,149,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,5⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,150,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,151,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,false,7⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,152,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,153,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,154,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,155,[⟨true,true,1⟩,⟨true,true,11⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,156,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩,⟨false,true,5⟩]⟩,⟨1,157,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,false,5⟩,⟨true,true,9⟩,⟨false,false,1⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,158,[⟨true,true,1⟩,⟨true,true,10⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩,⟨1,159,[⟨true,true,1⟩,⟨true,false,12⟩,⟨true,true,18⟩,⟨true,false,2⟩,⟨true,true,4⟩,⟨true,true,9⟩,⟨false,false,10⟩,⟨false,false,11⟩,⟨false,false,3⟩,⟨false,false,4⟩]⟩] := by rfl
  rw [hparents]
  intro b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    exact rec4487 2 144 (by decide) (by decide)
  · left
    exact rec4487 2 145 (by decide) (by decide)
  · left
    exact rec4504 2 146 (by decide) (by decide)
  · left
    exact rec4503 2 147 (by decide) (by decide)
  · left
    exact rec4487 2 148 (by decide) (by decide)
  · left
    exact rec4487 2 149 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(61,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(76,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 61)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 62)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4608 2 150 (by decide) (by decide)
      · right
        exact rec4612 2 150 (by decide) (by decide)
      · right
        exact rec4616 2 150 (by decide) (by decide)
      · right
        exact rec4620 2 150 (by decide) (by decide)
      · right
        exact rec4624 2 150 (by decide) (by decide)
      · right
        exact rec4628 2 150 (by decide) (by decide)
      · right
        exact rec4632 2 150 (by decide) (by decide)
      · right
        exact rec4636 2 150 (by decide) (by decide)
      · right
        exact rec4640 2 150 (by decide) (by decide)
      · right
        exact rec4644 2 150 (by decide) (by decide)
      · right
        exact rec4648 2 150 (by decide) (by decide)
      · right
        exact rec4652 2 150 (by decide) (by decide)
      · right
        exact rec4656 2 150 (by decide) (by decide)
      · right
        exact rec4660 2 150 (by decide) (by decide)
      · right
        exact rec4664 2 150 (by decide) (by decide)
      · right
        exact rec4668 2 150 (by decide) (by decide)
      · right
        exact rec4672 2 150 (by decide) (by decide)
      · right
        exact rec4676 2 150 (by decide) (by decide)
      · right
        exact rec4680 2 150 (by decide) (by decide)
      · right
        exact rec4684 2 150 (by decide) (by decide)
      · right
        exact rec4688 2 150 (by decide) (by decide)
      · right
        exact rec4692 2 150 (by decide) (by decide)
      · right
        exact rec4696 2 150 (by decide) (by decide)
      · right
        exact rec4700 2 150 (by decide) (by decide)
      · right
        exact rec4704 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 63)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 64)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4708 2 150 (by decide) (by decide)
      · right
        exact rec4714 2 150 (by decide) (by decide)
      · right
        exact rec4720 2 150 (by decide) (by decide)
      · right
        exact rec4726 2 150 (by decide) (by decide)
      · right
        exact rec4732 2 150 (by decide) (by decide)
      · right
        exact rec4738 2 150 (by decide) (by decide)
      · right
        exact rec4744 2 150 (by decide) (by decide)
      · right
        exact rec4750 2 150 (by decide) (by decide)
      · right
        exact rec4756 2 150 (by decide) (by decide)
      · right
        exact rec4762 2 150 (by decide) (by decide)
      · right
        exact rec4768 2 150 (by decide) (by decide)
      · right
        exact rec4774 2 150 (by decide) (by decide)
      · right
        exact rec4780 2 150 (by decide) (by decide)
      · right
        exact rec4786 2 150 (by decide) (by decide)
      · right
        exact rec4792 2 150 (by decide) (by decide)
      · right
        exact rec4798 2 150 (by decide) (by decide)
      · right
        exact rec4804 2 150 (by decide) (by decide)
      · right
        exact rec4810 2 150 (by decide) (by decide)
      · right
        exact rec4816 2 150 (by decide) (by decide)
      · right
        exact rec4822 2 150 (by decide) (by decide)
      · right
        exact rec4828 2 150 (by decide) (by decide)
      · right
        exact rec4834 2 150 (by decide) (by decide)
      · right
        exact rec4840 2 150 (by decide) (by decide)
      · right
        exact rec4846 2 150 (by decide) (by decide)
      · right
        exact rec4852 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 65)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 66)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 67)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4858 2 150 (by decide) (by decide)
      · right
        exact rec4861 2 150 (by decide) (by decide)
      · right
        exact rec4864 2 150 (by decide) (by decide)
      · right
        exact rec4867 2 150 (by decide) (by decide)
      · right
        exact rec4870 2 150 (by decide) (by decide)
      · right
        exact rec4873 2 150 (by decide) (by decide)
      · right
        exact rec4876 2 150 (by decide) (by decide)
      · right
        exact rec4879 2 150 (by decide) (by decide)
      · right
        exact rec4882 2 150 (by decide) (by decide)
      · right
        exact rec4885 2 150 (by decide) (by decide)
      · right
        exact rec4888 2 150 (by decide) (by decide)
      · right
        exact rec4891 2 150 (by decide) (by decide)
      · right
        exact rec4894 2 150 (by decide) (by decide)
      · right
        exact rec4897 2 150 (by decide) (by decide)
      · right
        exact rec4900 2 150 (by decide) (by decide)
      · right
        exact rec4903 2 150 (by decide) (by decide)
      · right
        exact rec4906 2 150 (by decide) (by decide)
      · right
        exact rec4909 2 150 (by decide) (by decide)
      · right
        exact rec4912 2 150 (by decide) (by decide)
      · right
        exact rec4915 2 150 (by decide) (by decide)
      · right
        exact rec4918 2 150 (by decide) (by decide)
      · right
        exact rec4921 2 150 (by decide) (by decide)
      · right
        exact rec4924 2 150 (by decide) (by decide)
      · right
        exact rec4927 2 150 (by decide) (by decide)
      · right
        exact rec4930 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 68)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 69)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec4933 2 150 (by decide) (by decide)
      · right
        exact rec4941 2 150 (by decide) (by decide)
      · right
        exact rec4950 2 150 (by decide) (by decide)
      · right
        exact rec4962 2 150 (by decide) (by decide)
      · right
        exact rec4974 2 150 (by decide) (by decide)
      · right
        exact rec4986 2 150 (by decide) (by decide)
      · right
        exact rec4994 2 150 (by decide) (by decide)
      · right
        exact rec5003 2 150 (by decide) (by decide)
      · right
        exact rec5013 2 150 (by decide) (by decide)
      · right
        exact rec5023 2 150 (by decide) (by decide)
      · right
        exact rec5033 2 150 (by decide) (by decide)
      · right
        exact rec5041 2 150 (by decide) (by decide)
      · right
        exact rec5050 2 150 (by decide) (by decide)
      · right
        exact rec5060 2 150 (by decide) (by decide)
      · right
        exact rec5070 2 150 (by decide) (by decide)
      · right
        exact rec5080 2 150 (by decide) (by decide)
      · right
        exact rec5088 2 150 (by decide) (by decide)
      · right
        exact rec5097 2 150 (by decide) (by decide)
      · right
        exact rec5107 2 150 (by decide) (by decide)
      · right
        exact rec5117 2 150 (by decide) (by decide)
      · right
        exact rec5127 2 150 (by decide) (by decide)
      · right
        exact rec5135 2 150 (by decide) (by decide)
      · right
        exact rec5144 2 150 (by decide) (by decide)
      · right
        exact rec5154 2 150 (by decide) (by decide)
      · right
        exact rec5164 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 70)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 71)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 72)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5175 2 150 (by decide) (by decide)
      · right
        exact rec5183 2 150 (by decide) (by decide)
      · right
        exact rec5191 2 150 (by decide) (by decide)
      · right
        exact rec5199 2 150 (by decide) (by decide)
      · right
        exact rec5207 2 150 (by decide) (by decide)
      · right
        exact rec5215 2 150 (by decide) (by decide)
      · right
        exact rec5223 2 150 (by decide) (by decide)
      · right
        exact rec5231 2 150 (by decide) (by decide)
      · right
        exact rec5239 2 150 (by decide) (by decide)
      · right
        exact rec5247 2 150 (by decide) (by decide)
      · right
        exact rec5255 2 150 (by decide) (by decide)
      · right
        exact rec5263 2 150 (by decide) (by decide)
      · right
        exact rec5271 2 150 (by decide) (by decide)
      · right
        exact rec5279 2 150 (by decide) (by decide)
      · right
        exact rec5287 2 150 (by decide) (by decide)
      · right
        exact rec5295 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 73)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 74)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 75)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5302 2 150 (by decide) (by decide)
      · right
        exact rec5312 2 150 (by decide) (by decide)
      · right
        exact rec5322 2 150 (by decide) (by decide)
      · right
        exact rec5332 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 76)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 77)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5344 2 150 (by decide) (by decide)
      · right
        exact rec5352 2 150 (by decide) (by decide)
      · right
        exact rec5358 2 150 (by decide) (by decide)
      · right
        exact rec5366 2 150 (by decide) (by decide)
      · right
        exact rec5373 2 150 (by decide) (by decide)
      · right
        exact rec5378 2 150 (by decide) (by decide)
      · right
        exact rec5386 2 150 (by decide) (by decide)
      · right
        exact rec5394 2 150 (by decide) (by decide)
      · right
        exact rec5398 2 150 (by decide) (by decide)
      · right
        exact rec5402 2 150 (by decide) (by decide)
      · right
        exact rec5406 2 150 (by decide) (by decide)
      · right
        exact rec5410 2 150 (by decide) (by decide)
      · right
        exact rec5414 2 150 (by decide) (by decide)
      · right
        exact rec5421 2 150 (by decide) (by decide)
      · right
        exact rec5427 2 150 (by decide) (by decide)
      · right
        exact rec5433 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 78)).length = 8 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 79)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec5438 2 150 (by decide) (by decide)
      · right
        exact rec5441 2 150 (by decide) (by decide)
      · right
        exact rec5445 2 150 (by decide) (by decide)
      · right
        exact rec5452 2 150 (by decide) (by decide)
      · right
        exact rec5455 2 150 (by decide) (by decide)
      · right
        exact rec5458 2 150 (by decide) (by decide)
      · right
        exact rec5462 2 150 (by decide) (by decide)
      · right
        exact rec5469 2 150 (by decide) (by decide)
      · right
        exact rec5472 2 150 (by decide) (by decide)
      · right
        exact rec5475 2 150 (by decide) (by decide)
      · right
        exact rec5478 2 150 (by decide) (by decide)
      · right
        exact rec5483 2 150 (by decide) (by decide)
      · right
        exact rec5486 2 150 (by decide) (by decide)
      · right
        exact rec5489 2 150 (by decide) (by decide)
      · right
        exact rec5492 2 150 (by decide) (by decide)
      · right
        exact rec5495 2 150 (by decide) (by decide)
      · right
        exact rec5498 2 150 (by decide) (by decide)
      · right
        exact rec5501 2 150 (by decide) (by decide)
      · right
        exact rec5504 2 150 (by decide) (by decide)
      · right
        exact rec5509 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 80)).length = 20 := by decide +kernel
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
        exact rec5512 2 150 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec5517 2 150 (by decide) (by decide)
      · right
        exact rec5523 2 150 (by decide) (by decide)
      · right
        exact rec5528 2 150 (by decide) (by decide)
      · left
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
        exact rec5533 2 150 (by decide) (by decide)
      · right
        exact rec5537 2 150 (by decide) (by decide)
      · right
        exact rec5542 2 150 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec5547 2 150 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 81)).length = 10 := by decide +kernel
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
    exact rec4503 2 151 (by decide) (by decide)
  · left
    exact rec4508 2 152 (by decide) (by decide)
  · left
    exact rec4508 2 153 (by decide) (by decide)
  · left
    exact rec4488 2 154 (by decide) (by decide)
  · left
    exact rec4488 2 155 (by decide) (by decide)
  · left
    exact rec4508 2 156 (by decide) (by decide)
  · left
    exact rec4508 2 157 (by decide) (by decide)
  · left
    exact rec4488 2 158 (by decide) (by decide)
  · left
    exact rec4488 2 159 (by decide) (by decide)
end Section14Coverage_2_3_p144_160

#print axioms solution
