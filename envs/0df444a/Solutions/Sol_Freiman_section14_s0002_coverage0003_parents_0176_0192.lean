-- Prove2me | solution 1 for Freiman.section14_s0002_coverage0003_parents_0176_0192
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T04:15:10.712068+00:00
-- url     : https://prove2.me/submissions/f2047792-350a-4e3b-a60a-75fdd3f028cc

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
namespace Section14Coverage_2_3_p176_192
private theorem rec4487 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[338]? = some (⟨60,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec4488 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[339]? = some (⟨60,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec4495 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([171, 187] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[171,187],206⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[346]? = some (⟨60,(-1),[1,2,5,6,13,14],[171,187],206⟩) from rfl))
private theorem rec4506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([186] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,13,14],[186],367⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[357]? = some (⟨60,(-1),[1,2,5,6,13,14],[186],367⟩) from rfl))
private theorem rec4508 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[359]? = some (⟨60,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec4513 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([191] : List ℕ)) : section14Recorded section14Catalog si parent 60 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨60,(-1),[1,2,13,14],[191],345⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[364]? = some (⟨60,(-1),[1,2,13,14],[191],345⟩) from rfl))
private theorem rec4609 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(0),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[460]? = some (⟨62,(0),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4613 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(1),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[464]? = some (⟨62,(1),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4617 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(2),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[468]? = some (⟨62,(2),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4621 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(3),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[472]? = some (⟨62,(3),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4625 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(4),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[476]? = some (⟨62,(4),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4629 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(5),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[480]? = some (⟨62,(5),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4633 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(6),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[484]? = some (⟨62,(6),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4637 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(7),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[488]? = some (⟨62,(7),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4641 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(8),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[492]? = some (⟨62,(8),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4645 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(9),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[496]? = some (⟨62,(9),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4649 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(10),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[500]? = some (⟨62,(10),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4653 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(11),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[504]? = some (⟨62,(11),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4657 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(12),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[508]? = some (⟨62,(12),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4661 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(13),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[512]? = some (⟨62,(13),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4665 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(14),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[516]? = some (⟨62,(14),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4669 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(15),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[520]? = some (⟨62,(15),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4673 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(16),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[524]? = some (⟨62,(16),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4677 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(17),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[528]? = some (⟨62,(17),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4681 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(18),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[532]? = some (⟨62,(18),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4685 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(19),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[536]? = some (⟨62,(19),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4689 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(20),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[540]? = some (⟨62,(20),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4693 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(21),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[544]? = some (⟨62,(21),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4697 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(22),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[548]? = some (⟨62,(22),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4701 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(23),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[552]? = some (⟨62,(23),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4705 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 62 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨62,(24),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[556]? = some (⟨62,(24),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec4709 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(0),[1,2,5,6,13,14],[190],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[560]? = some (⟨64,(0),[1,2,5,6,13,14],[190],368⟩) from rfl))
private theorem rec4715 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(1),[1,2,5,6,13,14],[190],369⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[566]? = some (⟨64,(1),[1,2,5,6,13,14],[190],369⟩) from rfl))
private theorem rec4721 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(2),[1,2,5,6,13,14],[190],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[572]? = some (⟨64,(2),[1,2,5,6,13,14],[190],368⟩) from rfl))
private theorem rec4727 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(3),[1,2,5,6,13,14],[190],370⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[578]? = some (⟨64,(3),[1,2,5,6,13,14],[190],370⟩) from rfl))
private theorem rec4733 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(4),[1,2,5,6,13,14],[190],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[584]? = some (⟨64,(4),[1,2,5,6,13,14],[190],371⟩) from rfl))
private theorem rec4739 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(5),[1,2,5,6,13,14],[190],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[590]? = some (⟨64,(5),[1,2,5,6,13,14],[190],368⟩) from rfl))
private theorem rec4745 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(6),[1,2,5,6,13,14],[190],369⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[596]? = some (⟨64,(6),[1,2,5,6,13,14],[190],369⟩) from rfl))
private theorem rec4751 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(7),[1,2,5,6,13,14],[190],368⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[602]? = some (⟨64,(7),[1,2,5,6,13,14],[190],368⟩) from rfl))
private theorem rec4757 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(8),[1,2,5,6,13,14],[190],370⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[608]? = some (⟨64,(8),[1,2,5,6,13,14],[190],370⟩) from rfl))
private theorem rec4763 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(9),[1,2,5,6,13,14],[190],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[614]? = some (⟨64,(9),[1,2,5,6,13,14],[190],371⟩) from rfl))
private theorem rec4769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(10),[1,2,5,6,13,14],[190],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[620]? = some (⟨64,(10),[1,2,5,6,13,14],[190],372⟩) from rfl))
private theorem rec4775 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(11),[1,2,5,6,13,14],[190],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[626]? = some (⟨64,(11),[1,2,5,6,13,14],[190],372⟩) from rfl))
private theorem rec4781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(12),[1,2,5,6,13,14],[190],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[632]? = some (⟨64,(12),[1,2,5,6,13,14],[190],372⟩) from rfl))
private theorem rec4787 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(13),[1,2,5,6,13,14],[190],372⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[638]? = some (⟨64,(13),[1,2,5,6,13,14],[190],372⟩) from rfl))
private theorem rec4793 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(14),[1,2,5,6,13,14],[190],371⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[644]? = some (⟨64,(14),[1,2,5,6,13,14],[190],371⟩) from rfl))
private theorem rec4799 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(15),[1,2,5,6,13,14],[190],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[650]? = some (⟨64,(15),[1,2,5,6,13,14],[190],373⟩) from rfl))
private theorem rec4805 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(16),[1,2,5,6,13,14],[190],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[656]? = some (⟨64,(16),[1,2,5,6,13,14],[190],373⟩) from rfl))
private theorem rec4811 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(17),[1,2,5,6,13,14],[190],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[662]? = some (⟨64,(17),[1,2,5,6,13,14],[190],373⟩) from rfl))
private theorem rec4817 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(18),[1,2,5,6,13,14],[190],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[668]? = some (⟨64,(18),[1,2,5,6,13,14],[190],373⟩) from rfl))
private theorem rec4823 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(19),[1,2,5,6,13,14],[190],373⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[674]? = some (⟨64,(19),[1,2,5,6,13,14],[190],373⟩) from rfl))
private theorem rec4829 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(20),[1,2,5,6,13,14],[190],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[680]? = some (⟨64,(20),[1,2,5,6,13,14],[190],374⟩) from rfl))
private theorem rec4835 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(21),[1,2,5,6,13,14],[190],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[686]? = some (⟨64,(21),[1,2,5,6,13,14],[190],374⟩) from rfl))
private theorem rec4841 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(22),[1,2,5,6,13,14],[190],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[692]? = some (⟨64,(22),[1,2,5,6,13,14],[190],374⟩) from rfl))
private theorem rec4847 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(23),[1,2,5,6,13,14],[190],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[698]? = some (⟨64,(23),[1,2,5,6,13,14],[190],374⟩) from rfl))
private theorem rec4853 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 64 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨64,(24),[1,2,5,6,13,14],[190],374⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[704]? = some (⟨64,(24),[1,2,5,6,13,14],[190],374⟩) from rfl))
private theorem rec4859 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(0),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[710]? = some (⟨67,(0),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4862 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(1),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[713]? = some (⟨67,(1),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4865 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(2),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[716]? = some (⟨67,(2),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4868 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(3),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[719]? = some (⟨67,(3),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4871 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(4),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[722]? = some (⟨67,(4),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4874 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(5),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[725]? = some (⟨67,(5),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4877 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(6),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[728]? = some (⟨67,(6),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4880 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(7),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[731]? = some (⟨67,(7),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4883 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(8),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[734]? = some (⟨67,(8),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4886 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(9),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[737]? = some (⟨67,(9),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4889 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(10),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[740]? = some (⟨67,(10),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4892 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(11),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[743]? = some (⟨67,(11),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4895 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(12),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[746]? = some (⟨67,(12),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4898 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(13),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[749]? = some (⟨67,(13),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4901 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(14),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[752]? = some (⟨67,(14),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4904 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(15),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[755]? = some (⟨67,(15),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4907 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(16),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[758]? = some (⟨67,(16),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4910 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(17),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[761]? = some (⟨67,(17),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4913 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(18),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[764]? = some (⟨67,(18),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4916 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(19),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[767]? = some (⟨67,(19),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(20),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[770]? = some (⟨67,(20),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4922 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(21),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[773]? = some (⟨67,(21),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4925 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(22),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[776]? = some (⟨67,(22),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4928 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(23),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[779]? = some (⟨67,(23),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 67 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨67,(24),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[782]? = some (⟨67,(24),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec4934 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(0),[1,2,5,6,13,14],[190],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[785]? = some (⟨69,(0),[1,2,5,6,13,14],[190],189⟩) from rfl))
private theorem rec4942 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(1),[1,2,5,6,13,14],[190],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[793]? = some (⟨69,(1),[1,2,5,6,13,14],[190],260⟩) from rfl))
private theorem rec4952 (si parent : ℕ) (hs : si ∈ ([2, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(2),[2,14],[190],261⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[803]? = some (⟨69,(2),[2,14],[190],261⟩) from rfl))
private theorem rec4964 (si parent : ℕ) (hs : si ∈ ([2, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(3),[2,14],[190],262⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[815]? = some (⟨69,(3),[2,14],[190],262⟩) from rfl))
private theorem rec4976 (si parent : ℕ) (hs : si ∈ ([2, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(4),[2,14],[190],263⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[827]? = some (⟨69,(4),[2,14],[190],263⟩) from rfl))
private theorem rec4987 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(5),[1,2,5,6,13,14],[190],189⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[838]? = some (⟨69,(5),[1,2,5,6,13,14],[190],189⟩) from rfl))
private theorem rec4995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(6),[1,2,5,6,13,14],[190],260⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[846]? = some (⟨69,(6),[1,2,5,6,13,14],[190],260⟩) from rfl))
private theorem rec5004 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(7),[1,2,5,6,13,14],[190],375⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[855]? = some (⟨69,(7),[1,2,5,6,13,14],[190],375⟩) from rfl))
private theorem rec5014 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(8),[1,2,5,6,13,14],[190],376⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[865]? = some (⟨69,(8),[1,2,5,6,13,14],[190],376⟩) from rfl))
private theorem rec5024 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(9),[1,2,5,6,13,14],[190],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[875]? = some (⟨69,(9),[1,2,5,6,13,14],[190],377⟩) from rfl))
private theorem rec5034 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(10),[1,2,5,6,13,14],[190],194⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[885]? = some (⟨69,(10),[1,2,5,6,13,14],[190],194⟩) from rfl))
private theorem rec5042 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(11),[1,2,5,6,13,14],[190],267⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[893]? = some (⟨69,(11),[1,2,5,6,13,14],[190],267⟩) from rfl))
private theorem rec5051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(12),[1,2,5,6,13,14],[190],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[902]? = some (⟨69,(12),[1,2,5,6,13,14],[190],378⟩) from rfl))
private theorem rec5061 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(13),[1,2,5,6,13,14],[190],378⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[912]? = some (⟨69,(13),[1,2,5,6,13,14],[190],378⟩) from rfl))
private theorem rec5071 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(14),[1,2,5,6,13,14],[190],377⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[922]? = some (⟨69,(14),[1,2,5,6,13,14],[190],377⟩) from rfl))
private theorem rec5081 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(15),[1,2,5,6,13,14],[190],196⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[932]? = some (⟨69,(15),[1,2,5,6,13,14],[190],196⟩) from rfl))
private theorem rec5089 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(16),[1,2,5,6,13,14],[190],269⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[940]? = some (⟨69,(16),[1,2,5,6,13,14],[190],269⟩) from rfl))
private theorem rec5098 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(17),[1,2,5,6,13,14],[190],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[949]? = some (⟨69,(17),[1,2,5,6,13,14],[190],379⟩) from rfl))
private theorem rec5108 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(18),[1,2,5,6,13,14],[190],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[959]? = some (⟨69,(18),[1,2,5,6,13,14],[190],379⟩) from rfl))
private theorem rec5118 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(19),[1,2,5,6,13,14],[190],379⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[969]? = some (⟨69,(19),[1,2,5,6,13,14],[190],379⟩) from rfl))
private theorem rec5128 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(20),[1,2,5,6,13,14],[190],198⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[979]? = some (⟨69,(20),[1,2,5,6,13,14],[190],198⟩) from rfl))
private theorem rec5136 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(21),[1,2,5,6,13,14],[190],271⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[987]? = some (⟨69,(21),[1,2,5,6,13,14],[190],271⟩) from rfl))
private theorem rec5145 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(22),[1,2,5,6,13,14],[190],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[996]? = some (⟨69,(22),[1,2,5,6,13,14],[190],380⟩) from rfl))
private theorem rec5155 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(23),[1,2,5,6,13,14],[190],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1006]? = some (⟨69,(23),[1,2,5,6,13,14],[190],380⟩) from rfl))
private theorem rec5165 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 69 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨69,(24),[1,2,5,6,13,14],[190],380⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1016]? = some (⟨69,(24),[1,2,5,6,13,14],[190],380⟩) from rfl))
private theorem rec5174 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(0),[1,2],[190],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1025]? = some (⟨72,(0),[1,2],[190],354⟩) from rfl))
private theorem rec5182 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(1),[1,2],[190],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1033]? = some (⟨72,(1),[1,2],[190],355⟩) from rfl))
private theorem rec5190 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(2),[1,2],[190],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1041]? = some (⟨72,(2),[1,2],[190],356⟩) from rfl))
private theorem rec5198 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(3),[1,2],[190],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1049]? = some (⟨72,(3),[1,2],[190],357⟩) from rfl))
private theorem rec5206 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(4),[1,2],[190],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1057]? = some (⟨72,(4),[1,2],[190],354⟩) from rfl))
private theorem rec5214 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(5),[1,2],[190],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1065]? = some (⟨72,(5),[1,2],[190],355⟩) from rfl))
private theorem rec5222 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(6),[1,2],[190],358⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1073]? = some (⟨72,(6),[1,2],[190],358⟩) from rfl))
private theorem rec5230 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(7),[1,2],[190],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1081]? = some (⟨72,(7),[1,2],[190],357⟩) from rfl))
private theorem rec5238 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(8),[1,2],[190],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1089]? = some (⟨72,(8),[1,2],[190],354⟩) from rfl))
private theorem rec5246 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(9),[1,2],[190],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1097]? = some (⟨72,(9),[1,2],[190],355⟩) from rfl))
private theorem rec5254 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(10),[1,2],[190],356⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1105]? = some (⟨72,(10),[1,2],[190],356⟩) from rfl))
private theorem rec5262 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(11),[1,2],[190],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1113]? = some (⟨72,(11),[1,2],[190],357⟩) from rfl))
private theorem rec5270 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(12),[1,2],[190],354⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1121]? = some (⟨72,(12),[1,2],[190],354⟩) from rfl))
private theorem rec5278 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(13),[1,2],[190],355⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1129]? = some (⟨72,(13),[1,2],[190],355⟩) from rfl))
private theorem rec5286 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(14),[1,2],[190],359⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1137]? = some (⟨72,(14),[1,2],[190],359⟩) from rfl))
private theorem rec5294 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 72 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨72,(15),[1,2],[190],357⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1145]? = some (⟨72,(15),[1,2],[190],357⟩) from rfl))
private theorem rec5303 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 75 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(0),[1,2,5,6],[190],381⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1154]? = some (⟨75,(0),[1,2,5,6],[190],381⟩) from rfl))
private theorem rec5313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 75 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(1),[1,2,5,6],[190],382⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1164]? = some (⟨75,(1),[1,2,5,6],[190],382⟩) from rfl))
private theorem rec5323 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 75 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(2),[1,2,5,6],[190],383⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1174]? = some (⟨75,(2),[1,2,5,6],[190],383⟩) from rfl))
private theorem rec5333 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 75 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨75,(3),[1,2,5,6],[190],384⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1184]? = some (⟨75,(3),[1,2,5,6],[190],384⟩) from rfl))
private theorem rec5344 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(0),[2],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1195]? = some (⟨77,(0),[2],[150,190],2⟩) from rfl))
private theorem rec5351 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(1),[2],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1202]? = some (⟨77,(1),[2],[190],2⟩) from rfl))
private theorem rec5359 (si parent : ℕ) (hs : si ∈ ([2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(2),[2,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1210]? = some (⟨77,(2),[2,13,14],[190],2⟩) from rfl))
private theorem rec5364 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(3),[1,2,5,6,14],[190],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1215]? = some (⟨77,(3),[1,2,5,6,14],[190],234⟩) from rfl))
private theorem rec5373 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(4),[2],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part4 (List.mem_of_getElem? (show section14DataRecords2Part1[1224]? = some (⟨77,(4),[2],[150,190],2⟩) from rfl))
private theorem rec5380 (si parent : ℕ) (hs : si ∈ ([2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(5),[2],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[5]? = some (⟨77,(5),[2],[190],2⟩) from rfl))
private theorem rec5387 (si parent : ℕ) (hs : si ∈ ([2, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(6),[2,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[12]? = some (⟨77,(6),[2,13,14],[190],2⟩) from rfl))
private theorem rec5392 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(7),[1,2,5,6,13,14],[190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[17]? = some (⟨77,(7),[1,2,5,6,13,14],[190],2⟩) from rfl))
private theorem rec5399 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(8),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[24]? = some (⟨77,(8),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec5403 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(9),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[28]? = some (⟨77,(9),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec5407 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(10),[1,2,5,6,13,14],[190],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[32]? = some (⟨77,(10),[1,2,5,6,13,14],[190],29⟩) from rfl))
private theorem rec5411 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(11),[1,2,5,6,13,14],[190],234⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[36]? = some (⟨77,(11),[1,2,5,6,13,14],[190],234⟩) from rfl))
private theorem rec5415 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(12),[1,2,5,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[40]? = some (⟨77,(12),[1,2,5,14],[190],3⟩) from rfl))
private theorem rec5422 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(13),[1,2,5,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[47]? = some (⟨77,(13),[1,2,5,14],[190],3⟩) from rfl))
private theorem rec5428 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(14),[1,2,5,6,13],[190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[53]? = some (⟨77,(14),[1,2,5,6,13],[190],99⟩) from rfl))
private theorem rec5434 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 77 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨77,(15),[1,2,5,6,13,14],[190],99⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[59]? = some (⟨77,(15),[1,2,5,6,13,14],[190],99⟩) from rfl))
private theorem rec5438 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(0),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[63]? = some (⟨79,(0),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5441 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(1),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[66]? = some (⟨79,(1),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5444 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(2),[1,2],[190],364⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[69]? = some (⟨79,(2),[1,2],[190],364⟩) from rfl))
private theorem rec5452 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(3),[1,2,5,6],[150,190],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[77]? = some (⟨79,(3),[1,2,5,6],[150,190],101⟩) from rfl))
private theorem rec5455 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(4),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[80]? = some (⟨79,(4),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6] : List ℕ)) (hp : parent ∈ ([150, 190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(5),[1,2,5,6],[150,190],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[83]? = some (⟨79,(5),[1,2,5,6],[150,190],2⟩) from rfl))
private theorem rec5461 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 79 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨79,(6),[1,2],[190],365⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[86]? = some (⟨79,(6),[1,2],[190],365⟩) from rfl))
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
private theorem rec5513 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 80 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(5),[1,2,5,6,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[138]? = some (⟨80,(5),[1,2,5,6,14],[190],3⟩) from rfl))
private theorem rec5518 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 80 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(7),[1,2,6,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[143]? = some (⟨80,(7),[1,2,6,14],[190],3⟩) from rfl))
private theorem rec5524 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 80 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(8),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[149]? = some (⟨80,(8),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec5527 (si parent : ℕ) (hs : si ∈ ([1, 2] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 80 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(9),[1,2],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[152]? = some (⟨80,(9),[1,2],[190],3⟩) from rfl))
private theorem rec5534 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 80 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(15),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[159]? = some (⟨80,(15),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec5538 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 80 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(16),[1,2,5,6,13,14],[190],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[163]? = some (⟨80,(16),[1,2,5,6,13,14],[190],3⟩) from rfl))
private theorem rec5541 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 80 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(17),[1,2,5,6,13,14],[190],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[166]? = some (⟨80,(17),[1,2,5,6,13,14],[190],48⟩) from rfl))
private theorem rec5548 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([190] : List ℕ)) : section14Recorded section14Catalog si parent 80 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨80,(19),[1,2,5,6,13,14],[190],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part5 (List.mem_of_getElem? (show section14DataRecords2Part2[173]? = some (⟨80,(19),[1,2,5,6,13,14],[190],143⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 2).plans.drop 3).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 2)).drop 176).take 16, section14Recorded section14Catalog 2 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 2 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 2).plans.drop 3).take 1 = [⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(61,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(76,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec4508 2 176 (by decide) (by decide)
  · left
    exact rec4508 2 177 (by decide) (by decide)
  · left
    exact rec4488 2 178 (by decide) (by decide)
  · left
    exact rec4488 2 179 (by decide) (by decide)
  · left
    exact rec4508 2 180 (by decide) (by decide)
  · left
    exact rec4508 2 181 (by decide) (by decide)
  · left
    exact rec4488 2 182 (by decide) (by decide)
  · left
    exact rec4488 2 183 (by decide) (by decide)
  · left
    exact rec4487 2 184 (by decide) (by decide)
  · left
    exact rec4487 2 185 (by decide) (by decide)
  · left
    exact rec4506 2 186 (by decide) (by decide)
  · left
    exact rec4495 2 187 (by decide) (by decide)
  · left
    exact rec4487 2 188 (by decide) (by decide)
  · left
    exact rec4487 2 189 (by decide) (by decide)
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
        exact rec4609 2 190 (by decide) (by decide)
      · right
        exact rec4613 2 190 (by decide) (by decide)
      · right
        exact rec4617 2 190 (by decide) (by decide)
      · right
        exact rec4621 2 190 (by decide) (by decide)
      · right
        exact rec4625 2 190 (by decide) (by decide)
      · right
        exact rec4629 2 190 (by decide) (by decide)
      · right
        exact rec4633 2 190 (by decide) (by decide)
      · right
        exact rec4637 2 190 (by decide) (by decide)
      · right
        exact rec4641 2 190 (by decide) (by decide)
      · right
        exact rec4645 2 190 (by decide) (by decide)
      · right
        exact rec4649 2 190 (by decide) (by decide)
      · right
        exact rec4653 2 190 (by decide) (by decide)
      · right
        exact rec4657 2 190 (by decide) (by decide)
      · right
        exact rec4661 2 190 (by decide) (by decide)
      · right
        exact rec4665 2 190 (by decide) (by decide)
      · right
        exact rec4669 2 190 (by decide) (by decide)
      · right
        exact rec4673 2 190 (by decide) (by decide)
      · right
        exact rec4677 2 190 (by decide) (by decide)
      · right
        exact rec4681 2 190 (by decide) (by decide)
      · right
        exact rec4685 2 190 (by decide) (by decide)
      · right
        exact rec4689 2 190 (by decide) (by decide)
      · right
        exact rec4693 2 190 (by decide) (by decide)
      · right
        exact rec4697 2 190 (by decide) (by decide)
      · right
        exact rec4701 2 190 (by decide) (by decide)
      · right
        exact rec4705 2 190 (by decide) (by decide)
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
        exact rec4709 2 190 (by decide) (by decide)
      · right
        exact rec4715 2 190 (by decide) (by decide)
      · right
        exact rec4721 2 190 (by decide) (by decide)
      · right
        exact rec4727 2 190 (by decide) (by decide)
      · right
        exact rec4733 2 190 (by decide) (by decide)
      · right
        exact rec4739 2 190 (by decide) (by decide)
      · right
        exact rec4745 2 190 (by decide) (by decide)
      · right
        exact rec4751 2 190 (by decide) (by decide)
      · right
        exact rec4757 2 190 (by decide) (by decide)
      · right
        exact rec4763 2 190 (by decide) (by decide)
      · right
        exact rec4769 2 190 (by decide) (by decide)
      · right
        exact rec4775 2 190 (by decide) (by decide)
      · right
        exact rec4781 2 190 (by decide) (by decide)
      · right
        exact rec4787 2 190 (by decide) (by decide)
      · right
        exact rec4793 2 190 (by decide) (by decide)
      · right
        exact rec4799 2 190 (by decide) (by decide)
      · right
        exact rec4805 2 190 (by decide) (by decide)
      · right
        exact rec4811 2 190 (by decide) (by decide)
      · right
        exact rec4817 2 190 (by decide) (by decide)
      · right
        exact rec4823 2 190 (by decide) (by decide)
      · right
        exact rec4829 2 190 (by decide) (by decide)
      · right
        exact rec4835 2 190 (by decide) (by decide)
      · right
        exact rec4841 2 190 (by decide) (by decide)
      · right
        exact rec4847 2 190 (by decide) (by decide)
      · right
        exact rec4853 2 190 (by decide) (by decide)
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
        exact rec4859 2 190 (by decide) (by decide)
      · right
        exact rec4862 2 190 (by decide) (by decide)
      · right
        exact rec4865 2 190 (by decide) (by decide)
      · right
        exact rec4868 2 190 (by decide) (by decide)
      · right
        exact rec4871 2 190 (by decide) (by decide)
      · right
        exact rec4874 2 190 (by decide) (by decide)
      · right
        exact rec4877 2 190 (by decide) (by decide)
      · right
        exact rec4880 2 190 (by decide) (by decide)
      · right
        exact rec4883 2 190 (by decide) (by decide)
      · right
        exact rec4886 2 190 (by decide) (by decide)
      · right
        exact rec4889 2 190 (by decide) (by decide)
      · right
        exact rec4892 2 190 (by decide) (by decide)
      · right
        exact rec4895 2 190 (by decide) (by decide)
      · right
        exact rec4898 2 190 (by decide) (by decide)
      · right
        exact rec4901 2 190 (by decide) (by decide)
      · right
        exact rec4904 2 190 (by decide) (by decide)
      · right
        exact rec4907 2 190 (by decide) (by decide)
      · right
        exact rec4910 2 190 (by decide) (by decide)
      · right
        exact rec4913 2 190 (by decide) (by decide)
      · right
        exact rec4916 2 190 (by decide) (by decide)
      · right
        exact rec4919 2 190 (by decide) (by decide)
      · right
        exact rec4922 2 190 (by decide) (by decide)
      · right
        exact rec4925 2 190 (by decide) (by decide)
      · right
        exact rec4928 2 190 (by decide) (by decide)
      · right
        exact rec4931 2 190 (by decide) (by decide)
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
        exact rec4934 2 190 (by decide) (by decide)
      · right
        exact rec4942 2 190 (by decide) (by decide)
      · right
        exact rec4952 2 190 (by decide) (by decide)
      · right
        exact rec4964 2 190 (by decide) (by decide)
      · right
        exact rec4976 2 190 (by decide) (by decide)
      · right
        exact rec4987 2 190 (by decide) (by decide)
      · right
        exact rec4995 2 190 (by decide) (by decide)
      · right
        exact rec5004 2 190 (by decide) (by decide)
      · right
        exact rec5014 2 190 (by decide) (by decide)
      · right
        exact rec5024 2 190 (by decide) (by decide)
      · right
        exact rec5034 2 190 (by decide) (by decide)
      · right
        exact rec5042 2 190 (by decide) (by decide)
      · right
        exact rec5051 2 190 (by decide) (by decide)
      · right
        exact rec5061 2 190 (by decide) (by decide)
      · right
        exact rec5071 2 190 (by decide) (by decide)
      · right
        exact rec5081 2 190 (by decide) (by decide)
      · right
        exact rec5089 2 190 (by decide) (by decide)
      · right
        exact rec5098 2 190 (by decide) (by decide)
      · right
        exact rec5108 2 190 (by decide) (by decide)
      · right
        exact rec5118 2 190 (by decide) (by decide)
      · right
        exact rec5128 2 190 (by decide) (by decide)
      · right
        exact rec5136 2 190 (by decide) (by decide)
      · right
        exact rec5145 2 190 (by decide) (by decide)
      · right
        exact rec5155 2 190 (by decide) (by decide)
      · right
        exact rec5165 2 190 (by decide) (by decide)
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
        exact rec5174 2 190 (by decide) (by decide)
      · right
        exact rec5182 2 190 (by decide) (by decide)
      · right
        exact rec5190 2 190 (by decide) (by decide)
      · right
        exact rec5198 2 190 (by decide) (by decide)
      · right
        exact rec5206 2 190 (by decide) (by decide)
      · right
        exact rec5214 2 190 (by decide) (by decide)
      · right
        exact rec5222 2 190 (by decide) (by decide)
      · right
        exact rec5230 2 190 (by decide) (by decide)
      · right
        exact rec5238 2 190 (by decide) (by decide)
      · right
        exact rec5246 2 190 (by decide) (by decide)
      · right
        exact rec5254 2 190 (by decide) (by decide)
      · right
        exact rec5262 2 190 (by decide) (by decide)
      · right
        exact rec5270 2 190 (by decide) (by decide)
      · right
        exact rec5278 2 190 (by decide) (by decide)
      · right
        exact rec5286 2 190 (by decide) (by decide)
      · right
        exact rec5294 2 190 (by decide) (by decide)
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
        exact rec5303 2 190 (by decide) (by decide)
      · right
        exact rec5313 2 190 (by decide) (by decide)
      · right
        exact rec5323 2 190 (by decide) (by decide)
      · right
        exact rec5333 2 190 (by decide) (by decide)
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
        exact rec5344 2 190 (by decide) (by decide)
      · right
        exact rec5351 2 190 (by decide) (by decide)
      · right
        exact rec5359 2 190 (by decide) (by decide)
      · right
        exact rec5364 2 190 (by decide) (by decide)
      · right
        exact rec5373 2 190 (by decide) (by decide)
      · right
        exact rec5380 2 190 (by decide) (by decide)
      · right
        exact rec5387 2 190 (by decide) (by decide)
      · right
        exact rec5392 2 190 (by decide) (by decide)
      · right
        exact rec5399 2 190 (by decide) (by decide)
      · right
        exact rec5403 2 190 (by decide) (by decide)
      · right
        exact rec5407 2 190 (by decide) (by decide)
      · right
        exact rec5411 2 190 (by decide) (by decide)
      · right
        exact rec5415 2 190 (by decide) (by decide)
      · right
        exact rec5422 2 190 (by decide) (by decide)
      · right
        exact rec5428 2 190 (by decide) (by decide)
      · right
        exact rec5434 2 190 (by decide) (by decide)
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
        exact rec5438 2 190 (by decide) (by decide)
      · right
        exact rec5441 2 190 (by decide) (by decide)
      · right
        exact rec5444 2 190 (by decide) (by decide)
      · right
        exact rec5452 2 190 (by decide) (by decide)
      · right
        exact rec5455 2 190 (by decide) (by decide)
      · right
        exact rec5458 2 190 (by decide) (by decide)
      · right
        exact rec5461 2 190 (by decide) (by decide)
      · right
        exact rec5469 2 190 (by decide) (by decide)
      · right
        exact rec5472 2 190 (by decide) (by decide)
      · right
        exact rec5475 2 190 (by decide) (by decide)
      · right
        exact rec5478 2 190 (by decide) (by decide)
      · right
        exact rec5483 2 190 (by decide) (by decide)
      · right
        exact rec5486 2 190 (by decide) (by decide)
      · right
        exact rec5489 2 190 (by decide) (by decide)
      · right
        exact rec5492 2 190 (by decide) (by decide)
      · right
        exact rec5495 2 190 (by decide) (by decide)
      · right
        exact rec5498 2 190 (by decide) (by decide)
      · right
        exact rec5501 2 190 (by decide) (by decide)
      · right
        exact rec5504 2 190 (by decide) (by decide)
      · right
        exact rec5509 2 190 (by decide) (by decide)
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
        exact rec5513 2 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec5518 2 190 (by decide) (by decide)
      · right
        exact rec5524 2 190 (by decide) (by decide)
      · right
        exact rec5527 2 190 (by decide) (by decide)
      · left
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
        exact rec5534 2 190 (by decide) (by decide)
      · right
        exact rec5538 2 190 (by decide) (by decide)
      · right
        exact rec5541 2 190 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec5548 2 190 (by decide) (by decide)
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
    exact rec4513 2 191 (by decide) (by decide)
end Section14Coverage_2_3_p176_192

#print axioms solution
