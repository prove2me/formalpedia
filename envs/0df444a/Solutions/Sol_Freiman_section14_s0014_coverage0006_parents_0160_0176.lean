-- Prove2me | solution 1 for Freiman.section14_s0014_coverage0006_parents_0160_0176
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T00:56:45.447906+00:00
-- url     : https://prove2.me/submissions/973d0fd7-1c43-4cf7-b26f-83ffd4abc28e

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
namespace Section14Coverage_14_6_p160_176
private theorem rec12931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[483]? = some (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec12932 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[484]? = some (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec12938 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[490]? = some (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) from rfl))
private theorem rec12940 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,13,14],[174],908⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[492]? = some (⟨245,(-1),[1,2,5,6,13,14],[174],908⟩) from rfl))
private theorem rec12943 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 245 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨245,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[495]? = some (⟨245,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec12987 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(0),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[539]? = some (⟨247,(0),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12989 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(1),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[541]? = some (⟨247,(1),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12991 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(2),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[543]? = some (⟨247,(2),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12993 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(3),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[545]? = some (⟨247,(3),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(4),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[547]? = some (⟨247,(4),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12997 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(5),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[549]? = some (⟨247,(5),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12999 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(6),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[551]? = some (⟨247,(6),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13001 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[553]? = some (⟨247,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13003 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(8),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[555]? = some (⟨247,(8),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(9),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[557]? = some (⟨247,(9),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13007 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(10),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[559]? = some (⟨247,(10),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13009 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(11),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[561]? = some (⟨247,(11),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13011 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(12),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[563]? = some (⟨247,(12),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13013 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(13),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[565]? = some (⟨247,(13),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13015 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(14),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[567]? = some (⟨247,(14),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13017 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(15),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[569]? = some (⟨247,(15),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13019 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(16),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[571]? = some (⟨247,(16),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13021 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(17),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[573]? = some (⟨247,(17),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13023 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(18),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[575]? = some (⟨247,(18),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13025 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(19),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[577]? = some (⟨247,(19),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13027 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(20),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[579]? = some (⟨247,(20),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13029 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(21),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[581]? = some (⟨247,(21),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13031 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(22),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[583]? = some (⟨247,(22),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13033 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(23),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[585]? = some (⟨247,(23),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13035 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 247 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨247,(24),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[587]? = some (⟨247,(24),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13037 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(0),[1,2,5,6,13,14],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[589]? = some (⟨249,(0),[1,2,5,6,13,14],[170],10⟩) from rfl))
private theorem rec13040 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(1),[2,5,6,14],[170],924⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[592]? = some (⟨249,(1),[2,5,6,14],[170],924⟩) from rfl))
private theorem rec13042 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(2),[1,2,5,6,13,14],[170],888⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[594]? = some (⟨249,(2),[1,2,5,6,13,14],[170],888⟩) from rfl))
private theorem rec13044 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(3),[1,2,5,6,13,14],[170],889⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[596]? = some (⟨249,(3),[1,2,5,6,13,14],[170],889⟩) from rfl))
private theorem rec13046 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(4),[1,2,5,6,13,14],[170],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[598]? = some (⟨249,(4),[1,2,5,6,13,14],[170],890⟩) from rfl))
private theorem rec13048 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(5),[1,2,5,6,13,14],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[600]? = some (⟨249,(5),[1,2,5,6,13,14],[170],10⟩) from rfl))
private theorem rec13051 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(6),[2,5,6,14],[170],924⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[603]? = some (⟨249,(6),[2,5,6,14],[170],924⟩) from rfl))
private theorem rec13053 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(7),[1,2,5,6,13,14],[170],888⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[605]? = some (⟨249,(7),[1,2,5,6,13,14],[170],888⟩) from rfl))
private theorem rec13055 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(8),[1,2,5,6,13,14],[170],889⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[607]? = some (⟨249,(8),[1,2,5,6,13,14],[170],889⟩) from rfl))
private theorem rec13057 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(9),[1,2,5,6,13,14],[170],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[609]? = some (⟨249,(9),[1,2,5,6,13,14],[170],890⟩) from rfl))
private theorem rec13059 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(10),[1,2,5,6,13,14],[170],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[611]? = some (⟨249,(10),[1,2,5,6,13,14],[170],18⟩) from rfl))
private theorem rec13062 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(11),[2,5,6,14],[170],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[614]? = some (⟨249,(11),[2,5,6,14],[170],891⟩) from rfl))
private theorem rec13064 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(12),[1,2,5,6,13,14],[170],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[616]? = some (⟨249,(12),[1,2,5,6,13,14],[170],891⟩) from rfl))
private theorem rec13066 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(13),[1,2,5,6,13,14],[170],891⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[618]? = some (⟨249,(13),[1,2,5,6,13,14],[170],891⟩) from rfl))
private theorem rec13068 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(14),[1,2,5,6,13,14],[170],890⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[620]? = some (⟨249,(14),[1,2,5,6,13,14],[170],890⟩) from rfl))
private theorem rec13070 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(15),[1,2,5,6,13,14],[170],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[622]? = some (⟨249,(15),[1,2,5,6,13,14],[170],21⟩) from rfl))
private theorem rec13073 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(16),[2,5,6,14],[170],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[625]? = some (⟨249,(16),[2,5,6,14],[170],892⟩) from rfl))
private theorem rec13075 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(17),[1,2,5,6,13,14],[170],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[627]? = some (⟨249,(17),[1,2,5,6,13,14],[170],892⟩) from rfl))
private theorem rec13077 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(18),[1,2,5,6,13,14],[170],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[629]? = some (⟨249,(18),[1,2,5,6,13,14],[170],892⟩) from rfl))
private theorem rec13079 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(19),[1,2,5,6,13,14],[170],892⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[631]? = some (⟨249,(19),[1,2,5,6,13,14],[170],892⟩) from rfl))
private theorem rec13081 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(20),[1,2,5,6,13,14],[170],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[633]? = some (⟨249,(20),[1,2,5,6,13,14],[170],24⟩) from rfl))
private theorem rec13084 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(21),[2,5,6,14],[170],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[636]? = some (⟨249,(21),[2,5,6,14],[170],893⟩) from rfl))
private theorem rec13086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(22),[1,2,5,6,13,14],[170],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[638]? = some (⟨249,(22),[1,2,5,6,13,14],[170],893⟩) from rfl))
private theorem rec13088 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(23),[1,2,5,6,13,14],[170],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[640]? = some (⟨249,(23),[1,2,5,6,13,14],[170],893⟩) from rfl))
private theorem rec13090 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 249 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨249,(24),[1,2,5,6,13,14],[170],893⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[642]? = some (⟨249,(24),[1,2,5,6,13,14],[170],893⟩) from rfl))
private theorem rec13092 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(0),[1,2,5,6,13,14],[170],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[644]? = some (⟨253,(0),[1,2,5,6,13,14],[170],884⟩) from rfl))
private theorem rec13096 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(1),[1,2,5,6,13,14],[170],894⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[648]? = some (⟨253,(1),[1,2,5,6,13,14],[170],894⟩) from rfl))
private theorem rec13100 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(2),[1,2,5,6,13,14],[170],895⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[652]? = some (⟨253,(2),[1,2,5,6,13,14],[170],895⟩) from rfl))
private theorem rec13104 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(3),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[656]? = some (⟨253,(3),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13107 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(4),[1,2,5,6,13,14],[170],30⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[659]? = some (⟨253,(4),[1,2,5,6,13,14],[170],30⟩) from rfl))
private theorem rec13110 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(5),[1,2,5,6,13,14],[170],884⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[662]? = some (⟨253,(5),[1,2,5,6,13,14],[170],884⟩) from rfl))
private theorem rec13114 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(6),[1,2,5,6,13,14],[170],894⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[666]? = some (⟨253,(6),[1,2,5,6,13,14],[170],894⟩) from rfl))
private theorem rec13118 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(7),[1,2,5,6,13,14],[170],896⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[670]? = some (⟨253,(7),[1,2,5,6,13,14],[170],896⟩) from rfl))
private theorem rec13123 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(8),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[675]? = some (⟨253,(8),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13126 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(9),[1,2,5,6,13,14],[170],32⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[678]? = some (⟨253,(9),[1,2,5,6,13,14],[170],32⟩) from rfl))
private theorem rec13129 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(10),[1,2,5,6,13,14],[170],84⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[681]? = some (⟨253,(10),[1,2,5,6,13,14],[170],84⟩) from rfl))
private theorem rec13132 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(11),[1,2,5,6,13,14],[170],897⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[684]? = some (⟨253,(11),[1,2,5,6,13,14],[170],897⟩) from rfl))
private theorem rec13135 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(12),[1,2,5,6,13,14],[170],898⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[687]? = some (⟨253,(12),[1,2,5,6,13,14],[170],898⟩) from rfl))
private theorem rec13138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(13),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[690]? = some (⟨253,(13),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13141 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(14),[1,2,5,6,13,14],[170],34⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[693]? = some (⟨253,(14),[1,2,5,6,13,14],[170],34⟩) from rfl))
private theorem rec13144 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(15),[1,2,5,6,13,14],[170],35⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[696]? = some (⟨253,(15),[1,2,5,6,13,14],[170],35⟩) from rfl))
private theorem rec13147 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(16),[1,2,5,6,13,14],[170],36⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[699]? = some (⟨253,(16),[1,2,5,6,13,14],[170],36⟩) from rfl))
private theorem rec13150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(17),[1,2,5,6,13,14],[170],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[702]? = some (⟨253,(17),[1,2,5,6,13,14],[170],37⟩) from rfl))
private theorem rec13153 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(18),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[705]? = some (⟨253,(18),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13156 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(19),[1,2,5,6,13,14],[170],37⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[708]? = some (⟨253,(19),[1,2,5,6,13,14],[170],37⟩) from rfl))
private theorem rec13159 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(20),[1,2,5,6,13,14],[170],38⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[711]? = some (⟨253,(20),[1,2,5,6,13,14],[170],38⟩) from rfl))
private theorem rec13162 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(21),[1,2,5,6,13,14],[170],39⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[714]? = some (⟨253,(21),[1,2,5,6,13,14],[170],39⟩) from rfl))
private theorem rec13165 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(22),[1,2,5,6,13,14],[170],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[717]? = some (⟨253,(22),[1,2,5,6,13,14],[170],40⟩) from rfl))
private theorem rec13168 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(23),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[720]? = some (⟨253,(23),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec13171 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 253 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨253,(24),[1,2,5,6,13,14],[170],40⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[723]? = some (⟨253,(24),[1,2,5,6,13,14],[170],40⟩) from rfl))
private theorem rec13224 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(5),[1,2,5,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[776]? = some (⟨258,(5),[1,2,5,14],[170],3⟩) from rfl))
private theorem rec13226 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[778]? = some (⟨258,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13227 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(8),[1,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[779]? = some (⟨258,(8),[1,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13230 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(9),[5,6,13,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[782]? = some (⟨258,(9),[5,6,13,14],[170],143⟩) from rfl))
private theorem rec13231 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(15),[1,2,6,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[783]? = some (⟨258,(15),[1,2,6,14],[170],3⟩) from rfl))
private theorem rec13233 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(16),[1,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[785]? = some (⟨258,(16),[1,5,6,13,14],[170],3⟩) from rfl))
private theorem rec13235 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(17),[1,2,5,6,13,14],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[787]? = some (⟨258,(17),[1,2,5,6,13,14],[170],48⟩) from rfl))
private theorem rec13237 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 258 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨258,(19),[2,5,6,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[789]? = some (⟨258,(19),[2,5,6,14],[170],143⟩) from rfl))
private theorem rec16578 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(0),[13,14],[170],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[370]? = some (⟨643,(0),[13,14],[170],1729⟩) from rfl))
private theorem rec16580 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(1),[13,14],[170],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[372]? = some (⟨643,(1),[13,14],[170],1729⟩) from rfl))
private theorem rec16582 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(2),[13,14],[170],1730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[374]? = some (⟨643,(2),[13,14],[170],1730⟩) from rfl))
private theorem rec16584 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(3),[13,14],[170],1730⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[376]? = some (⟨643,(3),[13,14],[170],1730⟩) from rfl))
private theorem rec16586 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(4),[13,14],[170],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[378]? = some (⟨643,(4),[13,14],[170],1729⟩) from rfl))
private theorem rec16588 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(5),[13,14],[170],1729⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[380]? = some (⟨643,(5),[13,14],[170],1729⟩) from rfl))
private theorem rec16590 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(6),[13,14],[170],1731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[382]? = some (⟨643,(6),[13,14],[170],1731⟩) from rfl))
private theorem rec16592 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(7),[13,14],[170],1731⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[384]? = some (⟨643,(7),[13,14],[170],1731⟩) from rfl))
private theorem rec16594 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(8),[13,14],[170],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[386]? = some (⟨643,(8),[13,14],[170],905⟩) from rfl))
private theorem rec16596 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 643 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨643,(9),[13,14],[170],905⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[388]? = some (⟨643,(9),[13,14],[170],905⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 6).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 160).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 14).plans.drop 6).take 1 = [⟨7,245,[([1],[]),([],[1])],false,[(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec12943 14 160 (by decide) (by decide)
  · left
    exact rec12943 14 161 (by decide) (by decide)
  · left
    exact rec12932 14 162 (by decide) (by decide)
  · left
    exact rec12932 14 163 (by decide) (by decide)
  · left
    exact rec12943 14 164 (by decide) (by decide)
  · left
    exact rec12943 14 165 (by decide) (by decide)
  · left
    exact rec12932 14 166 (by decide) (by decide)
  · left
    exact rec12932 14 167 (by decide) (by decide)
  · left
    exact rec12931 14 168 (by decide) (by decide)
  · left
    exact rec12931 14 169 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(246,⟨([1],[]),true,([1],[]),false,false,[]⟩),(247,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(248,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(249,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(250,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(641,⟨([],[1]),true,([],[1]),false,false,[]⟩),(252,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(642,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(643,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(644,⟨([1],[]),true,([],[1]),false,false,[]⟩),(257,⟨([],[1]),true,([1],[]),false,false,[]⟩),(258,⟨([1],[]),true,([],[]),true,false,[]⟩),(645,⟨([],[]),false,([],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 246)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 247)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12987 14 170 (by decide) (by decide)
      · right
        exact rec12989 14 170 (by decide) (by decide)
      · right
        exact rec12991 14 170 (by decide) (by decide)
      · right
        exact rec12993 14 170 (by decide) (by decide)
      · right
        exact rec12995 14 170 (by decide) (by decide)
      · right
        exact rec12997 14 170 (by decide) (by decide)
      · right
        exact rec12999 14 170 (by decide) (by decide)
      · right
        exact rec13001 14 170 (by decide) (by decide)
      · right
        exact rec13003 14 170 (by decide) (by decide)
      · right
        exact rec13005 14 170 (by decide) (by decide)
      · right
        exact rec13007 14 170 (by decide) (by decide)
      · right
        exact rec13009 14 170 (by decide) (by decide)
      · right
        exact rec13011 14 170 (by decide) (by decide)
      · right
        exact rec13013 14 170 (by decide) (by decide)
      · right
        exact rec13015 14 170 (by decide) (by decide)
      · right
        exact rec13017 14 170 (by decide) (by decide)
      · right
        exact rec13019 14 170 (by decide) (by decide)
      · right
        exact rec13021 14 170 (by decide) (by decide)
      · right
        exact rec13023 14 170 (by decide) (by decide)
      · right
        exact rec13025 14 170 (by decide) (by decide)
      · right
        exact rec13027 14 170 (by decide) (by decide)
      · right
        exact rec13029 14 170 (by decide) (by decide)
      · right
        exact rec13031 14 170 (by decide) (by decide)
      · right
        exact rec13033 14 170 (by decide) (by decide)
      · right
        exact rec13035 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 248)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 249)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13037 14 170 (by decide) (by decide)
      · right
        exact rec13040 14 170 (by decide) (by decide)
      · right
        exact rec13042 14 170 (by decide) (by decide)
      · right
        exact rec13044 14 170 (by decide) (by decide)
      · right
        exact rec13046 14 170 (by decide) (by decide)
      · right
        exact rec13048 14 170 (by decide) (by decide)
      · right
        exact rec13051 14 170 (by decide) (by decide)
      · right
        exact rec13053 14 170 (by decide) (by decide)
      · right
        exact rec13055 14 170 (by decide) (by decide)
      · right
        exact rec13057 14 170 (by decide) (by decide)
      · right
        exact rec13059 14 170 (by decide) (by decide)
      · right
        exact rec13062 14 170 (by decide) (by decide)
      · right
        exact rec13064 14 170 (by decide) (by decide)
      · right
        exact rec13066 14 170 (by decide) (by decide)
      · right
        exact rec13068 14 170 (by decide) (by decide)
      · right
        exact rec13070 14 170 (by decide) (by decide)
      · right
        exact rec13073 14 170 (by decide) (by decide)
      · right
        exact rec13075 14 170 (by decide) (by decide)
      · right
        exact rec13077 14 170 (by decide) (by decide)
      · right
        exact rec13079 14 170 (by decide) (by decide)
      · right
        exact rec13081 14 170 (by decide) (by decide)
      · right
        exact rec13084 14 170 (by decide) (by decide)
      · right
        exact rec13086 14 170 (by decide) (by decide)
      · right
        exact rec13088 14 170 (by decide) (by decide)
      · right
        exact rec13090 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 250)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 641)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 252)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 253)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec13092 14 170 (by decide) (by decide)
      · right
        exact rec13096 14 170 (by decide) (by decide)
      · right
        exact rec13100 14 170 (by decide) (by decide)
      · right
        exact rec13104 14 170 (by decide) (by decide)
      · right
        exact rec13107 14 170 (by decide) (by decide)
      · right
        exact rec13110 14 170 (by decide) (by decide)
      · right
        exact rec13114 14 170 (by decide) (by decide)
      · right
        exact rec13118 14 170 (by decide) (by decide)
      · right
        exact rec13123 14 170 (by decide) (by decide)
      · right
        exact rec13126 14 170 (by decide) (by decide)
      · right
        exact rec13129 14 170 (by decide) (by decide)
      · right
        exact rec13132 14 170 (by decide) (by decide)
      · right
        exact rec13135 14 170 (by decide) (by decide)
      · right
        exact rec13138 14 170 (by decide) (by decide)
      · right
        exact rec13141 14 170 (by decide) (by decide)
      · right
        exact rec13144 14 170 (by decide) (by decide)
      · right
        exact rec13147 14 170 (by decide) (by decide)
      · right
        exact rec13150 14 170 (by decide) (by decide)
      · right
        exact rec13153 14 170 (by decide) (by decide)
      · right
        exact rec13156 14 170 (by decide) (by decide)
      · right
        exact rec13159 14 170 (by decide) (by decide)
      · right
        exact rec13162 14 170 (by decide) (by decide)
      · right
        exact rec13165 14 170 (by decide) (by decide)
      · right
        exact rec13168 14 170 (by decide) (by decide)
      · right
        exact rec13171 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 642)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 643)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec16578 14 170 (by decide) (by decide)
      · right
        exact rec16580 14 170 (by decide) (by decide)
      · right
        exact rec16582 14 170 (by decide) (by decide)
      · right
        exact rec16584 14 170 (by decide) (by decide)
      · right
        exact rec16586 14 170 (by decide) (by decide)
      · right
        exact rec16588 14 170 (by decide) (by decide)
      · right
        exact rec16590 14 170 (by decide) (by decide)
      · right
        exact rec16592 14 170 (by decide) (by decide)
      · right
        exact rec16594 14 170 (by decide) (by decide)
      · right
        exact rec16596 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 644)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 257)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 258)).length = 20 := by decide +kernel
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
        exact rec13224 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13226 14 170 (by decide) (by decide)
      · right
        exact rec13227 14 170 (by decide) (by decide)
      · right
        exact rec13230 14 170 (by decide) (by decide)
      · left
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
        exact rec13231 14 170 (by decide) (by decide)
      · right
        exact rec13233 14 170 (by decide) (by decide)
      · right
        exact rec13235 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec13237 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 645)).length = 2 := by decide +kernel
      have hjj : j < 2 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · left
        decide +kernel
  · left
    exact rec12938 14 171 (by decide) (by decide)
  · left
    exact rec12931 14 172 (by decide) (by decide)
  · left
    exact rec12931 14 173 (by decide) (by decide)
  · left
    exact rec12940 14 174 (by decide) (by decide)
  · left
    exact rec12938 14 175 (by decide) (by decide)
end Section14Coverage_14_6_p160_176

#print axioms solution
