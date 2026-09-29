-- Prove2me | solution 1 for Freiman.section14_s0014_coverage0005_parents_0160_0176
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T00:44:17.470446+00:00
-- url     : https://prove2.me/submissions/1b4c8be2-ed70-42cf-ab80-db41cd91e1ce

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
namespace Section14Coverage_14_5_p160_176
private theorem rec7375 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[843]? = some (⟨153,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec7376 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[844]? = some (⟨153,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec7382 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([147, 151, 171, 175, 187, 191] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],636⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[850]? = some (⟨153,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],636⟩) from rfl))
private theorem rec7386 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[854]? = some (⟨153,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec7389 (si parent : ℕ) (hs : si ∈ ([1, 2, 13, 14] : List ℕ)) (hp : parent ∈ ([174] : List ℕ)) : section14Recorded section14Catalog si parent 153 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨153,(-1),[1,2,13,14],[174],878⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[857]? = some (⟨153,(-1),[1,2,13,14],[174],878⟩) from rfl))
private theorem rec7440 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(0),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[908]? = some (⟨155,(0),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7443 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(1),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[911]? = some (⟨155,(1),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7446 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(2),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[914]? = some (⟨155,(2),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7449 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(3),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[917]? = some (⟨155,(3),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7452 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(4),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[920]? = some (⟨155,(4),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7455 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(5),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[923]? = some (⟨155,(5),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(6),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[926]? = some (⟨155,(6),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7461 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[929]? = some (⟨155,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7464 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(8),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[932]? = some (⟨155,(8),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7467 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(9),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[935]? = some (⟨155,(9),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7470 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(10),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[938]? = some (⟨155,(10),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7473 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(11),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[941]? = some (⟨155,(11),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7476 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(12),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[944]? = some (⟨155,(12),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7479 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(13),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[947]? = some (⟨155,(13),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7482 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(14),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[950]? = some (⟨155,(14),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7485 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(15),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[953]? = some (⟨155,(15),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7488 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(16),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[956]? = some (⟨155,(16),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7491 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(17),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[959]? = some (⟨155,(17),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7494 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(18),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[962]? = some (⟨155,(18),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7497 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(19),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[965]? = some (⟨155,(19),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7500 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(20),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[968]? = some (⟨155,(20),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7503 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(21),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[971]? = some (⟨155,(21),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7506 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(22),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[974]? = some (⟨155,(22),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7509 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(23),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[977]? = some (⟨155,(23),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7512 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 155 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨155,(24),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[980]? = some (⟨155,(24),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec7515 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(0),[1,2,5,6,13,14],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[983]? = some (⟨157,(0),[1,2,5,6,13,14],[170],10⟩) from rfl))
private theorem rec7519 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(1),[1,2,5,6,13,14],[170],393⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[987]? = some (⟨157,(1),[1,2,5,6,13,14],[170],393⟩) from rfl))
private theorem rec7524 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(2),[1,2,5,6,13,14],[170],394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[992]? = some (⟨157,(2),[1,2,5,6,13,14],[170],394⟩) from rfl))
private theorem rec7529 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(3),[1,2,5,6,13,14],[170],395⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[997]? = some (⟨157,(3),[1,2,5,6,13,14],[170],395⟩) from rfl))
private theorem rec7534 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(4),[1,2,5,6,13,14],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1002]? = some (⟨157,(4),[1,2,5,6,13,14],[170],396⟩) from rfl))
private theorem rec7539 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(5),[1,2,5,6,13,14],[170],10⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1007]? = some (⟨157,(5),[1,2,5,6,13,14],[170],10⟩) from rfl))
private theorem rec7543 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(6),[1,2,5,6,13,14],[170],393⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1011]? = some (⟨157,(6),[1,2,5,6,13,14],[170],393⟩) from rfl))
private theorem rec7548 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(7),[1,2,5,6,13,14],[170],394⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1016]? = some (⟨157,(7),[1,2,5,6,13,14],[170],394⟩) from rfl))
private theorem rec7553 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(8),[1,2,5,6,13,14],[170],395⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1021]? = some (⟨157,(8),[1,2,5,6,13,14],[170],395⟩) from rfl))
private theorem rec7558 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(9),[1,2,5,6,13,14],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1026]? = some (⟨157,(9),[1,2,5,6,13,14],[170],396⟩) from rfl))
private theorem rec7563 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(10),[1,2,5,6,13,14],[170],18⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1031]? = some (⟨157,(10),[1,2,5,6,13,14],[170],18⟩) from rfl))
private theorem rec7567 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(11),[1,2,5,6,13,14],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1035]? = some (⟨157,(11),[1,2,5,6,13,14],[170],397⟩) from rfl))
private theorem rec7572 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(12),[1,2,5,6,13,14],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1040]? = some (⟨157,(12),[1,2,5,6,13,14],[170],397⟩) from rfl))
private theorem rec7577 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(13),[1,2,5,6,13,14],[170],397⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1045]? = some (⟨157,(13),[1,2,5,6,13,14],[170],397⟩) from rfl))
private theorem rec7582 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(14),[1,2,5,6,13,14],[170],396⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1050]? = some (⟨157,(14),[1,2,5,6,13,14],[170],396⟩) from rfl))
private theorem rec7587 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(15),[1,2,5,6,13,14],[170],21⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1055]? = some (⟨157,(15),[1,2,5,6,13,14],[170],21⟩) from rfl))
private theorem rec7591 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(16),[1,2,5,6,13,14],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1059]? = some (⟨157,(16),[1,2,5,6,13,14],[170],398⟩) from rfl))
private theorem rec7596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(17),[1,2,5,6,13,14],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1064]? = some (⟨157,(17),[1,2,5,6,13,14],[170],398⟩) from rfl))
private theorem rec7601 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(18),[1,2,5,6,13,14],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1069]? = some (⟨157,(18),[1,2,5,6,13,14],[170],398⟩) from rfl))
private theorem rec7606 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(19),[1,2,5,6,13,14],[170],398⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1074]? = some (⟨157,(19),[1,2,5,6,13,14],[170],398⟩) from rfl))
private theorem rec7611 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(20),[1,2,5,6,13,14],[170],24⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1079]? = some (⟨157,(20),[1,2,5,6,13,14],[170],24⟩) from rfl))
private theorem rec7615 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(21),[1,2,5,6,13,14],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1083]? = some (⟨157,(21),[1,2,5,6,13,14],[170],399⟩) from rfl))
private theorem rec7620 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(22),[1,2,5,6,13,14],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1088]? = some (⟨157,(22),[1,2,5,6,13,14],[170],399⟩) from rfl))
private theorem rec7625 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(23),[1,2,5,6,13,14],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1093]? = some (⟨157,(23),[1,2,5,6,13,14],[170],399⟩) from rfl))
private theorem rec7630 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 157 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨157,(24),[1,2,5,6,13,14],[170],399⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1098]? = some (⟨157,(24),[1,2,5,6,13,14],[170],399⟩) from rfl))
private theorem rec7635 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(0),[1,2,5,6,13,14],[170],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1103]? = some (⟨160,(0),[1,2,5,6,13,14],[170],638⟩) from rfl))
private theorem rec7642 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(1),[1,2,5,6,13,14],[170],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1110]? = some (⟨160,(1),[1,2,5,6,13,14],[170],639⟩) from rfl))
private theorem rec7649 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(2),[1,2,5,6,13,14],[170],640⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1117]? = some (⟨160,(2),[1,2,5,6,13,14],[170],640⟩) from rfl))
private theorem rec7656 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(3),[1,2,5,6,13,14],[170],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1124]? = some (⟨160,(3),[1,2,5,6,13,14],[170],641⟩) from rfl))
private theorem rec7663 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(4),[1,2,5,6,13,14],[170],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1131]? = some (⟨160,(4),[1,2,5,6,13,14],[170],638⟩) from rfl))
private theorem rec7670 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(5),[1,2,5,6,13,14],[170],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1138]? = some (⟨160,(5),[1,2,5,6,13,14],[170],639⟩) from rfl))
private theorem rec7677 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(6),[1,2,5,6,13,14],[170],642⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part6 (List.mem_of_getElem? (show section14DataRecords2Part3[1145]? = some (⟨160,(6),[1,2,5,6,13,14],[170],642⟩) from rfl))
private theorem rec7684 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(7),[1,2,5,6,13,14],[170],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[0]? = some (⟨160,(7),[1,2,5,6,13,14],[170],641⟩) from rfl))
private theorem rec7691 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(8),[1,2,5,6,13,14],[170],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[7]? = some (⟨160,(8),[1,2,5,6,13,14],[170],638⟩) from rfl))
private theorem rec7698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(9),[1,2,5,6,13,14],[170],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[14]? = some (⟨160,(9),[1,2,5,6,13,14],[170],639⟩) from rfl))
private theorem rec7705 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(10),[1,2,5,6,13,14],[170],640⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[21]? = some (⟨160,(10),[1,2,5,6,13,14],[170],640⟩) from rfl))
private theorem rec7712 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(11),[1,2,5,6,13,14],[170],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[28]? = some (⟨160,(11),[1,2,5,6,13,14],[170],641⟩) from rfl))
private theorem rec7719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(12),[1,2,5,6,13,14],[170],638⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[35]? = some (⟨160,(12),[1,2,5,6,13,14],[170],638⟩) from rfl))
private theorem rec7726 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(13),[1,2,5,6,13,14],[170],639⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[42]? = some (⟨160,(13),[1,2,5,6,13,14],[170],639⟩) from rfl))
private theorem rec7733 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(14),[1,2,5,6,13,14],[170],643⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[49]? = some (⟨160,(14),[1,2,5,6,13,14],[170],643⟩) from rfl))
private theorem rec7740 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 160 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨160,(15),[1,2,5,6,13,14],[170],641⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[56]? = some (⟨160,(15),[1,2,5,6,13,14],[170],641⟩) from rfl))
private theorem rec7747 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(0),[1,2,5,6,13,14],[170],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[63]? = some (⟨163,(0),[1,2,5,6,13,14],[170],406⟩) from rfl))
private theorem rec7755 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(1),[1,2,5,6,13,14],[170],407⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[71]? = some (⟨163,(1),[1,2,5,6,13,14],[170],407⟩) from rfl))
private theorem rec7763 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(2),[1,2,5,6,13,14],[170],406⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[79]? = some (⟨163,(2),[1,2,5,6,13,14],[170],406⟩) from rfl))
private theorem rec7771 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(3),[1,2,5,6,13,14],[170],408⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[87]? = some (⟨163,(3),[1,2,5,6,13,14],[170],408⟩) from rfl))
private theorem rec7779 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(4),[1,2,5,6,13,14],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[95]? = some (⟨163,(4),[1,2,5,6,13,14],[170],409⟩) from rfl))
private theorem rec7787 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(5),[1,2,5,6,13,14],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[103]? = some (⟨163,(5),[1,2,5,6,13,14],[170],409⟩) from rfl))
private theorem rec7795 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(6),[1,2,5,6,13,14],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[111]? = some (⟨163,(6),[1,2,5,6,13,14],[170],409⟩) from rfl))
private theorem rec7803 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(7),[1,2,5,6,13,14],[170],409⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[119]? = some (⟨163,(7),[1,2,5,6,13,14],[170],409⟩) from rfl))
private theorem rec7811 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(8),[1,2,5,6,13,14],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[127]? = some (⟨163,(8),[1,2,5,6,13,14],[170],410⟩) from rfl))
private theorem rec7819 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(9),[1,2,5,6,13,14],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[135]? = some (⟨163,(9),[1,2,5,6,13,14],[170],410⟩) from rfl))
private theorem rec7827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(10),[1,2,5,6,13,14],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[143]? = some (⟨163,(10),[1,2,5,6,13,14],[170],410⟩) from rfl))
private theorem rec7835 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(11),[1,2,5,6,13,14],[170],410⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[151]? = some (⟨163,(11),[1,2,5,6,13,14],[170],410⟩) from rfl))
private theorem rec7843 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(12),[1,2,5,6,13,14],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[159]? = some (⟨163,(12),[1,2,5,6,13,14],[170],411⟩) from rfl))
private theorem rec7851 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(13),[1,2,5,6,13,14],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[167]? = some (⟨163,(13),[1,2,5,6,13,14],[170],411⟩) from rfl))
private theorem rec7859 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(14),[1,2,5,6,13,14],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[175]? = some (⟨163,(14),[1,2,5,6,13,14],[170],411⟩) from rfl))
private theorem rec7867 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 163 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨163,(15),[1,2,5,6,13,14],[170],411⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[183]? = some (⟨163,(15),[1,2,5,6,13,14],[170],411⟩) from rfl))
private theorem rec7875 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(0),[1,2,5,6,13,14],[170],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[191]? = some (⟨166,(0),[1,2,5,6,13,14],[170],644⟩) from rfl))
private theorem rec7882 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(1),[1,2,5,6,13,14],[170],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[198]? = some (⟨166,(1),[1,2,5,6,13,14],[170],644⟩) from rfl))
private theorem rec7889 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(2),[1,2,5,6,13,14],[170],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[205]? = some (⟨166,(2),[1,2,5,6,13,14],[170],644⟩) from rfl))
private theorem rec7896 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(3),[1,2,5,6,13,14],[170],644⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[212]? = some (⟨166,(3),[1,2,5,6,13,14],[170],644⟩) from rfl))
private theorem rec7903 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(4),[1,2,5,6,13,14],[170],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[219]? = some (⟨166,(4),[1,2,5,6,13,14],[170],645⟩) from rfl))
private theorem rec7910 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(5),[1,2,5,6,13,14],[170],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[226]? = some (⟨166,(5),[1,2,5,6,13,14],[170],645⟩) from rfl))
private theorem rec7917 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(6),[1,2,5,6,13,14],[170],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[233]? = some (⟨166,(6),[1,2,5,6,13,14],[170],645⟩) from rfl))
private theorem rec7924 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(7),[1,2,5,6,13,14],[170],645⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[240]? = some (⟨166,(7),[1,2,5,6,13,14],[170],645⟩) from rfl))
private theorem rec7931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(8),[1,2,5,6,13,14],[170],646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[247]? = some (⟨166,(8),[1,2,5,6,13,14],[170],646⟩) from rfl))
private theorem rec7938 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(9),[1,2,5,6,13,14],[170],647⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[254]? = some (⟨166,(9),[1,2,5,6,13,14],[170],647⟩) from rfl))
private theorem rec7945 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(10),[1,2,5,6,13,14],[170],646⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[261]? = some (⟨166,(10),[1,2,5,6,13,14],[170],646⟩) from rfl))
private theorem rec7952 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[268]? = some (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) from rfl))
private theorem rec7959 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[275]? = some (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) from rfl))
private theorem rec7966 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[282]? = some (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) from rfl))
private theorem rec7973 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[289]? = some (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) from rfl))
private theorem rec7980 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 166 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[296]? = some (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) from rfl))
private theorem rec7987 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[303]? = some (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) from rfl))
private theorem rec7995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[311]? = some (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) from rfl))
private theorem rec8003 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[319]? = some (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) from rfl))
private theorem rec8011 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[327]? = some (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) from rfl))
private theorem rec8019 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[335]? = some (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) from rfl))
private theorem rec8027 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[343]? = some (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) from rfl))
private theorem rec8035 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[351]? = some (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) from rfl))
private theorem rec8043 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[359]? = some (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) from rfl))
private theorem rec8051 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[367]? = some (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) from rfl))
private theorem rec8059 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[375]? = some (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) from rfl))
private theorem rec8067 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[383]? = some (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) from rfl))
private theorem rec8075 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[391]? = some (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) from rfl))
private theorem rec8083 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[399]? = some (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) from rfl))
private theorem rec8091 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[407]? = some (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) from rfl))
private theorem rec8099 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[415]? = some (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) from rfl))
private theorem rec8107 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 167 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[423]? = some (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) from rfl))
private theorem rec8115 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 171 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[431]? = some (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) from rfl))
private theorem rec8122 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 171 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[438]? = some (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) from rfl))
private theorem rec8129 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 171 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[445]? = some (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) from rfl))
private theorem rec8136 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 171 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[452]? = some (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) from rfl))
private theorem rec8143 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[459]? = some (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) from rfl))
private theorem rec8151 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[467]? = some (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) from rfl))
private theorem rec8159 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[475]? = some (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) from rfl))
private theorem rec8167 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[483]? = some (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) from rfl))
private theorem rec8175 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[491]? = some (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) from rfl))
private theorem rec8183 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[499]? = some (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) from rfl))
private theorem rec8191 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[507]? = some (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) from rfl))
private theorem rec8199 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[515]? = some (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) from rfl))
private theorem rec8207 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[523]? = some (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) from rfl))
private theorem rec8215 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[531]? = some (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) from rfl))
private theorem rec8223 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[539]? = some (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) from rfl))
private theorem rec8231 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[547]? = some (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) from rfl))
private theorem rec8239 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[555]? = some (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) from rfl))
private theorem rec8247 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[563]? = some (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) from rfl))
private theorem rec8255 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[571]? = some (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) from rfl))
private theorem rec8263 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 172 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[579]? = some (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) from rfl))
private theorem rec8271 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[587]? = some (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) from rfl))
private theorem rec8278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[594]? = some (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) from rfl))
private theorem rec8285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(2),[1,2,5,6,13,14],[170],656⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[601]? = some (⟨175,(2),[1,2,5,6,13,14],[170],656⟩) from rfl))
private theorem rec8292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(3),[1,2,5,6,13,14],[170],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part7 (List.mem_of_getElem? (show section14DataRecords2Part4[608]? = some (⟨175,(3),[1,2,5,6,13,14],[170],657⟩) from rfl))
private theorem rec8299 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(4),[1,2,5,6,13,14],[170],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[0]? = some (⟨175,(4),[1,2,5,6,13,14],[170],654⟩) from rfl))
private theorem rec8306 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(5),[1,2,5,6,13,14],[170],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[7]? = some (⟨175,(5),[1,2,5,6,13,14],[170],655⟩) from rfl))
private theorem rec8313 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(6),[1,2,5,6,13,14],[170],658⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[14]? = some (⟨175,(6),[1,2,5,6,13,14],[170],658⟩) from rfl))
private theorem rec8320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(7),[1,2,5,6,13,14],[170],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[21]? = some (⟨175,(7),[1,2,5,6,13,14],[170],657⟩) from rfl))
private theorem rec8327 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(8),[1,2,5,6,13,14],[170],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[28]? = some (⟨175,(8),[1,2,5,6,13,14],[170],654⟩) from rfl))
private theorem rec8334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(9),[1,2,5,6,13,14],[170],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[35]? = some (⟨175,(9),[1,2,5,6,13,14],[170],655⟩) from rfl))
private theorem rec8341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(10),[1,2,5,6,13,14],[170],656⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[42]? = some (⟨175,(10),[1,2,5,6,13,14],[170],656⟩) from rfl))
private theorem rec8348 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(11),[1,2,5,6,13,14],[170],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[49]? = some (⟨175,(11),[1,2,5,6,13,14],[170],657⟩) from rfl))
private theorem rec8355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(12),[1,2,5,6,13,14],[170],654⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[56]? = some (⟨175,(12),[1,2,5,6,13,14],[170],654⟩) from rfl))
private theorem rec8362 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(13),[1,2,5,6,13,14],[170],655⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[63]? = some (⟨175,(13),[1,2,5,6,13,14],[170],655⟩) from rfl))
private theorem rec8369 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(14),[1,2,5,6,13,14],[170],659⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[70]? = some (⟨175,(14),[1,2,5,6,13,14],[170],659⟩) from rfl))
private theorem rec8376 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 175 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨175,(15),[1,2,5,6,13,14],[170],657⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[77]? = some (⟨175,(15),[1,2,5,6,13,14],[170],657⟩) from rfl))
private theorem rec8383 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(0),[1,2,5,6,13,14],[170],660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[84]? = some (⟨178,(0),[1,2,5,6,13,14],[170],660⟩) from rfl))
private theorem rec8391 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(1),[1,2,5,6,13,14],[170],661⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[92]? = some (⟨178,(1),[1,2,5,6,13,14],[170],661⟩) from rfl))
private theorem rec8399 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(2),[1,2,5,6,13,14],[170],660⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[100]? = some (⟨178,(2),[1,2,5,6,13,14],[170],660⟩) from rfl))
private theorem rec8407 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(3),[1,2,5,6,13,14],[170],662⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[108]? = some (⟨178,(3),[1,2,5,6,13,14],[170],662⟩) from rfl))
private theorem rec8415 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(4),[1,2,5,6,13,14],[170],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[116]? = some (⟨178,(4),[1,2,5,6,13,14],[170],663⟩) from rfl))
private theorem rec8423 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(5),[1,2,5,6,13,14],[170],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[124]? = some (⟨178,(5),[1,2,5,6,13,14],[170],663⟩) from rfl))
private theorem rec8431 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(6),[1,2,5,6,13,14],[170],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[132]? = some (⟨178,(6),[1,2,5,6,13,14],[170],663⟩) from rfl))
private theorem rec8439 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(7),[1,2,5,6,13,14],[170],663⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[140]? = some (⟨178,(7),[1,2,5,6,13,14],[170],663⟩) from rfl))
private theorem rec8447 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(8),[1,2,5,6,13,14],[170],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[148]? = some (⟨178,(8),[1,2,5,6,13,14],[170],664⟩) from rfl))
private theorem rec8455 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(9),[1,2,5,6,13,14],[170],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[156]? = some (⟨178,(9),[1,2,5,6,13,14],[170],664⟩) from rfl))
private theorem rec8463 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(10),[1,2,5,6,13,14],[170],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[164]? = some (⟨178,(10),[1,2,5,6,13,14],[170],664⟩) from rfl))
private theorem rec8471 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(11),[1,2,5,6,13,14],[170],664⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[172]? = some (⟨178,(11),[1,2,5,6,13,14],[170],664⟩) from rfl))
private theorem rec8479 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(12),[1,2,5,6,13,14],[170],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[180]? = some (⟨178,(12),[1,2,5,6,13,14],[170],665⟩) from rfl))
private theorem rec8487 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(13),[1,2,5,6,13,14],[170],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[188]? = some (⟨178,(13),[1,2,5,6,13,14],[170],665⟩) from rfl))
private theorem rec8495 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(14),[1,2,5,6,13,14],[170],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[196]? = some (⟨178,(14),[1,2,5,6,13,14],[170],665⟩) from rfl))
private theorem rec8503 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 178 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨178,(15),[1,2,5,6,13,14],[170],665⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[204]? = some (⟨178,(15),[1,2,5,6,13,14],[170],665⟩) from rfl))
private theorem rec8511 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(0),[1,2,5,6,13,14],[170],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[212]? = some (⟨180,(0),[1,2,5,6,13,14],[170],666⟩) from rfl))
private theorem rec8518 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(1),[1,2,5,6,13,14],[170],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[219]? = some (⟨180,(1),[1,2,5,6,13,14],[170],667⟩) from rfl))
private theorem rec8525 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(2),[1,2,5,6,13,14],[170],668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[226]? = some (⟨180,(2),[1,2,5,6,13,14],[170],668⟩) from rfl))
private theorem rec8532 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(3),[1,2,5,6,13,14],[170],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[233]? = some (⟨180,(3),[1,2,5,6,13,14],[170],669⟩) from rfl))
private theorem rec8539 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(4),[1,2,5,6,13,14],[170],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[240]? = some (⟨180,(4),[1,2,5,6,13,14],[170],666⟩) from rfl))
private theorem rec8546 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(5),[1,2,5,6,13,14],[170],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[247]? = some (⟨180,(5),[1,2,5,6,13,14],[170],667⟩) from rfl))
private theorem rec8553 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(6),[1,2,5,6,13,14],[170],670⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[254]? = some (⟨180,(6),[1,2,5,6,13,14],[170],670⟩) from rfl))
private theorem rec8560 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(7),[1,2,5,6,13,14],[170],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[261]? = some (⟨180,(7),[1,2,5,6,13,14],[170],669⟩) from rfl))
private theorem rec8567 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(8),[1,2,5,6,13,14],[170],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[268]? = some (⟨180,(8),[1,2,5,6,13,14],[170],666⟩) from rfl))
private theorem rec8574 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(9),[1,2,5,6,13,14],[170],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[275]? = some (⟨180,(9),[1,2,5,6,13,14],[170],667⟩) from rfl))
private theorem rec8581 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(10),[1,2,5,6,13,14],[170],668⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[282]? = some (⟨180,(10),[1,2,5,6,13,14],[170],668⟩) from rfl))
private theorem rec8588 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(11),[1,2,5,6,13,14],[170],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[289]? = some (⟨180,(11),[1,2,5,6,13,14],[170],669⟩) from rfl))
private theorem rec8595 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(12),[1,2,5,6,13,14],[170],666⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[296]? = some (⟨180,(12),[1,2,5,6,13,14],[170],666⟩) from rfl))
private theorem rec8602 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(13),[1,2,5,6,13,14],[170],667⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[303]? = some (⟨180,(13),[1,2,5,6,13,14],[170],667⟩) from rfl))
private theorem rec8609 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(14),[1,2,5,6,13,14],[170],671⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[310]? = some (⟨180,(14),[1,2,5,6,13,14],[170],671⟩) from rfl))
private theorem rec8616 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 180 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨180,(15),[1,2,5,6,13,14],[170],669⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[317]? = some (⟨180,(15),[1,2,5,6,13,14],[170],669⟩) from rfl))
private theorem rec8623 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(0),[1,2,5,6,13,14],[170],672⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[324]? = some (⟨183,(0),[1,2,5,6,13,14],[170],672⟩) from rfl))
private theorem rec8631 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(1),[1,2,5,6,13,14],[170],673⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[332]? = some (⟨183,(1),[1,2,5,6,13,14],[170],673⟩) from rfl))
private theorem rec8639 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(2),[1,2,5,6,13,14],[170],672⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[340]? = some (⟨183,(2),[1,2,5,6,13,14],[170],672⟩) from rfl))
private theorem rec8647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(3),[1,2,5,6,13,14],[170],674⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[348]? = some (⟨183,(3),[1,2,5,6,13,14],[170],674⟩) from rfl))
private theorem rec8655 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(4),[1,2,5,6,13,14],[170],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[356]? = some (⟨183,(4),[1,2,5,6,13,14],[170],675⟩) from rfl))
private theorem rec8663 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(5),[1,2,5,6,13,14],[170],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[364]? = some (⟨183,(5),[1,2,5,6,13,14],[170],675⟩) from rfl))
private theorem rec8671 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(6),[1,2,5,6,13,14],[170],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[372]? = some (⟨183,(6),[1,2,5,6,13,14],[170],675⟩) from rfl))
private theorem rec8679 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(7),[1,2,5,6,13,14],[170],675⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[380]? = some (⟨183,(7),[1,2,5,6,13,14],[170],675⟩) from rfl))
private theorem rec8687 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(8),[1,2,5,6,13,14],[170],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[388]? = some (⟨183,(8),[1,2,5,6,13,14],[170],676⟩) from rfl))
private theorem rec8695 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(9),[1,2,5,6,13,14],[170],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[396]? = some (⟨183,(9),[1,2,5,6,13,14],[170],676⟩) from rfl))
private theorem rec8703 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(10),[1,2,5,6,13,14],[170],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[404]? = some (⟨183,(10),[1,2,5,6,13,14],[170],676⟩) from rfl))
private theorem rec8711 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(11),[1,2,5,6,13,14],[170],676⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[412]? = some (⟨183,(11),[1,2,5,6,13,14],[170],676⟩) from rfl))
private theorem rec8719 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(12),[1,2,5,6,13,14],[170],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[420]? = some (⟨183,(12),[1,2,5,6,13,14],[170],677⟩) from rfl))
private theorem rec8727 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(13),[1,2,5,6,13,14],[170],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[428]? = some (⟨183,(13),[1,2,5,6,13,14],[170],677⟩) from rfl))
private theorem rec8735 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(14),[1,2,5,6,13,14],[170],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[436]? = some (⟨183,(14),[1,2,5,6,13,14],[170],677⟩) from rfl))
private theorem rec8743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 183 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨183,(15),[1,2,5,6,13,14],[170],677⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[444]? = some (⟨183,(15),[1,2,5,6,13,14],[170],677⟩) from rfl))
private theorem rec8751 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(0),[1,2,5,6,13,14],[170],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[452]? = some (⟨185,(0),[1,2,5,6,13,14],[170],678⟩) from rfl))
private theorem rec8758 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(1),[1,2,5,6,13,14],[170],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[459]? = some (⟨185,(1),[1,2,5,6,13,14],[170],679⟩) from rfl))
private theorem rec8765 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(2),[1,2,5,6,13,14],[170],680⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[466]? = some (⟨185,(2),[1,2,5,6,13,14],[170],680⟩) from rfl))
private theorem rec8772 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(3),[1,2,5,6,13,14],[170],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[473]? = some (⟨185,(3),[1,2,5,6,13,14],[170],681⟩) from rfl))
private theorem rec8779 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(4),[1,2,5,6,13,14],[170],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[480]? = some (⟨185,(4),[1,2,5,6,13,14],[170],678⟩) from rfl))
private theorem rec8786 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(5),[1,2,5,6,13,14],[170],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[487]? = some (⟨185,(5),[1,2,5,6,13,14],[170],679⟩) from rfl))
private theorem rec8793 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(6),[1,2,5,6,13,14],[170],682⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[494]? = some (⟨185,(6),[1,2,5,6,13,14],[170],682⟩) from rfl))
private theorem rec8800 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(7),[1,2,5,6,13,14],[170],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[501]? = some (⟨185,(7),[1,2,5,6,13,14],[170],681⟩) from rfl))
private theorem rec8807 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(8),[1,2,5,6,13,14],[170],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[508]? = some (⟨185,(8),[1,2,5,6,13,14],[170],678⟩) from rfl))
private theorem rec8814 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(9),[1,2,5,6,13,14],[170],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[515]? = some (⟨185,(9),[1,2,5,6,13,14],[170],679⟩) from rfl))
private theorem rec8821 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(10),[1,2,5,6,13,14],[170],680⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[522]? = some (⟨185,(10),[1,2,5,6,13,14],[170],680⟩) from rfl))
private theorem rec8828 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(11),[1,2,5,6,13,14],[170],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[529]? = some (⟨185,(11),[1,2,5,6,13,14],[170],681⟩) from rfl))
private theorem rec8835 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(12),[1,2,5,6,13,14],[170],678⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[536]? = some (⟨185,(12),[1,2,5,6,13,14],[170],678⟩) from rfl))
private theorem rec8842 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(13),[1,2,5,6,13,14],[170],679⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[543]? = some (⟨185,(13),[1,2,5,6,13,14],[170],679⟩) from rfl))
private theorem rec8849 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(14),[1,2,5,6,13,14],[170],683⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[550]? = some (⟨185,(14),[1,2,5,6,13,14],[170],683⟩) from rfl))
private theorem rec8856 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 185 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨185,(15),[1,2,5,6,13,14],[170],681⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[557]? = some (⟨185,(15),[1,2,5,6,13,14],[170],681⟩) from rfl))
private theorem rec8863 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(0),[1,2,5,6,13,14],[170],684⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[564]? = some (⟨188,(0),[1,2,5,6,13,14],[170],684⟩) from rfl))
private theorem rec8871 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(1),[1,2,5,6,13,14],[170],685⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[572]? = some (⟨188,(1),[1,2,5,6,13,14],[170],685⟩) from rfl))
private theorem rec8879 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(2),[1,2,5,6,13,14],[170],684⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[580]? = some (⟨188,(2),[1,2,5,6,13,14],[170],684⟩) from rfl))
private theorem rec8887 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(3),[1,2,5,6,13,14],[170],686⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[588]? = some (⟨188,(3),[1,2,5,6,13,14],[170],686⟩) from rfl))
private theorem rec8895 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(4),[1,2,5,6,13,14],[170],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[596]? = some (⟨188,(4),[1,2,5,6,13,14],[170],687⟩) from rfl))
private theorem rec8903 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(5),[1,2,5,6,13,14],[170],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[604]? = some (⟨188,(5),[1,2,5,6,13,14],[170],687⟩) from rfl))
private theorem rec8911 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(6),[1,2,5,6,13,14],[170],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[612]? = some (⟨188,(6),[1,2,5,6,13,14],[170],687⟩) from rfl))
private theorem rec8919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(7),[1,2,5,6,13,14],[170],687⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[620]? = some (⟨188,(7),[1,2,5,6,13,14],[170],687⟩) from rfl))
private theorem rec8927 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(8),[1,2,5,6,13,14],[170],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[628]? = some (⟨188,(8),[1,2,5,6,13,14],[170],688⟩) from rfl))
private theorem rec8935 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(9),[1,2,5,6,13,14],[170],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[636]? = some (⟨188,(9),[1,2,5,6,13,14],[170],688⟩) from rfl))
private theorem rec8943 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(10),[1,2,5,6,13,14],[170],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[644]? = some (⟨188,(10),[1,2,5,6,13,14],[170],688⟩) from rfl))
private theorem rec8951 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(11),[1,2,5,6,13,14],[170],688⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[652]? = some (⟨188,(11),[1,2,5,6,13,14],[170],688⟩) from rfl))
private theorem rec8959 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(12),[1,2,5,6,13,14],[170],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[660]? = some (⟨188,(12),[1,2,5,6,13,14],[170],689⟩) from rfl))
private theorem rec8967 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(13),[1,2,5,6,13,14],[170],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[668]? = some (⟨188,(13),[1,2,5,6,13,14],[170],689⟩) from rfl))
private theorem rec8975 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(14),[1,2,5,6,13,14],[170],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[676]? = some (⟨188,(14),[1,2,5,6,13,14],[170],689⟩) from rfl))
private theorem rec8983 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 188 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨188,(15),[1,2,5,6,13,14],[170],689⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[684]? = some (⟨188,(15),[1,2,5,6,13,14],[170],689⟩) from rfl))
private theorem rec8991 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(0),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[692]? = some (⟨190,(0),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec8998 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(1),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[699]? = some (⟨190,(1),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec9005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(2),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[706]? = some (⟨190,(2),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec9012 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(3),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[713]? = some (⟨190,(3),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec9019 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(4),[1,2,5,6,13,14],[170],690⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[720]? = some (⟨190,(4),[1,2,5,6,13,14],[170],690⟩) from rfl))
private theorem rec9026 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(5),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[727]? = some (⟨190,(5),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9033 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(6),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[734]? = some (⟨190,(6),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9040 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(7),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[741]? = some (⟨190,(7),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9047 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(8),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[748]? = some (⟨190,(8),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9054 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(9),[1,2,5,6,13,14],[170],691⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[755]? = some (⟨190,(9),[1,2,5,6,13,14],[170],691⟩) from rfl))
private theorem rec9061 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(10),[1,2,5,6,13,14],[170],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[762]? = some (⟨190,(10),[1,2,5,6,13,14],[170],692⟩) from rfl))
private theorem rec9068 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(11),[1,2,5,6,13,14],[170],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[769]? = some (⟨190,(11),[1,2,5,6,13,14],[170],693⟩) from rfl))
private theorem rec9075 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(12),[1,2,5,6,13,14],[170],694⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[776]? = some (⟨190,(12),[1,2,5,6,13,14],[170],694⟩) from rfl))
private theorem rec9082 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(13),[1,2,5,6,13,14],[170],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[783]? = some (⟨190,(13),[1,2,5,6,13,14],[170],693⟩) from rfl))
private theorem rec9089 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(14),[1,2,5,6,13,14],[170],695⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[790]? = some (⟨190,(14),[1,2,5,6,13,14],[170],695⟩) from rfl))
private theorem rec9096 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(15),[1,2,5,6,13,14],[170],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[797]? = some (⟨190,(15),[1,2,5,6,13,14],[170],692⟩) from rfl))
private theorem rec9103 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(16),[1,2,5,6,13,14],[170],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[804]? = some (⟨190,(16),[1,2,5,6,13,14],[170],696⟩) from rfl))
private theorem rec9110 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(17),[1,2,5,6,13,14],[170],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[811]? = some (⟨190,(17),[1,2,5,6,13,14],[170],696⟩) from rfl))
private theorem rec9117 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(18),[1,2,5,6,13,14],[170],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[818]? = some (⟨190,(18),[1,2,5,6,13,14],[170],696⟩) from rfl))
private theorem rec9124 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(19),[1,2,5,6,13,14],[170],696⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[825]? = some (⟨190,(19),[1,2,5,6,13,14],[170],696⟩) from rfl))
private theorem rec9131 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(20),[1,2,5,6,13,14],[170],692⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[832]? = some (⟨190,(20),[1,2,5,6,13,14],[170],692⟩) from rfl))
private theorem rec9138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(21),[1,2,5,6,13,14],[170],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[839]? = some (⟨190,(21),[1,2,5,6,13,14],[170],693⟩) from rfl))
private theorem rec9145 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(22),[1,2,5,6,13,14],[170],694⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[846]? = some (⟨190,(22),[1,2,5,6,13,14],[170],694⟩) from rfl))
private theorem rec9152 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(23),[1,2,5,6,13,14],[170],693⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[853]? = some (⟨190,(23),[1,2,5,6,13,14],[170],693⟩) from rfl))
private theorem rec9159 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 190 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨190,(24),[1,2,5,6,13,14],[170],695⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[860]? = some (⟨190,(24),[1,2,5,6,13,14],[170],695⟩) from rfl))
private theorem rec9166 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(0),[1,2,5,6,13,14],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[867]? = some (⟨192,(0),[1,2,5,6,13,14],[170],441⟩) from rfl))
private theorem rec9174 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(1),[1,2,5,6,13,14],[170],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[875]? = some (⟨192,(1),[1,2,5,6,13,14],[170],442⟩) from rfl))
private theorem rec9182 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(2),[1,2,5,6,13,14],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[883]? = some (⟨192,(2),[1,2,5,6,13,14],[170],441⟩) from rfl))
private theorem rec9190 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(3),[1,2,5,6,13,14],[170],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[891]? = some (⟨192,(3),[1,2,5,6,13,14],[170],443⟩) from rfl))
private theorem rec9198 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(4),[1,2,5,6,13,14],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[899]? = some (⟨192,(4),[1,2,5,6,13,14],[170],444⟩) from rfl))
private theorem rec9206 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(5),[1,2,5,6,13,14],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[907]? = some (⟨192,(5),[1,2,5,6,13,14],[170],441⟩) from rfl))
private theorem rec9214 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(6),[1,2,5,6,13,14],[170],442⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[915]? = some (⟨192,(6),[1,2,5,6,13,14],[170],442⟩) from rfl))
private theorem rec9222 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(7),[1,2,5,6,13,14],[170],441⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[923]? = some (⟨192,(7),[1,2,5,6,13,14],[170],441⟩) from rfl))
private theorem rec9230 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(8),[1,2,5,6,13,14],[170],443⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[931]? = some (⟨192,(8),[1,2,5,6,13,14],[170],443⟩) from rfl))
private theorem rec9238 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(9),[1,2,5,6,13,14],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[939]? = some (⟨192,(9),[1,2,5,6,13,14],[170],444⟩) from rfl))
private theorem rec9246 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(10),[1,2,5,6,13,14],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[947]? = some (⟨192,(10),[1,2,5,6,13,14],[170],445⟩) from rfl))
private theorem rec9254 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(11),[1,2,5,6,13,14],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[955]? = some (⟨192,(11),[1,2,5,6,13,14],[170],445⟩) from rfl))
private theorem rec9262 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(12),[1,2,5,6,13,14],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[963]? = some (⟨192,(12),[1,2,5,6,13,14],[170],445⟩) from rfl))
private theorem rec9270 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(13),[1,2,5,6,13,14],[170],445⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[971]? = some (⟨192,(13),[1,2,5,6,13,14],[170],445⟩) from rfl))
private theorem rec9278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(14),[1,2,5,6,13,14],[170],444⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[979]? = some (⟨192,(14),[1,2,5,6,13,14],[170],444⟩) from rfl))
private theorem rec9286 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(15),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[987]? = some (⟨192,(15),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9294 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(16),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[995]? = some (⟨192,(16),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9302 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(17),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1003]? = some (⟨192,(17),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9310 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(18),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1011]? = some (⟨192,(18),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9318 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(19),[1,2,5,6,13,14],[170],446⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1019]? = some (⟨192,(19),[1,2,5,6,13,14],[170],446⟩) from rfl))
private theorem rec9326 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(20),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1027]? = some (⟨192,(20),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(21),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1035]? = some (⟨192,(21),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9342 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(22),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1043]? = some (⟨192,(22),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9350 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(23),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1051]? = some (⟨192,(23),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9358 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 192 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨192,(24),[1,2,5,6,13,14],[170],447⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1059]? = some (⟨192,(24),[1,2,5,6,13,14],[170],447⟩) from rfl))
private theorem rec9366 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(0),[1,2,5,6,13,14],[170],697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1067]? = some (⟨195,(0),[1,2,5,6,13,14],[170],697⟩) from rfl))
private theorem rec9373 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(1),[1,2,5,6,13,14],[170],697⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1074]? = some (⟨195,(1),[1,2,5,6,13,14],[170],697⟩) from rfl))
private theorem rec9380 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(2),[1,2,5,6,13,14],[170],698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1081]? = some (⟨195,(2),[1,2,5,6,13,14],[170],698⟩) from rfl))
private theorem rec9387 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(3),[1,2,5,6,13,14],[170],698⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1088]? = some (⟨195,(3),[1,2,5,6,13,14],[170],698⟩) from rfl))
private theorem rec9394 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(4),[1,2,5,6,13,14],[170],699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1095]? = some (⟨195,(4),[1,2,5,6,13,14],[170],699⟩) from rfl))
private theorem rec9401 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(5),[1,2,5,6,13,14],[170],700⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1102]? = some (⟨195,(5),[1,2,5,6,13,14],[170],700⟩) from rfl))
private theorem rec9408 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(6),[1,2,5,6,13,14],[170],699⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1109]? = some (⟨195,(6),[1,2,5,6,13,14],[170],699⟩) from rfl))
private theorem rec9415 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(7),[1,2,5,6,13,14],[170],701⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1116]? = some (⟨195,(7),[1,2,5,6,13,14],[170],701⟩) from rfl))
private theorem rec9422 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(8),[1,2,5,6,13,14],[170],702⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1123]? = some (⟨195,(8),[1,2,5,6,13,14],[170],702⟩) from rfl))
private theorem rec9429 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 195 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨195,(9),[1,2,5,6,13,14],[170],703⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1130]? = some (⟨195,(9),[1,2,5,6,13,14],[170],703⟩) from rfl))
private theorem rec9436 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(0),[1,2,5,6,13,14],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1137]? = some (⟨197,(0),[1,2,5,6,13,14],[170],453⟩) from rfl))
private theorem rec9444 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(1),[1,2,5,6,13,14],[170],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1145]? = some (⟨197,(1),[1,2,5,6,13,14],[170],454⟩) from rfl))
private theorem rec9452 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(2),[1,2,5,6,13,14],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1153]? = some (⟨197,(2),[1,2,5,6,13,14],[170],453⟩) from rfl))
private theorem rec9460 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(3),[1,2,5,6,13,14],[170],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1161]? = some (⟨197,(3),[1,2,5,6,13,14],[170],455⟩) from rfl))
private theorem rec9468 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(4),[1,2,5,6,13,14],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1169]? = some (⟨197,(4),[1,2,5,6,13,14],[170],456⟩) from rfl))
private theorem rec9476 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(5),[1,2,5,6,13,14],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1177]? = some (⟨197,(5),[1,2,5,6,13,14],[170],453⟩) from rfl))
private theorem rec9484 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(6),[1,2,5,6,13,14],[170],454⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1185]? = some (⟨197,(6),[1,2,5,6,13,14],[170],454⟩) from rfl))
private theorem rec9492 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(7),[1,2,5,6,13,14],[170],453⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1193]? = some (⟨197,(7),[1,2,5,6,13,14],[170],453⟩) from rfl))
private theorem rec9500 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(8),[1,2,5,6,13,14],[170],455⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1201]? = some (⟨197,(8),[1,2,5,6,13,14],[170],455⟩) from rfl))
private theorem rec9508 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(9),[1,2,5,6,13,14],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1209]? = some (⟨197,(9),[1,2,5,6,13,14],[170],456⟩) from rfl))
private theorem rec9516 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(10),[1,2,5,6,13,14],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part8 (List.mem_of_getElem? (show section14DataRecords3Part1[1217]? = some (⟨197,(10),[1,2,5,6,13,14],[170],457⟩) from rfl))
private theorem rec9524 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(11),[1,2,5,6,13,14],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[6]? = some (⟨197,(11),[1,2,5,6,13,14],[170],457⟩) from rfl))
private theorem rec9532 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(12),[1,2,5,6,13,14],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[14]? = some (⟨197,(12),[1,2,5,6,13,14],[170],457⟩) from rfl))
private theorem rec9540 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(13),[1,2,5,6,13,14],[170],457⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[22]? = some (⟨197,(13),[1,2,5,6,13,14],[170],457⟩) from rfl))
private theorem rec9548 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(14),[1,2,5,6,13,14],[170],456⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[30]? = some (⟨197,(14),[1,2,5,6,13,14],[170],456⟩) from rfl))
private theorem rec9556 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(15),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[38]? = some (⟨197,(15),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9564 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(16),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[46]? = some (⟨197,(16),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9572 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(17),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[54]? = some (⟨197,(17),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9580 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(18),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[62]? = some (⟨197,(18),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9588 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(19),[1,2,5,6,13,14],[170],458⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[70]? = some (⟨197,(19),[1,2,5,6,13,14],[170],458⟩) from rfl))
private theorem rec9596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(20),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[78]? = some (⟨197,(20),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9604 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(21),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[86]? = some (⟨197,(21),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9612 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(22),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[94]? = some (⟨197,(22),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9620 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(23),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[102]? = some (⟨197,(23),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9628 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 197 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨197,(24),[1,2,5,6,13,14],[170],459⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[110]? = some (⟨197,(24),[1,2,5,6,13,14],[170],459⟩) from rfl))
private theorem rec9636 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(0),[1,2,5,6,13,14],[170],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[118]? = some (⟨200,(0),[1,2,5,6,13,14],[170],704⟩) from rfl))
private theorem rec9643 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(1),[1,2,5,6,13,14],[170],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[125]? = some (⟨200,(1),[1,2,5,6,13,14],[170],704⟩) from rfl))
private theorem rec9650 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(2),[1,2,5,6,13,14],[170],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[132]? = some (⟨200,(2),[1,2,5,6,13,14],[170],704⟩) from rfl))
private theorem rec9657 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(3),[1,2,5,6,13,14],[170],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[139]? = some (⟨200,(3),[1,2,5,6,13,14],[170],704⟩) from rfl))
private theorem rec9664 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(4),[1,2,5,6,13,14],[170],704⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[146]? = some (⟨200,(4),[1,2,5,6,13,14],[170],704⟩) from rfl))
private theorem rec9671 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(5),[1,2,5,6,13,14],[170],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[153]? = some (⟨200,(5),[1,2,5,6,13,14],[170],705⟩) from rfl))
private theorem rec9678 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(6),[1,2,5,6,13,14],[170],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[160]? = some (⟨200,(6),[1,2,5,6,13,14],[170],705⟩) from rfl))
private theorem rec9685 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(7),[1,2,5,6,13,14],[170],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[167]? = some (⟨200,(7),[1,2,5,6,13,14],[170],705⟩) from rfl))
private theorem rec9692 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(8),[1,2,5,6,13,14],[170],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[174]? = some (⟨200,(8),[1,2,5,6,13,14],[170],705⟩) from rfl))
private theorem rec9699 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(9),[1,2,5,6,13,14],[170],705⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[181]? = some (⟨200,(9),[1,2,5,6,13,14],[170],705⟩) from rfl))
private theorem rec9706 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(10),[1,2,5,6,13,14],[170],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[188]? = some (⟨200,(10),[1,2,5,6,13,14],[170],706⟩) from rfl))
private theorem rec9713 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(11),[1,2,5,6,13,14],[170],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[195]? = some (⟨200,(11),[1,2,5,6,13,14],[170],707⟩) from rfl))
private theorem rec9720 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(12),[1,2,5,6,13,14],[170],708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[202]? = some (⟨200,(12),[1,2,5,6,13,14],[170],708⟩) from rfl))
private theorem rec9727 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(13),[1,2,5,6,13,14],[170],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[209]? = some (⟨200,(13),[1,2,5,6,13,14],[170],707⟩) from rfl))
private theorem rec9734 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(14),[1,2,5,6,13,14],[170],709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[216]? = some (⟨200,(14),[1,2,5,6,13,14],[170],709⟩) from rfl))
private theorem rec9741 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(15),[1,2,5,6,13,14],[170],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[223]? = some (⟨200,(15),[1,2,5,6,13,14],[170],706⟩) from rfl))
private theorem rec9748 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(16),[1,2,5,6,13,14],[170],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[230]? = some (⟨200,(16),[1,2,5,6,13,14],[170],710⟩) from rfl))
private theorem rec9755 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(17),[1,2,5,6,13,14],[170],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[237]? = some (⟨200,(17),[1,2,5,6,13,14],[170],710⟩) from rfl))
private theorem rec9762 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(18),[1,2,5,6,13,14],[170],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[244]? = some (⟨200,(18),[1,2,5,6,13,14],[170],710⟩) from rfl))
private theorem rec9769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(19),[1,2,5,6,13,14],[170],710⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[251]? = some (⟨200,(19),[1,2,5,6,13,14],[170],710⟩) from rfl))
private theorem rec9776 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(20),[1,2,5,6,13,14],[170],706⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[258]? = some (⟨200,(20),[1,2,5,6,13,14],[170],706⟩) from rfl))
private theorem rec9783 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(21),[1,2,5,6,13,14],[170],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[265]? = some (⟨200,(21),[1,2,5,6,13,14],[170],707⟩) from rfl))
private theorem rec9790 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(22),[1,2,5,6,13,14],[170],708⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[272]? = some (⟨200,(22),[1,2,5,6,13,14],[170],708⟩) from rfl))
private theorem rec9797 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(23),[1,2,5,6,13,14],[170],707⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[279]? = some (⟨200,(23),[1,2,5,6,13,14],[170],707⟩) from rfl))
private theorem rec9804 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 200 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨200,(24),[1,2,5,6,13,14],[170],709⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[286]? = some (⟨200,(24),[1,2,5,6,13,14],[170],709⟩) from rfl))
private theorem rec9811 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(0),[1,2,5,6,13,14],[170],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[293]? = some (⟨202,(0),[1,2,5,6,13,14],[170],467⟩) from rfl))
private theorem rec9819 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(1),[1,2,5,6,13,14],[170],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[301]? = some (⟨202,(1),[1,2,5,6,13,14],[170],468⟩) from rfl))
private theorem rec9827 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(2),[1,2,5,6,13,14],[170],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[309]? = some (⟨202,(2),[1,2,5,6,13,14],[170],467⟩) from rfl))
private theorem rec9835 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(3),[1,2,5,6,13,14],[170],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[317]? = some (⟨202,(3),[1,2,5,6,13,14],[170],469⟩) from rfl))
private theorem rec9843 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(4),[1,2,5,6,13,14],[170],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[325]? = some (⟨202,(4),[1,2,5,6,13,14],[170],470⟩) from rfl))
private theorem rec9851 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(5),[1,2,5,6,13,14],[170],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[333]? = some (⟨202,(5),[1,2,5,6,13,14],[170],467⟩) from rfl))
private theorem rec9859 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(6),[1,2,5,6,13,14],[170],468⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[341]? = some (⟨202,(6),[1,2,5,6,13,14],[170],468⟩) from rfl))
private theorem rec9867 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(7),[1,2,5,6,13,14],[170],467⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[349]? = some (⟨202,(7),[1,2,5,6,13,14],[170],467⟩) from rfl))
private theorem rec9875 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(8),[1,2,5,6,13,14],[170],469⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[357]? = some (⟨202,(8),[1,2,5,6,13,14],[170],469⟩) from rfl))
private theorem rec9883 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(9),[1,2,5,6,13,14],[170],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[365]? = some (⟨202,(9),[1,2,5,6,13,14],[170],470⟩) from rfl))
private theorem rec9891 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(10),[1,2,5,6,13,14],[170],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[373]? = some (⟨202,(10),[1,2,5,6,13,14],[170],471⟩) from rfl))
private theorem rec9899 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(11),[1,2,5,6,13,14],[170],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[381]? = some (⟨202,(11),[1,2,5,6,13,14],[170],471⟩) from rfl))
private theorem rec9907 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(12),[1,2,5,6,13,14],[170],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[389]? = some (⟨202,(12),[1,2,5,6,13,14],[170],471⟩) from rfl))
private theorem rec9915 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(13),[1,2,5,6,13,14],[170],471⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[397]? = some (⟨202,(13),[1,2,5,6,13,14],[170],471⟩) from rfl))
private theorem rec9923 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(14),[1,2,5,6,13,14],[170],470⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[405]? = some (⟨202,(14),[1,2,5,6,13,14],[170],470⟩) from rfl))
private theorem rec9931 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(15),[1,2,5,6,13,14],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[413]? = some (⟨202,(15),[1,2,5,6,13,14],[170],472⟩) from rfl))
private theorem rec9939 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(16),[1,2,5,6,13,14],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[421]? = some (⟨202,(16),[1,2,5,6,13,14],[170],472⟩) from rfl))
private theorem rec9947 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(17),[1,2,5,6,13,14],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[429]? = some (⟨202,(17),[1,2,5,6,13,14],[170],472⟩) from rfl))
private theorem rec9955 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(18),[1,2,5,6,13,14],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[437]? = some (⟨202,(18),[1,2,5,6,13,14],[170],472⟩) from rfl))
private theorem rec9963 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(19),[1,2,5,6,13,14],[170],472⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[445]? = some (⟨202,(19),[1,2,5,6,13,14],[170],472⟩) from rfl))
private theorem rec9971 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(20),[1,2,5,6,13,14],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[453]? = some (⟨202,(20),[1,2,5,6,13,14],[170],473⟩) from rfl))
private theorem rec9979 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(21),[1,2,5,6,13,14],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[461]? = some (⟨202,(21),[1,2,5,6,13,14],[170],473⟩) from rfl))
private theorem rec9987 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(22),[1,2,5,6,13,14],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[469]? = some (⟨202,(22),[1,2,5,6,13,14],[170],473⟩) from rfl))
private theorem rec9995 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(23),[1,2,5,6,13,14],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[477]? = some (⟨202,(23),[1,2,5,6,13,14],[170],473⟩) from rfl))
private theorem rec10003 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 202 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨202,(24),[1,2,5,6,13,14],[170],473⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[485]? = some (⟨202,(24),[1,2,5,6,13,14],[170],473⟩) from rfl))
private theorem rec10011 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(0),[1,2,5,6,13,14],[170],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[493]? = some (⟨205,(0),[1,2,5,6,13,14],[170],711⟩) from rfl))
private theorem rec10018 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(1),[1,2,5,6,13,14],[170],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[500]? = some (⟨205,(1),[1,2,5,6,13,14],[170],711⟩) from rfl))
private theorem rec10025 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(2),[1,2,5,6,13,14],[170],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[507]? = some (⟨205,(2),[1,2,5,6,13,14],[170],711⟩) from rfl))
private theorem rec10032 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(3),[1,2,5,6,13,14],[170],712⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[514]? = some (⟨205,(3),[1,2,5,6,13,14],[170],712⟩) from rfl))
private theorem rec10038 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(4),[1,2,5,6,13,14],[170],711⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[520]? = some (⟨205,(4),[1,2,5,6,13,14],[170],711⟩) from rfl))
private theorem rec10045 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(5),[1,2,5,6,13,14],[170],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[527]? = some (⟨205,(5),[1,2,5,6,13,14],[170],713⟩) from rfl))
private theorem rec10052 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(6),[1,2,5,6,13,14],[170],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[534]? = some (⟨205,(6),[1,2,5,6,13,14],[170],713⟩) from rfl))
private theorem rec10059 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(7),[1,2,5,6,13,14],[170],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[541]? = some (⟨205,(7),[1,2,5,6,13,14],[170],713⟩) from rfl))
private theorem rec10066 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(8),[1,2,5,6,13,14],[170],714⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[548]? = some (⟨205,(8),[1,2,5,6,13,14],[170],714⟩) from rfl))
private theorem rec10072 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(9),[1,2,5,6,13,14],[170],713⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[554]? = some (⟨205,(9),[1,2,5,6,13,14],[170],713⟩) from rfl))
private theorem rec10079 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(10),[1,2,5,6,13,14],[170],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[561]? = some (⟨205,(10),[1,2,5,6,13,14],[170],715⟩) from rfl))
private theorem rec10086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(11),[1,2,5,6,13,14],[170],716⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[568]? = some (⟨205,(11),[1,2,5,6,13,14],[170],716⟩) from rfl))
private theorem rec10093 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(12),[1,2,5,6,13,14],[170],717⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[575]? = some (⟨205,(12),[1,2,5,6,13,14],[170],717⟩) from rfl))
private theorem rec10100 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(13),[1,2,5,6,13,14],[170],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[582]? = some (⟨205,(13),[1,2,5,6,13,14],[170],718⟩) from rfl))
private theorem rec10106 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(14),[1,2,5,6,13,14],[170],719⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[588]? = some (⟨205,(14),[1,2,5,6,13,14],[170],719⟩) from rfl))
private theorem rec10113 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(15),[1,2,5,6,13,14],[170],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[595]? = some (⟨205,(15),[1,2,5,6,13,14],[170],715⟩) from rfl))
private theorem rec10120 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(16),[1,2,5,6,13,14],[170],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[602]? = some (⟨205,(16),[1,2,5,6,13,14],[170],720⟩) from rfl))
private theorem rec10127 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(17),[1,2,5,6,13,14],[170],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[609]? = some (⟨205,(17),[1,2,5,6,13,14],[170],720⟩) from rfl))
private theorem rec10134 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(18),[1,2,5,6,13,14],[170],721⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[616]? = some (⟨205,(18),[1,2,5,6,13,14],[170],721⟩) from rfl))
private theorem rec10140 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(19),[1,2,5,6,13,14],[170],720⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[622]? = some (⟨205,(19),[1,2,5,6,13,14],[170],720⟩) from rfl))
private theorem rec10147 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(20),[1,2,5,6,13,14],[170],715⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[629]? = some (⟨205,(20),[1,2,5,6,13,14],[170],715⟩) from rfl))
private theorem rec10154 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(21),[1,2,5,6,13,14],[170],716⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[636]? = some (⟨205,(21),[1,2,5,6,13,14],[170],716⟩) from rfl))
private theorem rec10161 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(22),[1,2,5,6,13,14],[170],717⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[643]? = some (⟨205,(22),[1,2,5,6,13,14],[170],717⟩) from rfl))
private theorem rec10168 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(23),[1,2,5,6,13,14],[170],718⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[650]? = some (⟨205,(23),[1,2,5,6,13,14],[170],718⟩) from rfl))
private theorem rec10174 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 205 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨205,(24),[1,2,5,6,13,14],[170],719⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[656]? = some (⟨205,(24),[1,2,5,6,13,14],[170],719⟩) from rfl))
private theorem rec10181 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(0),[1,2,5,6,13,14],[170],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[663]? = some (⟨207,(0),[1,2,5,6,13,14],[170],481⟩) from rfl))
private theorem rec10189 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(1),[1,2,5,6,13,14],[170],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[671]? = some (⟨207,(1),[1,2,5,6,13,14],[170],482⟩) from rfl))
private theorem rec10197 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(2),[1,2,5,6,13,14],[170],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[679]? = some (⟨207,(2),[1,2,5,6,13,14],[170],481⟩) from rfl))
private theorem rec10205 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(3),[1,2,5,6,13,14],[170],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[687]? = some (⟨207,(3),[1,2,5,6,13,14],[170],483⟩) from rfl))
private theorem rec10213 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(4),[1,2,5,6,13,14],[170],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[695]? = some (⟨207,(4),[1,2,5,6,13,14],[170],484⟩) from rfl))
private theorem rec10221 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(5),[1,2,5,6,13,14],[170],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[703]? = some (⟨207,(5),[1,2,5,6,13,14],[170],481⟩) from rfl))
private theorem rec10229 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(6),[1,2,5,6,13,14],[170],482⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[711]? = some (⟨207,(6),[1,2,5,6,13,14],[170],482⟩) from rfl))
private theorem rec10237 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(7),[1,2,5,6,13,14],[170],481⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[719]? = some (⟨207,(7),[1,2,5,6,13,14],[170],481⟩) from rfl))
private theorem rec10245 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(8),[1,2,5,6,13,14],[170],483⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[727]? = some (⟨207,(8),[1,2,5,6,13,14],[170],483⟩) from rfl))
private theorem rec10253 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(9),[1,2,5,6,13,14],[170],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[735]? = some (⟨207,(9),[1,2,5,6,13,14],[170],484⟩) from rfl))
private theorem rec10261 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(10),[1,2,5,6,13,14],[170],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[743]? = some (⟨207,(10),[1,2,5,6,13,14],[170],485⟩) from rfl))
private theorem rec10269 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(11),[1,2,5,6,13,14],[170],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[751]? = some (⟨207,(11),[1,2,5,6,13,14],[170],485⟩) from rfl))
private theorem rec10277 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(12),[1,2,5,6,13,14],[170],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[759]? = some (⟨207,(12),[1,2,5,6,13,14],[170],485⟩) from rfl))
private theorem rec10285 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(13),[1,2,5,6,13,14],[170],485⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[767]? = some (⟨207,(13),[1,2,5,6,13,14],[170],485⟩) from rfl))
private theorem rec10293 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(14),[1,2,5,6,13,14],[170],484⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[775]? = some (⟨207,(14),[1,2,5,6,13,14],[170],484⟩) from rfl))
private theorem rec10301 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(15),[1,2,5,6,13,14],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[783]? = some (⟨207,(15),[1,2,5,6,13,14],[170],486⟩) from rfl))
private theorem rec10309 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(16),[1,2,5,6,13,14],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[791]? = some (⟨207,(16),[1,2,5,6,13,14],[170],486⟩) from rfl))
private theorem rec10317 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(17),[1,2,5,6,13,14],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[799]? = some (⟨207,(17),[1,2,5,6,13,14],[170],486⟩) from rfl))
private theorem rec10325 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(18),[1,2,5,6,13,14],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[807]? = some (⟨207,(18),[1,2,5,6,13,14],[170],486⟩) from rfl))
private theorem rec10333 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(19),[1,2,5,6,13,14],[170],486⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[815]? = some (⟨207,(19),[1,2,5,6,13,14],[170],486⟩) from rfl))
private theorem rec10341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(20),[1,2,5,6,13,14],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[823]? = some (⟨207,(20),[1,2,5,6,13,14],[170],487⟩) from rfl))
private theorem rec10349 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(21),[1,2,5,6,13,14],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[831]? = some (⟨207,(21),[1,2,5,6,13,14],[170],487⟩) from rfl))
private theorem rec10357 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(22),[1,2,5,6,13,14],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[839]? = some (⟨207,(22),[1,2,5,6,13,14],[170],487⟩) from rfl))
private theorem rec10365 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(23),[1,2,5,6,13,14],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[847]? = some (⟨207,(23),[1,2,5,6,13,14],[170],487⟩) from rfl))
private theorem rec10373 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 207 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨207,(24),[1,2,5,6,13,14],[170],487⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[855]? = some (⟨207,(24),[1,2,5,6,13,14],[170],487⟩) from rfl))
private theorem rec10381 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(0),[1,2,5,6,13,14],[170],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[863]? = some (⟨210,(0),[1,2,5,6,13,14],[170],722⟩) from rfl))
private theorem rec10385 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(1),[1,2,5,6,13,14],[170],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[867]? = some (⟨210,(1),[1,2,5,6,13,14],[170],723⟩) from rfl))
private theorem rec10389 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(2),[1,2,5,6,13,14],[170],724⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[871]? = some (⟨210,(2),[1,2,5,6,13,14],[170],724⟩) from rfl))
private theorem rec10393 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(3),[1,2,5,6,13,14],[170],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[875]? = some (⟨210,(3),[1,2,5,6,13,14],[170],725⟩) from rfl))
private theorem rec10397 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(4),[1,2,5,6,13,14],[170],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[879]? = some (⟨210,(4),[1,2,5,6,13,14],[170],722⟩) from rfl))
private theorem rec10401 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(5),[1,2,5,6,13,14],[170],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[883]? = some (⟨210,(5),[1,2,5,6,13,14],[170],723⟩) from rfl))
private theorem rec10405 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(6),[1,2,5,6,13,14],[170],726⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[887]? = some (⟨210,(6),[1,2,5,6,13,14],[170],726⟩) from rfl))
private theorem rec10409 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(7),[1,2,5,6,13,14],[170],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[891]? = some (⟨210,(7),[1,2,5,6,13,14],[170],725⟩) from rfl))
private theorem rec10413 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(8),[1,2,5,6,13,14],[170],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[895]? = some (⟨210,(8),[1,2,5,6,13,14],[170],722⟩) from rfl))
private theorem rec10417 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(9),[1,2,5,6,13,14],[170],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[899]? = some (⟨210,(9),[1,2,5,6,13,14],[170],723⟩) from rfl))
private theorem rec10421 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(10),[1,2,5,6,13,14],[170],724⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[903]? = some (⟨210,(10),[1,2,5,6,13,14],[170],724⟩) from rfl))
private theorem rec10425 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(11),[1,2,5,6,13,14],[170],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[907]? = some (⟨210,(11),[1,2,5,6,13,14],[170],725⟩) from rfl))
private theorem rec10429 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(12),[1,2,5,6,13,14],[170],722⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[911]? = some (⟨210,(12),[1,2,5,6,13,14],[170],722⟩) from rfl))
private theorem rec10433 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(13),[1,2,5,6,13,14],[170],723⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[915]? = some (⟨210,(13),[1,2,5,6,13,14],[170],723⟩) from rfl))
private theorem rec10437 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(14),[1,2,5,6,13,14],[170],727⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[919]? = some (⟨210,(14),[1,2,5,6,13,14],[170],727⟩) from rfl))
private theorem rec10441 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 210 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨210,(15),[1,2,5,6,13,14],[170],725⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[923]? = some (⟨210,(15),[1,2,5,6,13,14],[170],725⟩) from rfl))
private theorem rec10445 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(0),[1,2,5,6,13,14],[170],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[927]? = some (⟨213,(0),[1,2,5,6,13,14],[170],494⟩) from rfl))
private theorem rec10453 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(1),[1,2,5,6,13,14],[170],495⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[935]? = some (⟨213,(1),[1,2,5,6,13,14],[170],495⟩) from rfl))
private theorem rec10461 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(2),[1,2,5,6,13,14],[170],494⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[943]? = some (⟨213,(2),[1,2,5,6,13,14],[170],494⟩) from rfl))
private theorem rec10469 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(3),[1,2,5,6,13,14],[170],496⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[951]? = some (⟨213,(3),[1,2,5,6,13,14],[170],496⟩) from rfl))
private theorem rec10477 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(4),[1,2,5,6,13,14],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[959]? = some (⟨213,(4),[1,2,5,6,13,14],[170],497⟩) from rfl))
private theorem rec10485 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(5),[1,2,5,6,13,14],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[967]? = some (⟨213,(5),[1,2,5,6,13,14],[170],497⟩) from rfl))
private theorem rec10494 (si parent : ℕ) (hs : si ∈ ([2, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(6),[2,14],[170],920⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[976]? = some (⟨213,(6),[2,14],[170],920⟩) from rfl))
private theorem rec10504 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(7),[1,2,5,6,13,14],[170],497⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[986]? = some (⟨213,(7),[1,2,5,6,13,14],[170],497⟩) from rfl))
private theorem rec10512 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(8),[1,2,5,6,13,14],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[994]? = some (⟨213,(8),[1,2,5,6,13,14],[170],498⟩) from rfl))
private theorem rec10520 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(9),[1,2,5,6,13,14],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1002]? = some (⟨213,(9),[1,2,5,6,13,14],[170],498⟩) from rfl))
private theorem rec10528 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(10),[1,2,5,6,13,14],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1010]? = some (⟨213,(10),[1,2,5,6,13,14],[170],498⟩) from rfl))
private theorem rec10536 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(11),[1,2,5,6,13,14],[170],498⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1018]? = some (⟨213,(11),[1,2,5,6,13,14],[170],498⟩) from rfl))
private theorem rec10544 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(12),[1,2,5,6,13,14],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1026]? = some (⟨213,(12),[1,2,5,6,13,14],[170],499⟩) from rfl))
private theorem rec10552 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(13),[1,2,5,6,13,14],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1034]? = some (⟨213,(13),[1,2,5,6,13,14],[170],499⟩) from rfl))
private theorem rec10560 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(14),[1,2,5,6,13,14],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1042]? = some (⟨213,(14),[1,2,5,6,13,14],[170],499⟩) from rfl))
private theorem rec10568 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 213 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨213,(15),[1,2,5,6,13,14],[170],499⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1050]? = some (⟨213,(15),[1,2,5,6,13,14],[170],499⟩) from rfl))
private theorem rec10672 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(0),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1154]? = some (⟨220,(0),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10677 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(1),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1159]? = some (⟨220,(1),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10681 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(2),[1,2,5,6,13,14],[170],734⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1163]? = some (⟨220,(2),[1,2,5,6,13,14],[170],734⟩) from rfl))
private theorem rec10685 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(3),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1167]? = some (⟨220,(3),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec10689 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(4),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1171]? = some (⟨220,(4),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10693 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(5),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1175]? = some (⟨220,(5),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10697 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(6),[1,2,5,6,13,14],[170],511⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1179]? = some (⟨220,(6),[1,2,5,6,13,14],[170],511⟩) from rfl))
private theorem rec10701 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(7),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1183]? = some (⟨220,(7),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec10705 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(8),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1187]? = some (⟨220,(8),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10709 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(9),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1191]? = some (⟨220,(9),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10713 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(10),[1,2,5,6,13,14],[170],512⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1195]? = some (⟨220,(10),[1,2,5,6,13,14],[170],512⟩) from rfl))
private theorem rec10717 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(11),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1199]? = some (⟨220,(11),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec10721 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(12),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1203]? = some (⟨220,(12),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10725 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(13),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part9 (List.mem_of_getElem? (show section14DataRecords3Part2[1207]? = some (⟨220,(13),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10729 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(14),[1,2,5,6,13,14],[170],513⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[0]? = some (⟨220,(14),[1,2,5,6,13,14],[170],513⟩) from rfl))
private theorem rec10733 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(15),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[4]? = some (⟨220,(15),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec10737 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(16),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[8]? = some (⟨220,(16),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10741 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(17),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[12]? = some (⟨220,(17),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec10745 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(18),[1,2,5,6,13,14],[170],514⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[16]? = some (⟨220,(18),[1,2,5,6,13,14],[170],514⟩) from rfl))
private theorem rec10749 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 220 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨220,(19),[1,2,5,6,13,14],[170],29⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[20]? = some (⟨220,(19),[1,2,5,6,13,14],[170],29⟩) from rfl))
private theorem rec10753 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(0),[1,2,5,6,13,14],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[24]? = some (⟨221,(0),[1,2,5,6,13,14],[170],515⟩) from rfl))
private theorem rec10761 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(1),[1,2,5,6,13,14],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[32]? = some (⟨221,(1),[1,2,5,6,13,14],[170],515⟩) from rfl))
private theorem rec10769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(2),[1,2,5,6,13,14],[170],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[40]? = some (⟨221,(2),[1,2,5,6,13,14],[170],516⟩) from rfl))
private theorem rec10777 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(3),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[48]? = some (⟨221,(3),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec10785 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(4),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[56]? = some (⟨221,(4),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec10793 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(5),[1,2,5,6,13,14],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[64]? = some (⟨221,(5),[1,2,5,6,13,14],[170],515⟩) from rfl))
private theorem rec10801 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(6),[1,2,5,6,13,14],[170],515⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[72]? = some (⟨221,(6),[1,2,5,6,13,14],[170],515⟩) from rfl))
private theorem rec10809 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(7),[1,2,5,6,13,14],[170],516⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[80]? = some (⟨221,(7),[1,2,5,6,13,14],[170],516⟩) from rfl))
private theorem rec10817 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(8),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[88]? = some (⟨221,(8),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec10825 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(9),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[96]? = some (⟨221,(9),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec10833 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(10),[1,2,5,6,13,14],[170],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[104]? = some (⟨221,(10),[1,2,5,6,13,14],[170],519⟩) from rfl))
private theorem rec10841 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(11),[1,2,5,6,13,14],[170],519⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[112]? = some (⟨221,(11),[1,2,5,6,13,14],[170],519⟩) from rfl))
private theorem rec10849 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(12),[1,2,5,6,13,14],[170],520⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[120]? = some (⟨221,(12),[1,2,5,6,13,14],[170],520⟩) from rfl))
private theorem rec10857 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(13),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[128]? = some (⟨221,(13),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec10865 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(14),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[136]? = some (⟨221,(14),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec10873 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(15),[1,2,5,6,13,14],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[144]? = some (⟨221,(15),[1,2,5,6,13,14],[170],521⟩) from rfl))
private theorem rec10881 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(16),[1,2,5,6,13,14],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[152]? = some (⟨221,(16),[1,2,5,6,13,14],[170],521⟩) from rfl))
private theorem rec10889 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(17),[1,2,5,6,13,14],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[160]? = some (⟨221,(17),[1,2,5,6,13,14],[170],521⟩) from rfl))
private theorem rec10897 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(18),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[168]? = some (⟨221,(18),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec10906 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(19),[1,2,5,6,13,14],[170],521⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[177]? = some (⟨221,(19),[1,2,5,6,13,14],[170],521⟩) from rfl))
private theorem rec10914 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(20),[1,2,5,6,13,14],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[185]? = some (⟨221,(20),[1,2,5,6,13,14],[170],522⟩) from rfl))
private theorem rec10922 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(21),[1,2,5,6,13,14],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[193]? = some (⟨221,(21),[1,2,5,6,13,14],[170],522⟩) from rfl))
private theorem rec10930 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(22),[1,2,5,6,13,14],[170],522⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[201]? = some (⟨221,(22),[1,2,5,6,13,14],[170],522⟩) from rfl))
private theorem rec10938 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(23),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[209]? = some (⟨221,(23),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec10946 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 221 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨221,(24),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[217]? = some (⟨221,(24),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec10955 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(0),[1,2,6,13,14],[170],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[226]? = some (⟨222,(0),[1,2,6,13,14],[170],735⟩) from rfl))
private theorem rec10964 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(1),[1,2,5,6,13,14],[170],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[235]? = some (⟨222,(1),[1,2,5,6,13,14],[170],736⟩) from rfl))
private theorem rec10971 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(2),[1,2,5,6,13,14],[170],737⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[242]? = some (⟨222,(2),[1,2,5,6,13,14],[170],737⟩) from rfl))
private theorem rec10979 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(3),[1,2,5,6,13,14],[170],736⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[250]? = some (⟨222,(3),[1,2,5,6,13,14],[170],736⟩) from rfl))
private theorem rec10986 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(4),[1,2,5,6,13,14],[170],525⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[257]? = some (⟨222,(4),[1,2,5,6,13,14],[170],525⟩) from rfl))
private theorem rec10992 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(5),[1,2,5,6,13,14],[170],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[263]? = some (⟨222,(5),[1,2,5,6,13,14],[170],735⟩) from rfl))
private theorem rec10999 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(6),[1,2,6,13,14],[170],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[270]? = some (⟨222,(6),[1,2,6,13,14],[170],738⟩) from rfl))
private theorem rec11008 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(7),[1,2,5,6,13,14],[170],739⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[279]? = some (⟨222,(7),[1,2,5,6,13,14],[170],739⟩) from rfl))
private theorem rec11016 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(8),[1,2,5,6,13,14],[170],740⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[287]? = some (⟨222,(8),[1,2,5,6,13,14],[170],740⟩) from rfl))
private theorem rec11023 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(9),[1,2,5,6,13,14],[170],528⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[294]? = some (⟨222,(9),[1,2,5,6,13,14],[170],528⟩) from rfl))
private theorem rec11029 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(10),[1,2,6,13,14],[170],741⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[300]? = some (⟨222,(10),[1,2,6,13,14],[170],741⟩) from rfl))
private theorem rec11038 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(11),[1,2,6,13,14],[170],742⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[309]? = some (⟨222,(11),[1,2,6,13,14],[170],742⟩) from rfl))
private theorem rec11047 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(12),[1,2,6,13,14],[170],743⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[318]? = some (⟨222,(12),[1,2,6,13,14],[170],743⟩) from rfl))
private theorem rec11057 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(13),[1,2,6,13,14],[170],744⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[328]? = some (⟨222,(13),[1,2,6,13,14],[170],744⟩) from rfl))
private theorem rec11066 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(14),[1,2,5,6,13,14],[170],531⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[337]? = some (⟨222,(14),[1,2,5,6,13,14],[170],531⟩) from rfl))
private theorem rec11072 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(15),[1,2,5,6,13,14],[170],735⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[343]? = some (⟨222,(15),[1,2,5,6,13,14],[170],735⟩) from rfl))
private theorem rec11079 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(16),[1,2,5,6,13,14],[170],738⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[350]? = some (⟨222,(16),[1,2,5,6,13,14],[170],738⟩) from rfl))
private theorem rec11086 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(17),[1,2,5,6,13,14],[170],745⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[357]? = some (⟨222,(17),[1,2,5,6,13,14],[170],745⟩) from rfl))
private theorem rec11094 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(18),[1,2,5,6,13,14],[170],746⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[365]? = some (⟨222,(18),[1,2,5,6,13,14],[170],746⟩) from rfl))
private theorem rec11101 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(19),[1,2,5,6,13,14],[170],534⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[372]? = some (⟨222,(19),[1,2,5,6,13,14],[170],534⟩) from rfl))
private theorem rec11107 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(20),[1,2,5,6,13,14],[170],535⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[378]? = some (⟨222,(20),[1,2,5,6,13,14],[170],535⟩) from rfl))
private theorem rec11113 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(21),[1,2,5,6,13,14],[170],536⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[384]? = some (⟨222,(21),[1,2,5,6,13,14],[170],536⟩) from rfl))
private theorem rec11119 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(22),[1,2,5,6,13,14],[170],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[390]? = some (⟨222,(22),[1,2,5,6,13,14],[170],537⟩) from rfl))
private theorem rec11125 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(23),[1,2,5,6,13,14],[170],538⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[396]? = some (⟨222,(23),[1,2,5,6,13,14],[170],538⟩) from rfl))
private theorem rec11131 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 222 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨222,(24),[1,2,5,6,13,14],[170],537⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[402]? = some (⟨222,(24),[1,2,5,6,13,14],[170],537⟩) from rfl))
private theorem rec11138 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(0),[1,2,5,6,13,14],[170],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[409]? = some (⟨224,(0),[1,2,5,6,13,14],[170],539⟩) from rfl))
private theorem rec11144 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(1),[1,2,5,6,13,14],[170],539⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[415]? = some (⟨224,(1),[1,2,5,6,13,14],[170],539⟩) from rfl))
private theorem rec11150 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(2),[1,2,5,6,13,14],[170],540⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[421]? = some (⟨224,(2),[1,2,5,6,13,14],[170],540⟩) from rfl))
private theorem rec11156 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(3),[1,2,5,6,13,14],[170],541⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[427]? = some (⟨224,(3),[1,2,5,6,13,14],[170],541⟩) from rfl))
private theorem rec11162 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(4),[1,2,5,6,13,14],[170],542⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[433]? = some (⟨224,(4),[1,2,5,6,13,14],[170],542⟩) from rfl))
private theorem rec11168 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(5),[1,2,5,6,13,14],[170],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[439]? = some (⟨224,(5),[1,2,5,6,13,14],[170],543⟩) from rfl))
private theorem rec11176 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(6),[1,2,5,6,13,14],[170],543⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[447]? = some (⟨224,(6),[1,2,5,6,13,14],[170],543⟩) from rfl))
private theorem rec11184 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(7),[1,2,5,6,13,14],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[455]? = some (⟨224,(7),[1,2,5,6,13,14],[170],544⟩) from rfl))
private theorem rec11192 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(8),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[463]? = some (⟨224,(8),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec11200 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(9),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[471]? = some (⟨224,(9),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec11208 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(10),[1,2,5,6,13,14],[170],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[479]? = some (⟨224,(10),[1,2,5,6,13,14],[170],545⟩) from rfl))
private theorem rec11216 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(11),[1,2,5,6,13,14],[170],545⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[487]? = some (⟨224,(11),[1,2,5,6,13,14],[170],545⟩) from rfl))
private theorem rec11224 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(12),[1,2,5,6,13,14],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[495]? = some (⟨224,(12),[1,2,5,6,13,14],[170],544⟩) from rfl))
private theorem rec11232 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(13),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[503]? = some (⟨224,(13),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec11240 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(14),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[511]? = some (⟨224,(14),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec11248 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(15),[1,2,5,6,13,14],[170],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[519]? = some (⟨224,(15),[1,2,5,6,13,14],[170],546⟩) from rfl))
private theorem rec11256 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(16),[1,2,5,6,13,14],[170],546⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[527]? = some (⟨224,(16),[1,2,5,6,13,14],[170],546⟩) from rfl))
private theorem rec11264 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(17),[1,2,5,6,13,14],[170],544⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[535]? = some (⟨224,(17),[1,2,5,6,13,14],[170],544⟩) from rfl))
private theorem rec11272 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(18),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[543]? = some (⟨224,(18),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec11280 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(19),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[551]? = some (⟨224,(19),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec11288 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(20),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[559]? = some (⟨224,(20),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11296 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(21),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[567]? = some (⟨224,(21),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11304 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(22),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[575]? = some (⟨224,(22),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11312 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(23),[1,2,5,6,13,14],[170],517⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[583]? = some (⟨224,(23),[1,2,5,6,13,14],[170],517⟩) from rfl))
private theorem rec11320 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 224 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨224,(24),[1,2,5,6,13,14],[170],518⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[591]? = some (⟨224,(24),[1,2,5,6,13,14],[170],518⟩) from rfl))
private theorem rec11328 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(0),[1,2,5,6,13,14],[170],747⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[599]? = some (⟨225,(0),[1,2,5,6,13,14],[170],747⟩) from rfl))
private theorem rec11334 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(1),[1,2,5,6,13,14],[170],748⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[605]? = some (⟨225,(1),[1,2,5,6,13,14],[170],748⟩) from rfl))
private theorem rec11340 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(2),[1,2,5,6,13,14],[170],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[611]? = some (⟨225,(2),[1,2,5,6,13,14],[170],749⟩) from rfl))
private theorem rec11347 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(3),[1,2,5,6,13,14],[170],750⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[618]? = some (⟨225,(3),[1,2,5,6,13,14],[170],750⟩) from rfl))
private theorem rec11354 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(4),[1,2,5,6,13,14],[170],749⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[625]? = some (⟨225,(4),[1,2,5,6,13,14],[170],749⟩) from rfl))
private theorem rec11361 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(5),[1,2,5,6,13,14],[170],751⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[632]? = some (⟨225,(5),[1,2,5,6,13,14],[170],751⟩) from rfl))
private theorem rec11367 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(6),[1,2,5,6,13,14],[170],752⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[638]? = some (⟨225,(6),[1,2,5,6,13,14],[170],752⟩) from rfl))
private theorem rec11373 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(7),[1,2,5,6,13,14],[170],753⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[644]? = some (⟨225,(7),[1,2,5,6,13,14],[170],753⟩) from rfl))
private theorem rec11381 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(8),[1,2,5,6,13,14],[170],754⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[652]? = some (⟨225,(8),[1,2,5,6,13,14],[170],754⟩) from rfl))
private theorem rec11388 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(9),[1,2,5,6,13,14],[170],753⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[659]? = some (⟨225,(9),[1,2,5,6,13,14],[170],753⟩) from rfl))
private theorem rec11396 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(10),[1,2,5,6,13,14],[170],755⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[667]? = some (⟨225,(10),[1,2,5,6,13,14],[170],755⟩) from rfl))
private theorem rec11402 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(11),[1,2,5,6,13,14],[170],756⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[673]? = some (⟨225,(11),[1,2,5,6,13,14],[170],756⟩) from rfl))
private theorem rec11408 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(12),[1,2,5,6,13,14],[170],757⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[679]? = some (⟨225,(12),[1,2,5,6,13,14],[170],757⟩) from rfl))
private theorem rec11416 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(13),[1,2,5,6,13,14],[170],758⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[687]? = some (⟨225,(13),[1,2,5,6,13,14],[170],758⟩) from rfl))
private theorem rec11423 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(14),[1,2,5,6,13,14],[170],757⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[694]? = some (⟨225,(14),[1,2,5,6,13,14],[170],757⟩) from rfl))
private theorem rec11431 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(15),[1,2,5,6,13,14],[170],759⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[702]? = some (⟨225,(15),[1,2,5,6,13,14],[170],759⟩) from rfl))
private theorem rec11437 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(16),[1,2,5,6,13,14],[170],760⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[708]? = some (⟨225,(16),[1,2,5,6,13,14],[170],760⟩) from rfl))
private theorem rec11443 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(17),[1,2,5,6,13,14],[170],761⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[714]? = some (⟨225,(17),[1,2,5,6,13,14],[170],761⟩) from rfl))
private theorem rec11451 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(18),[1,2,5,6,13,14],[170],762⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[722]? = some (⟨225,(18),[1,2,5,6,13,14],[170],762⟩) from rfl))
private theorem rec11458 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(19),[1,2,5,6,13,14],[170],761⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[729]? = some (⟨225,(19),[1,2,5,6,13,14],[170],761⟩) from rfl))
private theorem rec11466 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(20),[1,2,5,6,13,14],[170],763⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[737]? = some (⟨225,(20),[1,2,5,6,13,14],[170],763⟩) from rfl))
private theorem rec11472 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(21),[1,2,5,6,13,14],[170],764⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[743]? = some (⟨225,(21),[1,2,5,6,13,14],[170],764⟩) from rfl))
private theorem rec11478 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(22),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[749]? = some (⟨225,(22),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11486 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(23),[1,2,5,6,13,14],[170],765⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[757]? = some (⟨225,(23),[1,2,5,6,13,14],[170],765⟩) from rfl))
private theorem rec11493 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 225 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨225,(24),[1,2,5,6,13,14],[170],547⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[764]? = some (⟨225,(24),[1,2,5,6,13,14],[170],547⟩) from rfl))
private theorem rec11501 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(0),[1,2,5,6,13,14],[170],766⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[772]? = some (⟨226,(0),[1,2,5,6,13,14],[170],766⟩) from rfl))
private theorem rec11508 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(1),[1,2,5,6,13,14],[170],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[779]? = some (⟨226,(1),[1,2,5,6,13,14],[170],767⟩) from rfl))
private theorem rec11514 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(2),[1,2,5,6,13,14],[170],768⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[785]? = some (⟨226,(2),[1,2,5,6,13,14],[170],768⟩) from rfl))
private theorem rec11520 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(3),[1,2,5,6,13,14],[170],767⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[791]? = some (⟨226,(3),[1,2,5,6,13,14],[170],767⟩) from rfl))
private theorem rec11526 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(4),[1,2,5,6,13,14],[170],769⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[797]? = some (⟨226,(4),[1,2,5,6,13,14],[170],769⟩) from rfl))
private theorem rec11532 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(5),[1,2,5,6,13,14],[170],770⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[803]? = some (⟨226,(5),[1,2,5,6,13,14],[170],770⟩) from rfl))
private theorem rec11538 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(6),[1,2,5,6,13,14],[170],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[809]? = some (⟨226,(6),[1,2,5,6,13,14],[170],771⟩) from rfl))
private theorem rec11544 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(7),[1,2,5,6,13,14],[170],771⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[815]? = some (⟨226,(7),[1,2,5,6,13,14],[170],771⟩) from rfl))
private theorem rec11550 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(8),[1,2,5,6,13,14],[170],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[821]? = some (⟨226,(8),[1,2,5,6,13,14],[170],772⟩) from rfl))
private theorem rec11556 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 226 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨226,(9),[1,2,5,6,13,14],[170],772⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[827]? = some (⟨226,(9),[1,2,5,6,13,14],[170],772⟩) from rfl))
private theorem rec11562 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(0),[1,2,5,6,13,14],[170],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[833]? = some (⟨227,(0),[1,2,5,6,13,14],[170],773⟩) from rfl))
private theorem rec11568 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(1),[1,2,5,6,13,14],[170],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[839]? = some (⟨227,(1),[1,2,5,6,13,14],[170],774⟩) from rfl))
private theorem rec11574 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(2),[1,2,5,6,13,14],[170],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[845]? = some (⟨227,(2),[1,2,5,6,13,14],[170],775⟩) from rfl))
private theorem rec11582 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(3),[1,2,5,6,13,14],[170],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[853]? = some (⟨227,(3),[1,2,5,6,13,14],[170],776⟩) from rfl))
private theorem rec11588 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(4),[1,2,5,6,13,14],[170],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[859]? = some (⟨227,(4),[1,2,5,6,13,14],[170],775⟩) from rfl))
private theorem rec11596 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(5),[1,2,5,6,13,14],[170],773⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[867]? = some (⟨227,(5),[1,2,5,6,13,14],[170],773⟩) from rfl))
private theorem rec11602 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(6),[1,2,5,6,13,14],[170],774⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[873]? = some (⟨227,(6),[1,2,5,6,13,14],[170],774⟩) from rfl))
private theorem rec11608 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(7),[1,2,5,6,13,14],[170],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[879]? = some (⟨227,(7),[1,2,5,6,13,14],[170],775⟩) from rfl))
private theorem rec11616 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(8),[1,2,5,6,13,14],[170],776⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[887]? = some (⟨227,(8),[1,2,5,6,13,14],[170],776⟩) from rfl))
private theorem rec11622 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(9),[1,2,5,6,13,14],[170],775⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[893]? = some (⟨227,(9),[1,2,5,6,13,14],[170],775⟩) from rfl))
private theorem rec11630 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(10),[1,2,5,6,13,14],[170],777⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[901]? = some (⟨227,(10),[1,2,5,6,13,14],[170],777⟩) from rfl))
private theorem rec11636 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(11),[1,2,5,6,13,14],[170],778⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[907]? = some (⟨227,(11),[1,2,5,6,13,14],[170],778⟩) from rfl))
private theorem rec11642 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(12),[1,2,5,6,13,14],[170],779⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[913]? = some (⟨227,(12),[1,2,5,6,13,14],[170],779⟩) from rfl))
private theorem rec11650 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(13),[1,2,5,6,13,14],[170],780⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[921]? = some (⟨227,(13),[1,2,5,6,13,14],[170],780⟩) from rfl))
private theorem rec11656 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(14),[1,2,5,6,13,14],[170],779⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[927]? = some (⟨227,(14),[1,2,5,6,13,14],[170],779⟩) from rfl))
private theorem rec11664 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(15),[1,2,5,6,13,14],[170],781⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[935]? = some (⟨227,(15),[1,2,5,6,13,14],[170],781⟩) from rfl))
private theorem rec11670 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(16),[1,2,5,6,13,14],[170],782⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[941]? = some (⟨227,(16),[1,2,5,6,13,14],[170],782⟩) from rfl))
private theorem rec11676 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(17),[1,2,5,6,13,14],[170],783⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[947]? = some (⟨227,(17),[1,2,5,6,13,14],[170],783⟩) from rfl))
private theorem rec11684 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(18),[1,2,5,6,13,14],[170],784⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[955]? = some (⟨227,(18),[1,2,5,6,13,14],[170],784⟩) from rfl))
private theorem rec11690 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(19),[1,2,5,6,13,14],[170],783⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[961]? = some (⟨227,(19),[1,2,5,6,13,14],[170],783⟩) from rfl))
private theorem rec11698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(20),[1,2,5,6,13,14],[170],785⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[969]? = some (⟨227,(20),[1,2,5,6,13,14],[170],785⟩) from rfl))
private theorem rec11704 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(21),[1,2,5,6,13,14],[170],786⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[975]? = some (⟨227,(21),[1,2,5,6,13,14],[170],786⟩) from rfl))
private theorem rec11710 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(22),[1,2,5,6,13,14],[170],787⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[981]? = some (⟨227,(22),[1,2,5,6,13,14],[170],787⟩) from rfl))
private theorem rec11718 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(23),[1,2,5,6,13,14],[170],788⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[989]? = some (⟨227,(23),[1,2,5,6,13,14],[170],788⟩) from rfl))
private theorem rec11724 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 227 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨227,(24),[1,2,5,6,13,14],[170],787⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[995]? = some (⟨227,(24),[1,2,5,6,13,14],[170],787⟩) from rfl))
private theorem rec11732 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(0),[1,2,5,6,13,14],[170],789⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1003]? = some (⟨228,(0),[1,2,5,6,13,14],[170],789⟩) from rfl))
private theorem rec11739 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(1),[1,2,5,6,13,14],[170],790⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1010]? = some (⟨228,(1),[1,2,5,6,13,14],[170],790⟩) from rfl))
private theorem rec11747 (si parent : ℕ) (hs : si ∈ ([2, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(2),[2,14],[170],921⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1018]? = some (⟨228,(2),[2,14],[170],921⟩) from rfl))
private theorem rec11756 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(3),[1,2,5,6,13,14],[170],792⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1027]? = some (⟨228,(3),[1,2,5,6,13,14],[170],792⟩) from rfl))
private theorem rec11763 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(4),[1,2,5,6,13,14],[170],793⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1034]? = some (⟨228,(4),[1,2,5,6,13,14],[170],793⟩) from rfl))
private theorem rec11769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(5),[1,2,5,6,13,14],[170],794⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1040]? = some (⟨228,(5),[1,2,5,6,13,14],[170],794⟩) from rfl))
private theorem rec11775 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(6),[1,2,5,6,13,14],[170],795⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1046]? = some (⟨228,(6),[1,2,5,6,13,14],[170],795⟩) from rfl))
private theorem rec11781 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(7),[1,2,5,6,13,14],[170],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1052]? = some (⟨228,(7),[1,2,5,6,13,14],[170],796⟩) from rfl))
private theorem rec11787 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(8),[1,2,5,6,13,14],[170],797⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1058]? = some (⟨228,(8),[1,2,5,6,13,14],[170],797⟩) from rfl))
private theorem rec11793 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(9),[1,2,5,6,13,14],[170],796⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1064]? = some (⟨228,(9),[1,2,5,6,13,14],[170],796⟩) from rfl))
private theorem rec11800 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(10),[1,2,5,6,13,14],[170],798⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1071]? = some (⟨228,(10),[1,2,5,6,13,14],[170],798⟩) from rfl))
private theorem rec11806 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(11),[1,2,5,6,13,14],[170],799⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1077]? = some (⟨228,(11),[1,2,5,6,13,14],[170],799⟩) from rfl))
private theorem rec11812 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(12),[1,2,5,6,13,14],[170],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1083]? = some (⟨228,(12),[1,2,5,6,13,14],[170],800⟩) from rfl))
private theorem rec11818 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(13),[1,2,5,6,13,14],[170],801⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1089]? = some (⟨228,(13),[1,2,5,6,13,14],[170],801⟩) from rfl))
private theorem rec11824 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(14),[1,2,5,6,13,14],[170],800⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1095]? = some (⟨228,(14),[1,2,5,6,13,14],[170],800⟩) from rfl))
private theorem rec11830 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(15),[1,2,5,6,13,14],[170],802⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1101]? = some (⟨228,(15),[1,2,5,6,13,14],[170],802⟩) from rfl))
private theorem rec11836 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(16),[1,2,5,6,13,14],[170],803⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1107]? = some (⟨228,(16),[1,2,5,6,13,14],[170],803⟩) from rfl))
private theorem rec11842 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(17),[1,2,5,6,13,14],[170],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1113]? = some (⟨228,(17),[1,2,5,6,13,14],[170],804⟩) from rfl))
private theorem rec11848 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(18),[1,2,5,6,13,14],[170],805⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1119]? = some (⟨228,(18),[1,2,5,6,13,14],[170],805⟩) from rfl))
private theorem rec11854 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(19),[1,2,5,6,13,14],[170],804⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1125]? = some (⟨228,(19),[1,2,5,6,13,14],[170],804⟩) from rfl))
private theorem rec11860 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(20),[1,2,5,6,13,14],[170],806⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1131]? = some (⟨228,(20),[1,2,5,6,13,14],[170],806⟩) from rfl))
private theorem rec11866 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(21),[1,2,5,6,13,14],[170],807⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1137]? = some (⟨228,(21),[1,2,5,6,13,14],[170],807⟩) from rfl))
private theorem rec11872 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(22),[1,2,5,6,13,14],[170],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1143]? = some (⟨228,(22),[1,2,5,6,13,14],[170],808⟩) from rfl))
private theorem rec11878 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(23),[1,2,5,6,13,14],[170],809⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1149]? = some (⟨228,(23),[1,2,5,6,13,14],[170],809⟩) from rfl))
private theorem rec11884 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 228 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨228,(24),[1,2,5,6,13,14],[170],808⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1155]? = some (⟨228,(24),[1,2,5,6,13,14],[170],808⟩) from rfl))
private theorem rec11890 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(0),[1,2,5,6,13,14],[170],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1161]? = some (⟨230,(0),[1,2,5,6,13,14],[170],810⟩) from rfl))
private theorem rec11896 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(1),[1,2,5,6,13,14],[170],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1167]? = some (⟨230,(1),[1,2,5,6,13,14],[170],811⟩) from rfl))
private theorem rec11903 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(2),[1,2,5,6,13,14],[170],812⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1174]? = some (⟨230,(2),[1,2,5,6,13,14],[170],812⟩) from rfl))
private theorem rec11909 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(3),[1,2,5,6,13,14],[170],813⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1180]? = some (⟨230,(3),[1,2,5,6,13,14],[170],813⟩) from rfl))
private theorem rec11915 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(4),[1,2,5,6,13,14],[170],814⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1186]? = some (⟨230,(4),[1,2,5,6,13,14],[170],814⟩) from rfl))
private theorem rec11921 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(5),[1,2,5,6,13,14],[170],810⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1192]? = some (⟨230,(5),[1,2,5,6,13,14],[170],810⟩) from rfl))
private theorem rec11927 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(6),[1,2,5,6,13,14],[170],811⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part10 (List.mem_of_getElem? (show section14DataRecords3Part3[1198]? = some (⟨230,(6),[1,2,5,6,13,14],[170],811⟩) from rfl))
private theorem rec11935 (si parent : ℕ) (hs : si ∈ ([2, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(7),[2,14],[170],922⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[6]? = some (⟨230,(7),[2,14],[170],922⟩) from rfl))
private theorem rec11942 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(8),[1,2,5,6,13,14],[170],816⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[13]? = some (⟨230,(8),[1,2,5,6,13,14],[170],816⟩) from rfl))
private theorem rec11949 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(9),[1,2,6,13,14],[170],817⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[20]? = some (⟨230,(9),[1,2,6,13,14],[170],817⟩) from rfl))
private theorem rec11958 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(10),[1,2,5,6,13,14],[170],818⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[29]? = some (⟨230,(10),[1,2,5,6,13,14],[170],818⟩) from rfl))
private theorem rec11964 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(11),[1,2,5,6,13,14],[170],819⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[35]? = some (⟨230,(11),[1,2,5,6,13,14],[170],819⟩) from rfl))
private theorem rec11971 (si parent : ℕ) (hs : si ∈ ([2, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(12),[2,6,14],[170],923⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[42]? = some (⟨230,(12),[2,6,14],[170],923⟩) from rfl))
private theorem rec11978 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(13),[1,2,5,6,13,14],[170],821⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[49]? = some (⟨230,(13),[1,2,5,6,13,14],[170],821⟩) from rfl))
private theorem rec11984 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(14),[1,2,6,13,14],[170],817⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[55]? = some (⟨230,(14),[1,2,6,13,14],[170],817⟩) from rfl))
private theorem rec11993 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(15),[1,2,5,6,13,14],[170],822⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[64]? = some (⟨230,(15),[1,2,5,6,13,14],[170],822⟩) from rfl))
private theorem rec11999 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(16),[1,2,5,6,13,14],[170],823⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[70]? = some (⟨230,(16),[1,2,5,6,13,14],[170],823⟩) from rfl))
private theorem rec12005 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(17),[1,2,5,6,13,14],[170],824⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[76]? = some (⟨230,(17),[1,2,5,6,13,14],[170],824⟩) from rfl))
private theorem rec12013 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(18),[1,2,5,6,13,14],[170],825⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[84]? = some (⟨230,(18),[1,2,5,6,13,14],[170],825⟩) from rfl))
private theorem rec12019 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(19),[1,2,5,6,13,14],[170],824⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[90]? = some (⟨230,(19),[1,2,5,6,13,14],[170],824⟩) from rfl))
private theorem rec12027 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (20) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(20),[1,2,5,6,13,14],[170],826⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[98]? = some (⟨230,(20),[1,2,5,6,13,14],[170],826⟩) from rfl))
private theorem rec12033 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (21) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(21),[1,2,5,6,13,14],[170],827⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[104]? = some (⟨230,(21),[1,2,5,6,13,14],[170],827⟩) from rfl))
private theorem rec12039 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (22) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(22),[1,2,5,6,13,14],[170],828⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[110]? = some (⟨230,(22),[1,2,5,6,13,14],[170],828⟩) from rfl))
private theorem rec12047 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (23) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(23),[1,2,5,6,13,14],[170],829⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[118]? = some (⟨230,(23),[1,2,5,6,13,14],[170],829⟩) from rfl))
private theorem rec12053 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 230 (24) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨230,(24),[1,2,5,6,13,14],[170],828⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[124]? = some (⟨230,(24),[1,2,5,6,13,14],[170],828⟩) from rfl))
private theorem rec12061 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(0),[1,2,5,6,13,14],[170],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[132]? = some (⟨231,(0),[1,2,5,6,13,14],[170],830⟩) from rfl))
private theorem rec12068 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(1),[1,2,5,6,13,14],[170],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[139]? = some (⟨231,(1),[1,2,5,6,13,14],[170],831⟩) from rfl))
private theorem rec12076 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(2),[1,2,5,6,13,14],[170],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[147]? = some (⟨231,(2),[1,2,5,6,13,14],[170],832⟩) from rfl))
private theorem rec12082 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(3),[1,2,5,6,13,14],[170],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[153]? = some (⟨231,(3),[1,2,5,6,13,14],[170],833⟩) from rfl))
private theorem rec12088 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(4),[1,2,5,6,13,14],[170],830⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[159]? = some (⟨231,(4),[1,2,5,6,13,14],[170],830⟩) from rfl))
private theorem rec12095 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(5),[1,2,5,6,13,14],[170],831⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[166]? = some (⟨231,(5),[1,2,5,6,13,14],[170],831⟩) from rfl))
private theorem rec12103 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(6),[1,2,5,6,13,14],[170],832⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[174]? = some (⟨231,(6),[1,2,5,6,13,14],[170],832⟩) from rfl))
private theorem rec12109 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(7),[1,2,5,6,13,14],[170],833⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[180]? = some (⟨231,(7),[1,2,5,6,13,14],[170],833⟩) from rfl))
private theorem rec12115 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(8),[1,2,5,6,13,14],[170],834⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[186]? = some (⟨231,(8),[1,2,5,6,13,14],[170],834⟩) from rfl))
private theorem rec12121 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(9),[1,2,5,6,13,14],[170],835⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[192]? = some (⟨231,(9),[1,2,5,6,13,14],[170],835⟩) from rfl))
private theorem rec12127 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(10),[1,2,5,6,13,14],[170],836⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[198]? = some (⟨231,(10),[1,2,5,6,13,14],[170],836⟩) from rfl))
private theorem rec12133 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(11),[1,2,5,6,13,14],[170],837⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[204]? = some (⟨231,(11),[1,2,5,6,13,14],[170],837⟩) from rfl))
private theorem rec12139 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(12),[1,2,5,6,13,14],[170],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[210]? = some (⟨231,(12),[1,2,5,6,13,14],[170],838⟩) from rfl))
private theorem rec12145 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(13),[1,2,5,6,13,14],[170],839⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[216]? = some (⟨231,(13),[1,2,5,6,13,14],[170],839⟩) from rfl))
private theorem rec12151 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(14),[1,2,5,6,13,14],[170],838⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[222]? = some (⟨231,(14),[1,2,5,6,13,14],[170],838⟩) from rfl))
private theorem rec12157 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(15),[1,2,5,6,13,14],[170],840⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[228]? = some (⟨231,(15),[1,2,5,6,13,14],[170],840⟩) from rfl))
private theorem rec12163 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(16),[1,2,5,6,13,14],[170],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[234]? = some (⟨231,(16),[1,2,5,6,13,14],[170],841⟩) from rfl))
private theorem rec12169 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(17),[1,2,5,6,13,14],[170],842⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[240]? = some (⟨231,(17),[1,2,5,6,13,14],[170],842⟩) from rfl))
private theorem rec12175 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(18),[1,2,5,6,13,14],[170],841⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[246]? = some (⟨231,(18),[1,2,5,6,13,14],[170],841⟩) from rfl))
private theorem rec12181 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 231 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨231,(19),[1,2,5,6,13,14],[170],843⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[252]? = some (⟨231,(19),[1,2,5,6,13,14],[170],843⟩) from rfl))
private theorem rec12187 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(0),[1,2,5,6,13,14],[170],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[258]? = some (⟨232,(0),[1,2,5,6,13,14],[170],844⟩) from rfl))
private theorem rec12193 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(1),[1,2,5,6,13,14],[170],845⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[264]? = some (⟨232,(1),[1,2,5,6,13,14],[170],845⟩) from rfl))
private theorem rec12199 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(2),[1,2,5,6,13,14],[170],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[270]? = some (⟨232,(2),[1,2,5,6,13,14],[170],846⟩) from rfl))
private theorem rec12206 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(3),[1,2,5,6,13,14],[170],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[277]? = some (⟨232,(3),[1,2,5,6,13,14],[170],847⟩) from rfl))
private theorem rec12213 (si parent : ℕ) (hs : si ∈ ([2, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(4),[2,14],[170],855⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[284]? = some (⟨232,(4),[2,14],[170],855⟩) from rfl))
private theorem rec12220 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(5),[1,2,5,6,13,14],[170],849⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[291]? = some (⟨232,(5),[1,2,5,6,13,14],[170],849⟩) from rfl))
private theorem rec12226 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(6),[1,2,5,6,13,14],[170],850⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[297]? = some (⟨232,(6),[1,2,5,6,13,14],[170],850⟩) from rfl))
private theorem rec12232 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(7),[1,2,5,6,13,14],[170],851⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[303]? = some (⟨232,(7),[1,2,5,6,13,14],[170],851⟩) from rfl))
private theorem rec12239 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(8),[1,2,5,6,13,14],[170],852⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[310]? = some (⟨232,(8),[1,2,5,6,13,14],[170],852⟩) from rfl))
private theorem rec12245 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(9),[1,2,5,6,13,14],[170],853⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[316]? = some (⟨232,(9),[1,2,5,6,13,14],[170],853⟩) from rfl))
private theorem rec12253 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(10),[1,2,5,6,13,14],[170],844⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[324]? = some (⟨232,(10),[1,2,5,6,13,14],[170],844⟩) from rfl))
private theorem rec12259 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(11),[1,2,5,6,13,14],[170],854⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[330]? = some (⟨232,(11),[1,2,5,6,13,14],[170],854⟩) from rfl))
private theorem rec12265 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(12),[1,2,5,6,13,14],[170],846⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[336]? = some (⟨232,(12),[1,2,5,6,13,14],[170],846⟩) from rfl))
private theorem rec12272 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(13),[1,2,5,6,13,14],[170],847⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[343]? = some (⟨232,(13),[1,2,5,6,13,14],[170],847⟩) from rfl))
private theorem rec12278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[349]? = some (⟨232,(14),[1,2,5,6,13,14],[170],855⟩) from rfl))
private theorem rec12286 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[357]? = some (⟨232,(15),[1,2,5,6,13,14],[170],856⟩) from rfl))
private theorem rec12292 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[363]? = some (⟨232,(16),[1,2,5,6,13,14],[170],857⟩) from rfl))
private theorem rec12298 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[369]? = some (⟨232,(17),[1,2,5,6,13,14],[170],858⟩) from rfl))
private theorem rec12305 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (18) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[376]? = some (⟨232,(18),[1,2,5,6,13,14],[170],859⟩) from rfl))
private theorem rec12311 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 232 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[382]? = some (⟨232,(19),[1,2,5,6,13,14],[170],860⟩) from rfl))
private theorem rec12319 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[390]? = some (⟨234,(0),[1,2,5,6,13,14],[170],568⟩) from rfl))
private theorem rec12325 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[396]? = some (⟨234,(1),[1,2,5,6,13,14],[170],569⟩) from rfl))
private theorem rec12333 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[404]? = some (⟨234,(2),[1,2,5,6,13,14],[170],570⟩) from rfl))
private theorem rec12341 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[412]? = some (⟨234,(3),[1,2,5,6,13,14],[170],571⟩) from rfl))
private theorem rec12349 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[420]? = some (⟨234,(4),[1,2,5,6,13,14],[170],572⟩) from rfl))
private theorem rec12355 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[426]? = some (⟨234,(5),[1,2,5,6,13,14],[170],573⟩) from rfl))
private theorem rec12363 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[434]? = some (⟨234,(6),[1,2,5,6,13,14],[170],573⟩) from rfl))
private theorem rec12371 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[442]? = some (⟨234,(7),[1,2,5,6,13,14],[170],573⟩) from rfl))
private theorem rec12379 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[450]? = some (⟨234,(8),[1,2,5,6,13,14],[170],574⟩) from rfl))
private theorem rec12385 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[456]? = some (⟨234,(9),[1,2,5,6,13,14],[170],575⟩) from rfl))
private theorem rec12393 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[464]? = some (⟨234,(10),[1,2,5,6,13,14],[170],575⟩) from rfl))
private theorem rec12401 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[472]? = some (⟨234,(11),[1,2,5,6,13,14],[170],575⟩) from rfl))
private theorem rec12409 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[480]? = some (⟨234,(12),[1,2,5,6,13,14],[170],576⟩) from rfl))
private theorem rec12415 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[486]? = some (⟨234,(13),[1,2,5,6,13,14],[170],577⟩) from rfl))
private theorem rec12423 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[494]? = some (⟨234,(14),[1,2,5,6,13,14],[170],577⟩) from rfl))
private theorem rec12431 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 234 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[502]? = some (⟨234,(15),[1,2,5,6,13,14],[170],577⟩) from rfl))
private theorem rec12439 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[510]? = some (⟨235,(0),[1,2,5,6,13,14],[170],578⟩) from rfl))
private theorem rec12445 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part11 (List.mem_of_getElem? (show section14DataRecords3Part4[516]? = some (⟨235,(1),[1,2,5,6,13,14],[170],579⟩) from rfl))
private theorem rec12451 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[3]? = some (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) from rfl))
private theorem rec12459 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[11]? = some (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) from rfl))
private theorem rec12465 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[17]? = some (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) from rfl))
private theorem rec12471 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[23]? = some (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) from rfl))
private theorem rec12477 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[29]? = some (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) from rfl))
private theorem rec12485 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[37]? = some (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) from rfl))
private theorem rec12491 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(8),[1,2,5,6,13,14],[170],578⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[43]? = some (⟨235,(8),[1,2,5,6,13,14],[170],578⟩) from rfl))
private theorem rec12497 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(9),[1,2,5,6,13,14],[170],579⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[49]? = some (⟨235,(9),[1,2,5,6,13,14],[170],579⟩) from rfl))
private theorem rec12503 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(10),[1,2,5,6,13,14],[170],580⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[55]? = some (⟨235,(10),[1,2,5,6,13,14],[170],580⟩) from rfl))
private theorem rec12511 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(11),[1,2,5,6,13,14],[170],581⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[63]? = some (⟨235,(11),[1,2,5,6,13,14],[170],581⟩) from rfl))
private theorem rec12517 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(12),[1,2,5,6,13,14],[170],586⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[69]? = some (⟨235,(12),[1,2,5,6,13,14],[170],586⟩) from rfl))
private theorem rec12523 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(13),[1,2,5,6,13,14],[170],587⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[75]? = some (⟨235,(13),[1,2,5,6,13,14],[170],587⟩) from rfl))
private theorem rec12529 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(14),[1,2,5,6,13,14],[170],588⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[81]? = some (⟨235,(14),[1,2,5,6,13,14],[170],588⟩) from rfl))
private theorem rec12537 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 235 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨235,(15),[1,2,5,6,13,14],[170],589⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[89]? = some (⟨235,(15),[1,2,5,6,13,14],[170],589⟩) from rfl))
private theorem rec12543 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 236 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(0),[1,2,5,6,13,14],[170],861⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[95]? = some (⟨236,(0),[1,2,5,6,13,14],[170],861⟩) from rfl))
private theorem rec12550 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 236 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(1),[1,2,5,6,13,14],[170],862⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[102]? = some (⟨236,(1),[1,2,5,6,13,14],[170],862⟩) from rfl))
private theorem rec12557 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 236 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(2),[1,2,6,13,14],[170],863⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[109]? = some (⟨236,(2),[1,2,6,13,14],[170],863⟩) from rfl))
private theorem rec12566 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 236 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨236,(3),[1,2,5,6,13,14],[170],864⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[118]? = some (⟨236,(3),[1,2,5,6,13,14],[170],864⟩) from rfl))
private theorem rec12573 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(0),[1,2,5,6,13,14],[170],865⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[125]? = some (⟨237,(0),[1,2,5,6,13,14],[170],865⟩) from rfl))
private theorem rec12580 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(1),[1,2,5,6,13,14],[170],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[132]? = some (⟨237,(1),[1,2,5,6,13,14],[170],594⟩) from rfl))
private theorem rec12587 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(2),[1,2,5,6,13,14],[170],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[139]? = some (⟨237,(2),[1,2,5,6,13,14],[170],595⟩) from rfl))
private theorem rec12593 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(3),[1,2,5,6,13,14],[170],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[145]? = some (⟨237,(3),[1,2,5,6,13,14],[170],596⟩) from rfl))
private theorem rec12601 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(4),[1,2,5,6,13,14],[170],866⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[153]? = some (⟨237,(4),[1,2,5,6,13,14],[170],866⟩) from rfl))
private theorem rec12608 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(5),[1,2,5,6,13,14],[170],598⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[160]? = some (⟨237,(5),[1,2,5,6,13,14],[170],598⟩) from rfl))
private theorem rec12614 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(6),[1,2,5,6,13,14],[170],599⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[166]? = some (⟨237,(6),[1,2,5,6,13,14],[170],599⟩) from rfl))
private theorem rec12620 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(7),[1,2,5,6,13,14],[170],600⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[172]? = some (⟨237,(7),[1,2,5,6,13,14],[170],600⟩) from rfl))
private theorem rec12626 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(8),[1,2,6,13,14],[170],867⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[178]? = some (⟨237,(8),[1,2,6,13,14],[170],867⟩) from rfl))
private theorem rec12635 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(9),[1,2,5,6,13,14],[170],594⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[187]? = some (⟨237,(9),[1,2,5,6,13,14],[170],594⟩) from rfl))
private theorem rec12641 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(10),[1,2,5,6,13,14],[170],595⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[193]? = some (⟨237,(10),[1,2,5,6,13,14],[170],595⟩) from rfl))
private theorem rec12647 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(11),[1,2,5,6,13,14],[170],596⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[199]? = some (⟨237,(11),[1,2,5,6,13,14],[170],596⟩) from rfl))
private theorem rec12653 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(12),[1,2,5,6,13,14],[170],868⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[205]? = some (⟨237,(12),[1,2,5,6,13,14],[170],868⟩) from rfl))
private theorem rec12660 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(13),[1,2,5,6,13,14],[170],602⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[212]? = some (⟨237,(13),[1,2,5,6,13,14],[170],602⟩) from rfl))
private theorem rec12666 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(14),[1,2,5,6,13,14],[170],603⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[218]? = some (⟨237,(14),[1,2,5,6,13,14],[170],603⟩) from rfl))
private theorem rec12672 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 237 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨237,(15),[1,2,5,6,13,14],[170],604⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[224]? = some (⟨237,(15),[1,2,5,6,13,14],[170],604⟩) from rfl))
private theorem rec12678 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (0) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[230]? = some (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) from rfl))
private theorem rec12684 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[236]? = some (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) from rfl))
private theorem rec12690 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (2) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[242]? = some (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) from rfl))
private theorem rec12698 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[250]? = some (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) from rfl))
private theorem rec12705 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (4) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[257]? = some (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) from rfl))
private theorem rec12711 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[263]? = some (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) from rfl))
private theorem rec12717 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(6),[1,2,5,6,13,14],[170],611⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[269]? = some (⟨238,(6),[1,2,5,6,13,14],[170],611⟩) from rfl))
private theorem rec12725 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(7),[1,2,5,6,13,14],[170],612⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[277]? = some (⟨238,(7),[1,2,5,6,13,14],[170],612⟩) from rfl))
private theorem rec12731 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(8),[1,2,5,6,13,14],[170],613⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[283]? = some (⟨238,(8),[1,2,5,6,13,14],[170],613⟩) from rfl))
private theorem rec12737 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(9),[1,2,5,6,13,14],[170],614⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[289]? = some (⟨238,(9),[1,2,5,6,13,14],[170],614⟩) from rfl))
private theorem rec12743 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (10) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(10),[1,2,5,6,13,14],[170],615⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[295]? = some (⟨238,(10),[1,2,5,6,13,14],[170],615⟩) from rfl))
private theorem rec12751 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (11) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(11),[1,2,5,6,13,14],[170],616⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[303]? = some (⟨238,(11),[1,2,5,6,13,14],[170],616⟩) from rfl))
private theorem rec12757 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (12) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(12),[1,2,5,6,13,14],[170],617⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[309]? = some (⟨238,(12),[1,2,5,6,13,14],[170],617⟩) from rfl))
private theorem rec12763 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (13) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(13),[1,2,5,6,13,14],[170],618⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[315]? = some (⟨238,(13),[1,2,5,6,13,14],[170],618⟩) from rfl))
private theorem rec12769 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (14) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(14),[1,2,5,6,13,14],[170],619⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[321]? = some (⟨238,(14),[1,2,5,6,13,14],[170],619⟩) from rfl))
private theorem rec12777 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 238 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨238,(15),[1,2,5,6,13,14],[170],620⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[329]? = some (⟨238,(15),[1,2,5,6,13,14],[170],620⟩) from rfl))
private theorem rec12883 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (5) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(5),[1,2,5,6,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[435]? = some (⟨243,(5),[1,2,5,6,14],[170],3⟩) from rfl))
private theorem rec12889 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (7) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(7),[1,2,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[441]? = some (⟨243,(7),[1,2,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12895 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(8),[1,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[447]? = some (⟨243,(8),[1,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12904 (si parent : ℕ) (hs : si ∈ ([5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (9) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(9),[5,6,13,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[456]? = some (⟨243,(9),[5,6,13,14],[170],143⟩) from rfl))
private theorem rec12907 (si parent : ℕ) (hs : si ∈ ([1, 2, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (15) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(15),[1,2,6,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[459]? = some (⟨243,(15),[1,2,6,14],[170],3⟩) from rfl))
private theorem rec12913 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (16) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(16),[1,5,6,13,14],[170],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[465]? = some (⟨243,(16),[1,5,6,13,14],[170],3⟩) from rfl))
private theorem rec12919 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (17) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(17),[1,2,5,6,13,14],[170],48⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[471]? = some (⟨243,(17),[1,2,5,6,13,14],[170],48⟩) from rfl))
private theorem rec12924 (si parent : ℕ) (hs : si ∈ ([2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 243 (19) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨243,(19),[2,5,6,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[476]? = some (⟨243,(19),[2,5,6,14],[170],143⟩) from rfl))
private theorem rec16570 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 640 (1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨640,(1),[13,14],[170],872⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[362]? = some (⟨640,(1),[13,14],[170],872⟩) from rfl))
private theorem rec16572 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 640 (3) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨640,(3),[13,14],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[364]? = some (⟨640,(3),[13,14],[170],101⟩) from rfl))
private theorem rec16574 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 640 (6) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨640,(6),[13,14],[170],143⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[366]? = some (⟨640,(6),[13,14],[170],143⟩) from rfl))
private theorem rec16576 (si parent : ℕ) (hs : si ∈ ([13, 14] : List ℕ)) (hp : parent ∈ ([170] : List ℕ)) : section14Recorded section14Catalog si parent 640 (8) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨640,(8),[13,14],[170],101⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part15 (List.mem_of_getElem? (show section14DataRecords4Part4[368]? = some (⟨640,(8),[13,14],[170],101⟩) from rfl))
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 14).plans.drop 5).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 14)).drop 160).take 16, section14Recorded section14Catalog 14 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 14 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 14).plans.drop 5).take 1 = [⟨6,153,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])],false,[(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(640,⟨([],[]),false,([2],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec7386 14 160 (by decide) (by decide)
  · left
    exact rec7386 14 161 (by decide) (by decide)
  · left
    exact rec7376 14 162 (by decide) (by decide)
  · left
    exact rec7376 14 163 (by decide) (by decide)
  · left
    exact rec7386 14 164 (by decide) (by decide)
  · left
    exact rec7386 14 165 (by decide) (by decide)
  · left
    exact rec7376 14 166 (by decide) (by decide)
  · left
    exact rec7376 14 167 (by decide) (by decide)
  · left
    exact rec7375 14 168 (by decide) (by decide)
  · left
    exact rec7375 14 169 (by decide) (by decide)
  · right
    intro gs hgs
    change gs ∈ [(154,⟨([1],[]),true,([1],[]),false,false,[]⟩),(155,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(156,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(157,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(158,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(159,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(160,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(161,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(162,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(163,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(164,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(165,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(166,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(167,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(168,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(169,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(170,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(171,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(172,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(173,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(174,⟨([3,1,1],[3,1,1]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(175,⟨([3,1,1,1],[3,1,1]),true,([3,1,1,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(176,⟨([3,1,1,2],[3,1,1]),true,([3,1,1,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 276⟩]⟩),(177,⟨([3,1,1],[3,1,1,1]),true,([3,1,1],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(178,⟨([3,1,1],[3,1,1,2]),true,([3,1,1],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 276⟩]⟩),(179,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(180,⟨([3,1,2,1],[3,1,2]),true,([3,1,2,2],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(181,⟨([3,1,2,2],[3,1,2]),true,([3,1,2,1],[3,1,2]),false,true,[⟨false,false,section14DataThreshold 297⟩]⟩),(182,⟨([3,1,2],[3,1,2,1]),true,([3,1,2],[3,1,2,2]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(183,⟨([3,1,2],[3,1,2,2]),true,([3,1,2],[3,1,2,1]),false,true,[⟨true,true,section14DataThreshold 297⟩]⟩),(184,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(185,⟨([3,1,2,1],[3,1,1]),true,([3,1,2,2],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(186,⟨([3,1,2,2],[3,1,1]),true,([3,1,2,1],[3,1,1]),false,true,[⟨false,false,section14DataThreshold 318⟩]⟩),(187,⟨([3,1,2],[3,1,1,1]),true,([3,1,2],[3,1,1,2]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(188,⟨([3,1,2],[3,1,1,2]),true,([3,1,2],[3,1,1,1]),false,true,[⟨true,true,section14DataThreshold 318⟩]⟩),(189,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(190,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(191,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(192,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(193,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(194,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(195,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(196,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(197,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(198,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(199,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(200,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(201,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(202,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(203,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(204,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(205,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(206,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(207,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(208,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(209,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(210,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(211,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(212,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(213,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(219,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(220,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(221,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(222,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(223,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(224,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(225,⟨([3,2],[3,3]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(226,⟨([3,1,1],[3,1,1]),true,([3,2],[3,3]),false,false,[]⟩),(227,⟨([3,1,1],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(228,⟨([3,1,2],[3,1,2]),true,([3,1,1],[3,1,1]),false,false,[]⟩),(229,⟨([3,1,2],[3,1,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(230,⟨([3,1,2],[3,1,1]),true,([3,1,2],[3,1,2]),false,false,[]⟩),(231,⟨([3,1,2],[3,1,1]),true,([3,1,1],[3,2]),false,false,[]⟩),(232,⟨([3,1,1],[3,2]),true,([3,1,2],[3,1,1]),false,false,[]⟩),(233,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(234,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(235,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(236,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(237,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(238,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(239,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(240,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(243,⟨([1],[]),true,([],[]),true,false,[]⟩),(640,⟨([],[]),false,([2],[1]),false,false,[]⟩)] at hgs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
    rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 154)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 155)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7440 14 170 (by decide) (by decide)
      · right
        exact rec7443 14 170 (by decide) (by decide)
      · right
        exact rec7446 14 170 (by decide) (by decide)
      · right
        exact rec7449 14 170 (by decide) (by decide)
      · right
        exact rec7452 14 170 (by decide) (by decide)
      · right
        exact rec7455 14 170 (by decide) (by decide)
      · right
        exact rec7458 14 170 (by decide) (by decide)
      · right
        exact rec7461 14 170 (by decide) (by decide)
      · right
        exact rec7464 14 170 (by decide) (by decide)
      · right
        exact rec7467 14 170 (by decide) (by decide)
      · right
        exact rec7470 14 170 (by decide) (by decide)
      · right
        exact rec7473 14 170 (by decide) (by decide)
      · right
        exact rec7476 14 170 (by decide) (by decide)
      · right
        exact rec7479 14 170 (by decide) (by decide)
      · right
        exact rec7482 14 170 (by decide) (by decide)
      · right
        exact rec7485 14 170 (by decide) (by decide)
      · right
        exact rec7488 14 170 (by decide) (by decide)
      · right
        exact rec7491 14 170 (by decide) (by decide)
      · right
        exact rec7494 14 170 (by decide) (by decide)
      · right
        exact rec7497 14 170 (by decide) (by decide)
      · right
        exact rec7500 14 170 (by decide) (by decide)
      · right
        exact rec7503 14 170 (by decide) (by decide)
      · right
        exact rec7506 14 170 (by decide) (by decide)
      · right
        exact rec7509 14 170 (by decide) (by decide)
      · right
        exact rec7512 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 156)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 157)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7515 14 170 (by decide) (by decide)
      · right
        exact rec7519 14 170 (by decide) (by decide)
      · right
        exact rec7524 14 170 (by decide) (by decide)
      · right
        exact rec7529 14 170 (by decide) (by decide)
      · right
        exact rec7534 14 170 (by decide) (by decide)
      · right
        exact rec7539 14 170 (by decide) (by decide)
      · right
        exact rec7543 14 170 (by decide) (by decide)
      · right
        exact rec7548 14 170 (by decide) (by decide)
      · right
        exact rec7553 14 170 (by decide) (by decide)
      · right
        exact rec7558 14 170 (by decide) (by decide)
      · right
        exact rec7563 14 170 (by decide) (by decide)
      · right
        exact rec7567 14 170 (by decide) (by decide)
      · right
        exact rec7572 14 170 (by decide) (by decide)
      · right
        exact rec7577 14 170 (by decide) (by decide)
      · right
        exact rec7582 14 170 (by decide) (by decide)
      · right
        exact rec7587 14 170 (by decide) (by decide)
      · right
        exact rec7591 14 170 (by decide) (by decide)
      · right
        exact rec7596 14 170 (by decide) (by decide)
      · right
        exact rec7601 14 170 (by decide) (by decide)
      · right
        exact rec7606 14 170 (by decide) (by decide)
      · right
        exact rec7611 14 170 (by decide) (by decide)
      · right
        exact rec7615 14 170 (by decide) (by decide)
      · right
        exact rec7620 14 170 (by decide) (by decide)
      · right
        exact rec7625 14 170 (by decide) (by decide)
      · right
        exact rec7630 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 158)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 159)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 160)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7635 14 170 (by decide) (by decide)
      · right
        exact rec7642 14 170 (by decide) (by decide)
      · right
        exact rec7649 14 170 (by decide) (by decide)
      · right
        exact rec7656 14 170 (by decide) (by decide)
      · right
        exact rec7663 14 170 (by decide) (by decide)
      · right
        exact rec7670 14 170 (by decide) (by decide)
      · right
        exact rec7677 14 170 (by decide) (by decide)
      · right
        exact rec7684 14 170 (by decide) (by decide)
      · right
        exact rec7691 14 170 (by decide) (by decide)
      · right
        exact rec7698 14 170 (by decide) (by decide)
      · right
        exact rec7705 14 170 (by decide) (by decide)
      · right
        exact rec7712 14 170 (by decide) (by decide)
      · right
        exact rec7719 14 170 (by decide) (by decide)
      · right
        exact rec7726 14 170 (by decide) (by decide)
      · right
        exact rec7733 14 170 (by decide) (by decide)
      · right
        exact rec7740 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 161)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 162)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 163)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7747 14 170 (by decide) (by decide)
      · right
        exact rec7755 14 170 (by decide) (by decide)
      · right
        exact rec7763 14 170 (by decide) (by decide)
      · right
        exact rec7771 14 170 (by decide) (by decide)
      · right
        exact rec7779 14 170 (by decide) (by decide)
      · right
        exact rec7787 14 170 (by decide) (by decide)
      · right
        exact rec7795 14 170 (by decide) (by decide)
      · right
        exact rec7803 14 170 (by decide) (by decide)
      · right
        exact rec7811 14 170 (by decide) (by decide)
      · right
        exact rec7819 14 170 (by decide) (by decide)
      · right
        exact rec7827 14 170 (by decide) (by decide)
      · right
        exact rec7835 14 170 (by decide) (by decide)
      · right
        exact rec7843 14 170 (by decide) (by decide)
      · right
        exact rec7851 14 170 (by decide) (by decide)
      · right
        exact rec7859 14 170 (by decide) (by decide)
      · right
        exact rec7867 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 164)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 165)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 166)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7875 14 170 (by decide) (by decide)
      · right
        exact rec7882 14 170 (by decide) (by decide)
      · right
        exact rec7889 14 170 (by decide) (by decide)
      · right
        exact rec7896 14 170 (by decide) (by decide)
      · right
        exact rec7903 14 170 (by decide) (by decide)
      · right
        exact rec7910 14 170 (by decide) (by decide)
      · right
        exact rec7917 14 170 (by decide) (by decide)
      · right
        exact rec7924 14 170 (by decide) (by decide)
      · right
        exact rec7931 14 170 (by decide) (by decide)
      · right
        exact rec7938 14 170 (by decide) (by decide)
      · right
        exact rec7945 14 170 (by decide) (by decide)
      · right
        exact rec7952 14 170 (by decide) (by decide)
      · right
        exact rec7959 14 170 (by decide) (by decide)
      · right
        exact rec7966 14 170 (by decide) (by decide)
      · right
        exact rec7973 14 170 (by decide) (by decide)
      · right
        exact rec7980 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 167)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec7987 14 170 (by decide) (by decide)
      · right
        exact rec7995 14 170 (by decide) (by decide)
      · right
        exact rec8003 14 170 (by decide) (by decide)
      · right
        exact rec8011 14 170 (by decide) (by decide)
      · right
        exact rec8019 14 170 (by decide) (by decide)
      · right
        exact rec8027 14 170 (by decide) (by decide)
      · right
        exact rec8035 14 170 (by decide) (by decide)
      · right
        exact rec8043 14 170 (by decide) (by decide)
      · right
        exact rec8051 14 170 (by decide) (by decide)
      · right
        exact rec8059 14 170 (by decide) (by decide)
      · right
        exact rec8067 14 170 (by decide) (by decide)
      · right
        exact rec8075 14 170 (by decide) (by decide)
      · right
        exact rec8083 14 170 (by decide) (by decide)
      · right
        exact rec8091 14 170 (by decide) (by decide)
      · right
        exact rec8099 14 170 (by decide) (by decide)
      · right
        exact rec8107 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 168)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 169)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 170)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 171)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8115 14 170 (by decide) (by decide)
      · right
        exact rec8122 14 170 (by decide) (by decide)
      · right
        exact rec8129 14 170 (by decide) (by decide)
      · right
        exact rec8136 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 172)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8143 14 170 (by decide) (by decide)
      · right
        exact rec8151 14 170 (by decide) (by decide)
      · right
        exact rec8159 14 170 (by decide) (by decide)
      · right
        exact rec8167 14 170 (by decide) (by decide)
      · right
        exact rec8175 14 170 (by decide) (by decide)
      · right
        exact rec8183 14 170 (by decide) (by decide)
      · right
        exact rec8191 14 170 (by decide) (by decide)
      · right
        exact rec8199 14 170 (by decide) (by decide)
      · right
        exact rec8207 14 170 (by decide) (by decide)
      · right
        exact rec8215 14 170 (by decide) (by decide)
      · right
        exact rec8223 14 170 (by decide) (by decide)
      · right
        exact rec8231 14 170 (by decide) (by decide)
      · right
        exact rec8239 14 170 (by decide) (by decide)
      · right
        exact rec8247 14 170 (by decide) (by decide)
      · right
        exact rec8255 14 170 (by decide) (by decide)
      · right
        exact rec8263 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 173)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 174)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 175)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8271 14 170 (by decide) (by decide)
      · right
        exact rec8278 14 170 (by decide) (by decide)
      · right
        exact rec8285 14 170 (by decide) (by decide)
      · right
        exact rec8292 14 170 (by decide) (by decide)
      · right
        exact rec8299 14 170 (by decide) (by decide)
      · right
        exact rec8306 14 170 (by decide) (by decide)
      · right
        exact rec8313 14 170 (by decide) (by decide)
      · right
        exact rec8320 14 170 (by decide) (by decide)
      · right
        exact rec8327 14 170 (by decide) (by decide)
      · right
        exact rec8334 14 170 (by decide) (by decide)
      · right
        exact rec8341 14 170 (by decide) (by decide)
      · right
        exact rec8348 14 170 (by decide) (by decide)
      · right
        exact rec8355 14 170 (by decide) (by decide)
      · right
        exact rec8362 14 170 (by decide) (by decide)
      · right
        exact rec8369 14 170 (by decide) (by decide)
      · right
        exact rec8376 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 176)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 177)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 178)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8383 14 170 (by decide) (by decide)
      · right
        exact rec8391 14 170 (by decide) (by decide)
      · right
        exact rec8399 14 170 (by decide) (by decide)
      · right
        exact rec8407 14 170 (by decide) (by decide)
      · right
        exact rec8415 14 170 (by decide) (by decide)
      · right
        exact rec8423 14 170 (by decide) (by decide)
      · right
        exact rec8431 14 170 (by decide) (by decide)
      · right
        exact rec8439 14 170 (by decide) (by decide)
      · right
        exact rec8447 14 170 (by decide) (by decide)
      · right
        exact rec8455 14 170 (by decide) (by decide)
      · right
        exact rec8463 14 170 (by decide) (by decide)
      · right
        exact rec8471 14 170 (by decide) (by decide)
      · right
        exact rec8479 14 170 (by decide) (by decide)
      · right
        exact rec8487 14 170 (by decide) (by decide)
      · right
        exact rec8495 14 170 (by decide) (by decide)
      · right
        exact rec8503 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 179)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 180)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8511 14 170 (by decide) (by decide)
      · right
        exact rec8518 14 170 (by decide) (by decide)
      · right
        exact rec8525 14 170 (by decide) (by decide)
      · right
        exact rec8532 14 170 (by decide) (by decide)
      · right
        exact rec8539 14 170 (by decide) (by decide)
      · right
        exact rec8546 14 170 (by decide) (by decide)
      · right
        exact rec8553 14 170 (by decide) (by decide)
      · right
        exact rec8560 14 170 (by decide) (by decide)
      · right
        exact rec8567 14 170 (by decide) (by decide)
      · right
        exact rec8574 14 170 (by decide) (by decide)
      · right
        exact rec8581 14 170 (by decide) (by decide)
      · right
        exact rec8588 14 170 (by decide) (by decide)
      · right
        exact rec8595 14 170 (by decide) (by decide)
      · right
        exact rec8602 14 170 (by decide) (by decide)
      · right
        exact rec8609 14 170 (by decide) (by decide)
      · right
        exact rec8616 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 181)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 182)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 183)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8623 14 170 (by decide) (by decide)
      · right
        exact rec8631 14 170 (by decide) (by decide)
      · right
        exact rec8639 14 170 (by decide) (by decide)
      · right
        exact rec8647 14 170 (by decide) (by decide)
      · right
        exact rec8655 14 170 (by decide) (by decide)
      · right
        exact rec8663 14 170 (by decide) (by decide)
      · right
        exact rec8671 14 170 (by decide) (by decide)
      · right
        exact rec8679 14 170 (by decide) (by decide)
      · right
        exact rec8687 14 170 (by decide) (by decide)
      · right
        exact rec8695 14 170 (by decide) (by decide)
      · right
        exact rec8703 14 170 (by decide) (by decide)
      · right
        exact rec8711 14 170 (by decide) (by decide)
      · right
        exact rec8719 14 170 (by decide) (by decide)
      · right
        exact rec8727 14 170 (by decide) (by decide)
      · right
        exact rec8735 14 170 (by decide) (by decide)
      · right
        exact rec8743 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 184)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 185)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8751 14 170 (by decide) (by decide)
      · right
        exact rec8758 14 170 (by decide) (by decide)
      · right
        exact rec8765 14 170 (by decide) (by decide)
      · right
        exact rec8772 14 170 (by decide) (by decide)
      · right
        exact rec8779 14 170 (by decide) (by decide)
      · right
        exact rec8786 14 170 (by decide) (by decide)
      · right
        exact rec8793 14 170 (by decide) (by decide)
      · right
        exact rec8800 14 170 (by decide) (by decide)
      · right
        exact rec8807 14 170 (by decide) (by decide)
      · right
        exact rec8814 14 170 (by decide) (by decide)
      · right
        exact rec8821 14 170 (by decide) (by decide)
      · right
        exact rec8828 14 170 (by decide) (by decide)
      · right
        exact rec8835 14 170 (by decide) (by decide)
      · right
        exact rec8842 14 170 (by decide) (by decide)
      · right
        exact rec8849 14 170 (by decide) (by decide)
      · right
        exact rec8856 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 186)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 187)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 188)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8863 14 170 (by decide) (by decide)
      · right
        exact rec8871 14 170 (by decide) (by decide)
      · right
        exact rec8879 14 170 (by decide) (by decide)
      · right
        exact rec8887 14 170 (by decide) (by decide)
      · right
        exact rec8895 14 170 (by decide) (by decide)
      · right
        exact rec8903 14 170 (by decide) (by decide)
      · right
        exact rec8911 14 170 (by decide) (by decide)
      · right
        exact rec8919 14 170 (by decide) (by decide)
      · right
        exact rec8927 14 170 (by decide) (by decide)
      · right
        exact rec8935 14 170 (by decide) (by decide)
      · right
        exact rec8943 14 170 (by decide) (by decide)
      · right
        exact rec8951 14 170 (by decide) (by decide)
      · right
        exact rec8959 14 170 (by decide) (by decide)
      · right
        exact rec8967 14 170 (by decide) (by decide)
      · right
        exact rec8975 14 170 (by decide) (by decide)
      · right
        exact rec8983 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 189)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 190)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec8991 14 170 (by decide) (by decide)
      · right
        exact rec8998 14 170 (by decide) (by decide)
      · right
        exact rec9005 14 170 (by decide) (by decide)
      · right
        exact rec9012 14 170 (by decide) (by decide)
      · right
        exact rec9019 14 170 (by decide) (by decide)
      · right
        exact rec9026 14 170 (by decide) (by decide)
      · right
        exact rec9033 14 170 (by decide) (by decide)
      · right
        exact rec9040 14 170 (by decide) (by decide)
      · right
        exact rec9047 14 170 (by decide) (by decide)
      · right
        exact rec9054 14 170 (by decide) (by decide)
      · right
        exact rec9061 14 170 (by decide) (by decide)
      · right
        exact rec9068 14 170 (by decide) (by decide)
      · right
        exact rec9075 14 170 (by decide) (by decide)
      · right
        exact rec9082 14 170 (by decide) (by decide)
      · right
        exact rec9089 14 170 (by decide) (by decide)
      · right
        exact rec9096 14 170 (by decide) (by decide)
      · right
        exact rec9103 14 170 (by decide) (by decide)
      · right
        exact rec9110 14 170 (by decide) (by decide)
      · right
        exact rec9117 14 170 (by decide) (by decide)
      · right
        exact rec9124 14 170 (by decide) (by decide)
      · right
        exact rec9131 14 170 (by decide) (by decide)
      · right
        exact rec9138 14 170 (by decide) (by decide)
      · right
        exact rec9145 14 170 (by decide) (by decide)
      · right
        exact rec9152 14 170 (by decide) (by decide)
      · right
        exact rec9159 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 191)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 192)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9166 14 170 (by decide) (by decide)
      · right
        exact rec9174 14 170 (by decide) (by decide)
      · right
        exact rec9182 14 170 (by decide) (by decide)
      · right
        exact rec9190 14 170 (by decide) (by decide)
      · right
        exact rec9198 14 170 (by decide) (by decide)
      · right
        exact rec9206 14 170 (by decide) (by decide)
      · right
        exact rec9214 14 170 (by decide) (by decide)
      · right
        exact rec9222 14 170 (by decide) (by decide)
      · right
        exact rec9230 14 170 (by decide) (by decide)
      · right
        exact rec9238 14 170 (by decide) (by decide)
      · right
        exact rec9246 14 170 (by decide) (by decide)
      · right
        exact rec9254 14 170 (by decide) (by decide)
      · right
        exact rec9262 14 170 (by decide) (by decide)
      · right
        exact rec9270 14 170 (by decide) (by decide)
      · right
        exact rec9278 14 170 (by decide) (by decide)
      · right
        exact rec9286 14 170 (by decide) (by decide)
      · right
        exact rec9294 14 170 (by decide) (by decide)
      · right
        exact rec9302 14 170 (by decide) (by decide)
      · right
        exact rec9310 14 170 (by decide) (by decide)
      · right
        exact rec9318 14 170 (by decide) (by decide)
      · right
        exact rec9326 14 170 (by decide) (by decide)
      · right
        exact rec9334 14 170 (by decide) (by decide)
      · right
        exact rec9342 14 170 (by decide) (by decide)
      · right
        exact rec9350 14 170 (by decide) (by decide)
      · right
        exact rec9358 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 193)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 194)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 195)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9366 14 170 (by decide) (by decide)
      · right
        exact rec9373 14 170 (by decide) (by decide)
      · right
        exact rec9380 14 170 (by decide) (by decide)
      · right
        exact rec9387 14 170 (by decide) (by decide)
      · right
        exact rec9394 14 170 (by decide) (by decide)
      · right
        exact rec9401 14 170 (by decide) (by decide)
      · right
        exact rec9408 14 170 (by decide) (by decide)
      · right
        exact rec9415 14 170 (by decide) (by decide)
      · right
        exact rec9422 14 170 (by decide) (by decide)
      · right
        exact rec9429 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 196)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 197)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9436 14 170 (by decide) (by decide)
      · right
        exact rec9444 14 170 (by decide) (by decide)
      · right
        exact rec9452 14 170 (by decide) (by decide)
      · right
        exact rec9460 14 170 (by decide) (by decide)
      · right
        exact rec9468 14 170 (by decide) (by decide)
      · right
        exact rec9476 14 170 (by decide) (by decide)
      · right
        exact rec9484 14 170 (by decide) (by decide)
      · right
        exact rec9492 14 170 (by decide) (by decide)
      · right
        exact rec9500 14 170 (by decide) (by decide)
      · right
        exact rec9508 14 170 (by decide) (by decide)
      · right
        exact rec9516 14 170 (by decide) (by decide)
      · right
        exact rec9524 14 170 (by decide) (by decide)
      · right
        exact rec9532 14 170 (by decide) (by decide)
      · right
        exact rec9540 14 170 (by decide) (by decide)
      · right
        exact rec9548 14 170 (by decide) (by decide)
      · right
        exact rec9556 14 170 (by decide) (by decide)
      · right
        exact rec9564 14 170 (by decide) (by decide)
      · right
        exact rec9572 14 170 (by decide) (by decide)
      · right
        exact rec9580 14 170 (by decide) (by decide)
      · right
        exact rec9588 14 170 (by decide) (by decide)
      · right
        exact rec9596 14 170 (by decide) (by decide)
      · right
        exact rec9604 14 170 (by decide) (by decide)
      · right
        exact rec9612 14 170 (by decide) (by decide)
      · right
        exact rec9620 14 170 (by decide) (by decide)
      · right
        exact rec9628 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 198)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 199)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 200)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9636 14 170 (by decide) (by decide)
      · right
        exact rec9643 14 170 (by decide) (by decide)
      · right
        exact rec9650 14 170 (by decide) (by decide)
      · right
        exact rec9657 14 170 (by decide) (by decide)
      · right
        exact rec9664 14 170 (by decide) (by decide)
      · right
        exact rec9671 14 170 (by decide) (by decide)
      · right
        exact rec9678 14 170 (by decide) (by decide)
      · right
        exact rec9685 14 170 (by decide) (by decide)
      · right
        exact rec9692 14 170 (by decide) (by decide)
      · right
        exact rec9699 14 170 (by decide) (by decide)
      · right
        exact rec9706 14 170 (by decide) (by decide)
      · right
        exact rec9713 14 170 (by decide) (by decide)
      · right
        exact rec9720 14 170 (by decide) (by decide)
      · right
        exact rec9727 14 170 (by decide) (by decide)
      · right
        exact rec9734 14 170 (by decide) (by decide)
      · right
        exact rec9741 14 170 (by decide) (by decide)
      · right
        exact rec9748 14 170 (by decide) (by decide)
      · right
        exact rec9755 14 170 (by decide) (by decide)
      · right
        exact rec9762 14 170 (by decide) (by decide)
      · right
        exact rec9769 14 170 (by decide) (by decide)
      · right
        exact rec9776 14 170 (by decide) (by decide)
      · right
        exact rec9783 14 170 (by decide) (by decide)
      · right
        exact rec9790 14 170 (by decide) (by decide)
      · right
        exact rec9797 14 170 (by decide) (by decide)
      · right
        exact rec9804 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 201)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 202)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec9811 14 170 (by decide) (by decide)
      · right
        exact rec9819 14 170 (by decide) (by decide)
      · right
        exact rec9827 14 170 (by decide) (by decide)
      · right
        exact rec9835 14 170 (by decide) (by decide)
      · right
        exact rec9843 14 170 (by decide) (by decide)
      · right
        exact rec9851 14 170 (by decide) (by decide)
      · right
        exact rec9859 14 170 (by decide) (by decide)
      · right
        exact rec9867 14 170 (by decide) (by decide)
      · right
        exact rec9875 14 170 (by decide) (by decide)
      · right
        exact rec9883 14 170 (by decide) (by decide)
      · right
        exact rec9891 14 170 (by decide) (by decide)
      · right
        exact rec9899 14 170 (by decide) (by decide)
      · right
        exact rec9907 14 170 (by decide) (by decide)
      · right
        exact rec9915 14 170 (by decide) (by decide)
      · right
        exact rec9923 14 170 (by decide) (by decide)
      · right
        exact rec9931 14 170 (by decide) (by decide)
      · right
        exact rec9939 14 170 (by decide) (by decide)
      · right
        exact rec9947 14 170 (by decide) (by decide)
      · right
        exact rec9955 14 170 (by decide) (by decide)
      · right
        exact rec9963 14 170 (by decide) (by decide)
      · right
        exact rec9971 14 170 (by decide) (by decide)
      · right
        exact rec9979 14 170 (by decide) (by decide)
      · right
        exact rec9987 14 170 (by decide) (by decide)
      · right
        exact rec9995 14 170 (by decide) (by decide)
      · right
        exact rec10003 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 203)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 204)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 205)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10011 14 170 (by decide) (by decide)
      · right
        exact rec10018 14 170 (by decide) (by decide)
      · right
        exact rec10025 14 170 (by decide) (by decide)
      · right
        exact rec10032 14 170 (by decide) (by decide)
      · right
        exact rec10038 14 170 (by decide) (by decide)
      · right
        exact rec10045 14 170 (by decide) (by decide)
      · right
        exact rec10052 14 170 (by decide) (by decide)
      · right
        exact rec10059 14 170 (by decide) (by decide)
      · right
        exact rec10066 14 170 (by decide) (by decide)
      · right
        exact rec10072 14 170 (by decide) (by decide)
      · right
        exact rec10079 14 170 (by decide) (by decide)
      · right
        exact rec10086 14 170 (by decide) (by decide)
      · right
        exact rec10093 14 170 (by decide) (by decide)
      · right
        exact rec10100 14 170 (by decide) (by decide)
      · right
        exact rec10106 14 170 (by decide) (by decide)
      · right
        exact rec10113 14 170 (by decide) (by decide)
      · right
        exact rec10120 14 170 (by decide) (by decide)
      · right
        exact rec10127 14 170 (by decide) (by decide)
      · right
        exact rec10134 14 170 (by decide) (by decide)
      · right
        exact rec10140 14 170 (by decide) (by decide)
      · right
        exact rec10147 14 170 (by decide) (by decide)
      · right
        exact rec10154 14 170 (by decide) (by decide)
      · right
        exact rec10161 14 170 (by decide) (by decide)
      · right
        exact rec10168 14 170 (by decide) (by decide)
      · right
        exact rec10174 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 206)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 207)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10181 14 170 (by decide) (by decide)
      · right
        exact rec10189 14 170 (by decide) (by decide)
      · right
        exact rec10197 14 170 (by decide) (by decide)
      · right
        exact rec10205 14 170 (by decide) (by decide)
      · right
        exact rec10213 14 170 (by decide) (by decide)
      · right
        exact rec10221 14 170 (by decide) (by decide)
      · right
        exact rec10229 14 170 (by decide) (by decide)
      · right
        exact rec10237 14 170 (by decide) (by decide)
      · right
        exact rec10245 14 170 (by decide) (by decide)
      · right
        exact rec10253 14 170 (by decide) (by decide)
      · right
        exact rec10261 14 170 (by decide) (by decide)
      · right
        exact rec10269 14 170 (by decide) (by decide)
      · right
        exact rec10277 14 170 (by decide) (by decide)
      · right
        exact rec10285 14 170 (by decide) (by decide)
      · right
        exact rec10293 14 170 (by decide) (by decide)
      · right
        exact rec10301 14 170 (by decide) (by decide)
      · right
        exact rec10309 14 170 (by decide) (by decide)
      · right
        exact rec10317 14 170 (by decide) (by decide)
      · right
        exact rec10325 14 170 (by decide) (by decide)
      · right
        exact rec10333 14 170 (by decide) (by decide)
      · right
        exact rec10341 14 170 (by decide) (by decide)
      · right
        exact rec10349 14 170 (by decide) (by decide)
      · right
        exact rec10357 14 170 (by decide) (by decide)
      · right
        exact rec10365 14 170 (by decide) (by decide)
      · right
        exact rec10373 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 208)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 209)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 210)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10381 14 170 (by decide) (by decide)
      · right
        exact rec10385 14 170 (by decide) (by decide)
      · right
        exact rec10389 14 170 (by decide) (by decide)
      · right
        exact rec10393 14 170 (by decide) (by decide)
      · right
        exact rec10397 14 170 (by decide) (by decide)
      · right
        exact rec10401 14 170 (by decide) (by decide)
      · right
        exact rec10405 14 170 (by decide) (by decide)
      · right
        exact rec10409 14 170 (by decide) (by decide)
      · right
        exact rec10413 14 170 (by decide) (by decide)
      · right
        exact rec10417 14 170 (by decide) (by decide)
      · right
        exact rec10421 14 170 (by decide) (by decide)
      · right
        exact rec10425 14 170 (by decide) (by decide)
      · right
        exact rec10429 14 170 (by decide) (by decide)
      · right
        exact rec10433 14 170 (by decide) (by decide)
      · right
        exact rec10437 14 170 (by decide) (by decide)
      · right
        exact rec10441 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 211)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 212)).length = 16 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 213)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10445 14 170 (by decide) (by decide)
      · right
        exact rec10453 14 170 (by decide) (by decide)
      · right
        exact rec10461 14 170 (by decide) (by decide)
      · right
        exact rec10469 14 170 (by decide) (by decide)
      · right
        exact rec10477 14 170 (by decide) (by decide)
      · right
        exact rec10485 14 170 (by decide) (by decide)
      · right
        exact rec10494 14 170 (by decide) (by decide)
      · right
        exact rec10504 14 170 (by decide) (by decide)
      · right
        exact rec10512 14 170 (by decide) (by decide)
      · right
        exact rec10520 14 170 (by decide) (by decide)
      · right
        exact rec10528 14 170 (by decide) (by decide)
      · right
        exact rec10536 14 170 (by decide) (by decide)
      · right
        exact rec10544 14 170 (by decide) (by decide)
      · right
        exact rec10552 14 170 (by decide) (by decide)
      · right
        exact rec10560 14 170 (by decide) (by decide)
      · right
        exact rec10568 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 219)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 220)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10672 14 170 (by decide) (by decide)
      · right
        exact rec10677 14 170 (by decide) (by decide)
      · right
        exact rec10681 14 170 (by decide) (by decide)
      · right
        exact rec10685 14 170 (by decide) (by decide)
      · right
        exact rec10689 14 170 (by decide) (by decide)
      · right
        exact rec10693 14 170 (by decide) (by decide)
      · right
        exact rec10697 14 170 (by decide) (by decide)
      · right
        exact rec10701 14 170 (by decide) (by decide)
      · right
        exact rec10705 14 170 (by decide) (by decide)
      · right
        exact rec10709 14 170 (by decide) (by decide)
      · right
        exact rec10713 14 170 (by decide) (by decide)
      · right
        exact rec10717 14 170 (by decide) (by decide)
      · right
        exact rec10721 14 170 (by decide) (by decide)
      · right
        exact rec10725 14 170 (by decide) (by decide)
      · right
        exact rec10729 14 170 (by decide) (by decide)
      · right
        exact rec10733 14 170 (by decide) (by decide)
      · right
        exact rec10737 14 170 (by decide) (by decide)
      · right
        exact rec10741 14 170 (by decide) (by decide)
      · right
        exact rec10745 14 170 (by decide) (by decide)
      · right
        exact rec10749 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 221)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10753 14 170 (by decide) (by decide)
      · right
        exact rec10761 14 170 (by decide) (by decide)
      · right
        exact rec10769 14 170 (by decide) (by decide)
      · right
        exact rec10777 14 170 (by decide) (by decide)
      · right
        exact rec10785 14 170 (by decide) (by decide)
      · right
        exact rec10793 14 170 (by decide) (by decide)
      · right
        exact rec10801 14 170 (by decide) (by decide)
      · right
        exact rec10809 14 170 (by decide) (by decide)
      · right
        exact rec10817 14 170 (by decide) (by decide)
      · right
        exact rec10825 14 170 (by decide) (by decide)
      · right
        exact rec10833 14 170 (by decide) (by decide)
      · right
        exact rec10841 14 170 (by decide) (by decide)
      · right
        exact rec10849 14 170 (by decide) (by decide)
      · right
        exact rec10857 14 170 (by decide) (by decide)
      · right
        exact rec10865 14 170 (by decide) (by decide)
      · right
        exact rec10873 14 170 (by decide) (by decide)
      · right
        exact rec10881 14 170 (by decide) (by decide)
      · right
        exact rec10889 14 170 (by decide) (by decide)
      · right
        exact rec10897 14 170 (by decide) (by decide)
      · right
        exact rec10906 14 170 (by decide) (by decide)
      · right
        exact rec10914 14 170 (by decide) (by decide)
      · right
        exact rec10922 14 170 (by decide) (by decide)
      · right
        exact rec10930 14 170 (by decide) (by decide)
      · right
        exact rec10938 14 170 (by decide) (by decide)
      · right
        exact rec10946 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 222)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec10955 14 170 (by decide) (by decide)
      · right
        exact rec10964 14 170 (by decide) (by decide)
      · right
        exact rec10971 14 170 (by decide) (by decide)
      · right
        exact rec10979 14 170 (by decide) (by decide)
      · right
        exact rec10986 14 170 (by decide) (by decide)
      · right
        exact rec10992 14 170 (by decide) (by decide)
      · right
        exact rec10999 14 170 (by decide) (by decide)
      · right
        exact rec11008 14 170 (by decide) (by decide)
      · right
        exact rec11016 14 170 (by decide) (by decide)
      · right
        exact rec11023 14 170 (by decide) (by decide)
      · right
        exact rec11029 14 170 (by decide) (by decide)
      · right
        exact rec11038 14 170 (by decide) (by decide)
      · right
        exact rec11047 14 170 (by decide) (by decide)
      · right
        exact rec11057 14 170 (by decide) (by decide)
      · right
        exact rec11066 14 170 (by decide) (by decide)
      · right
        exact rec11072 14 170 (by decide) (by decide)
      · right
        exact rec11079 14 170 (by decide) (by decide)
      · right
        exact rec11086 14 170 (by decide) (by decide)
      · right
        exact rec11094 14 170 (by decide) (by decide)
      · right
        exact rec11101 14 170 (by decide) (by decide)
      · right
        exact rec11107 14 170 (by decide) (by decide)
      · right
        exact rec11113 14 170 (by decide) (by decide)
      · right
        exact rec11119 14 170 (by decide) (by decide)
      · right
        exact rec11125 14 170 (by decide) (by decide)
      · right
        exact rec11131 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 223)).length = 10 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 224)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11138 14 170 (by decide) (by decide)
      · right
        exact rec11144 14 170 (by decide) (by decide)
      · right
        exact rec11150 14 170 (by decide) (by decide)
      · right
        exact rec11156 14 170 (by decide) (by decide)
      · right
        exact rec11162 14 170 (by decide) (by decide)
      · right
        exact rec11168 14 170 (by decide) (by decide)
      · right
        exact rec11176 14 170 (by decide) (by decide)
      · right
        exact rec11184 14 170 (by decide) (by decide)
      · right
        exact rec11192 14 170 (by decide) (by decide)
      · right
        exact rec11200 14 170 (by decide) (by decide)
      · right
        exact rec11208 14 170 (by decide) (by decide)
      · right
        exact rec11216 14 170 (by decide) (by decide)
      · right
        exact rec11224 14 170 (by decide) (by decide)
      · right
        exact rec11232 14 170 (by decide) (by decide)
      · right
        exact rec11240 14 170 (by decide) (by decide)
      · right
        exact rec11248 14 170 (by decide) (by decide)
      · right
        exact rec11256 14 170 (by decide) (by decide)
      · right
        exact rec11264 14 170 (by decide) (by decide)
      · right
        exact rec11272 14 170 (by decide) (by decide)
      · right
        exact rec11280 14 170 (by decide) (by decide)
      · right
        exact rec11288 14 170 (by decide) (by decide)
      · right
        exact rec11296 14 170 (by decide) (by decide)
      · right
        exact rec11304 14 170 (by decide) (by decide)
      · right
        exact rec11312 14 170 (by decide) (by decide)
      · right
        exact rec11320 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 225)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11328 14 170 (by decide) (by decide)
      · right
        exact rec11334 14 170 (by decide) (by decide)
      · right
        exact rec11340 14 170 (by decide) (by decide)
      · right
        exact rec11347 14 170 (by decide) (by decide)
      · right
        exact rec11354 14 170 (by decide) (by decide)
      · right
        exact rec11361 14 170 (by decide) (by decide)
      · right
        exact rec11367 14 170 (by decide) (by decide)
      · right
        exact rec11373 14 170 (by decide) (by decide)
      · right
        exact rec11381 14 170 (by decide) (by decide)
      · right
        exact rec11388 14 170 (by decide) (by decide)
      · right
        exact rec11396 14 170 (by decide) (by decide)
      · right
        exact rec11402 14 170 (by decide) (by decide)
      · right
        exact rec11408 14 170 (by decide) (by decide)
      · right
        exact rec11416 14 170 (by decide) (by decide)
      · right
        exact rec11423 14 170 (by decide) (by decide)
      · right
        exact rec11431 14 170 (by decide) (by decide)
      · right
        exact rec11437 14 170 (by decide) (by decide)
      · right
        exact rec11443 14 170 (by decide) (by decide)
      · right
        exact rec11451 14 170 (by decide) (by decide)
      · right
        exact rec11458 14 170 (by decide) (by decide)
      · right
        exact rec11466 14 170 (by decide) (by decide)
      · right
        exact rec11472 14 170 (by decide) (by decide)
      · right
        exact rec11478 14 170 (by decide) (by decide)
      · right
        exact rec11486 14 170 (by decide) (by decide)
      · right
        exact rec11493 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 226)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11501 14 170 (by decide) (by decide)
      · right
        exact rec11508 14 170 (by decide) (by decide)
      · right
        exact rec11514 14 170 (by decide) (by decide)
      · right
        exact rec11520 14 170 (by decide) (by decide)
      · right
        exact rec11526 14 170 (by decide) (by decide)
      · right
        exact rec11532 14 170 (by decide) (by decide)
      · right
        exact rec11538 14 170 (by decide) (by decide)
      · right
        exact rec11544 14 170 (by decide) (by decide)
      · right
        exact rec11550 14 170 (by decide) (by decide)
      · right
        exact rec11556 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 227)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11562 14 170 (by decide) (by decide)
      · right
        exact rec11568 14 170 (by decide) (by decide)
      · right
        exact rec11574 14 170 (by decide) (by decide)
      · right
        exact rec11582 14 170 (by decide) (by decide)
      · right
        exact rec11588 14 170 (by decide) (by decide)
      · right
        exact rec11596 14 170 (by decide) (by decide)
      · right
        exact rec11602 14 170 (by decide) (by decide)
      · right
        exact rec11608 14 170 (by decide) (by decide)
      · right
        exact rec11616 14 170 (by decide) (by decide)
      · right
        exact rec11622 14 170 (by decide) (by decide)
      · right
        exact rec11630 14 170 (by decide) (by decide)
      · right
        exact rec11636 14 170 (by decide) (by decide)
      · right
        exact rec11642 14 170 (by decide) (by decide)
      · right
        exact rec11650 14 170 (by decide) (by decide)
      · right
        exact rec11656 14 170 (by decide) (by decide)
      · right
        exact rec11664 14 170 (by decide) (by decide)
      · right
        exact rec11670 14 170 (by decide) (by decide)
      · right
        exact rec11676 14 170 (by decide) (by decide)
      · right
        exact rec11684 14 170 (by decide) (by decide)
      · right
        exact rec11690 14 170 (by decide) (by decide)
      · right
        exact rec11698 14 170 (by decide) (by decide)
      · right
        exact rec11704 14 170 (by decide) (by decide)
      · right
        exact rec11710 14 170 (by decide) (by decide)
      · right
        exact rec11718 14 170 (by decide) (by decide)
      · right
        exact rec11724 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 228)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11732 14 170 (by decide) (by decide)
      · right
        exact rec11739 14 170 (by decide) (by decide)
      · right
        exact rec11747 14 170 (by decide) (by decide)
      · right
        exact rec11756 14 170 (by decide) (by decide)
      · right
        exact rec11763 14 170 (by decide) (by decide)
      · right
        exact rec11769 14 170 (by decide) (by decide)
      · right
        exact rec11775 14 170 (by decide) (by decide)
      · right
        exact rec11781 14 170 (by decide) (by decide)
      · right
        exact rec11787 14 170 (by decide) (by decide)
      · right
        exact rec11793 14 170 (by decide) (by decide)
      · right
        exact rec11800 14 170 (by decide) (by decide)
      · right
        exact rec11806 14 170 (by decide) (by decide)
      · right
        exact rec11812 14 170 (by decide) (by decide)
      · right
        exact rec11818 14 170 (by decide) (by decide)
      · right
        exact rec11824 14 170 (by decide) (by decide)
      · right
        exact rec11830 14 170 (by decide) (by decide)
      · right
        exact rec11836 14 170 (by decide) (by decide)
      · right
        exact rec11842 14 170 (by decide) (by decide)
      · right
        exact rec11848 14 170 (by decide) (by decide)
      · right
        exact rec11854 14 170 (by decide) (by decide)
      · right
        exact rec11860 14 170 (by decide) (by decide)
      · right
        exact rec11866 14 170 (by decide) (by decide)
      · right
        exact rec11872 14 170 (by decide) (by decide)
      · right
        exact rec11878 14 170 (by decide) (by decide)
      · right
        exact rec11884 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 229)).length = 25 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 230)).length = 25 := by decide +kernel
      have hjj : j < 25 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec11890 14 170 (by decide) (by decide)
      · right
        exact rec11896 14 170 (by decide) (by decide)
      · right
        exact rec11903 14 170 (by decide) (by decide)
      · right
        exact rec11909 14 170 (by decide) (by decide)
      · right
        exact rec11915 14 170 (by decide) (by decide)
      · right
        exact rec11921 14 170 (by decide) (by decide)
      · right
        exact rec11927 14 170 (by decide) (by decide)
      · right
        exact rec11935 14 170 (by decide) (by decide)
      · right
        exact rec11942 14 170 (by decide) (by decide)
      · right
        exact rec11949 14 170 (by decide) (by decide)
      · right
        exact rec11958 14 170 (by decide) (by decide)
      · right
        exact rec11964 14 170 (by decide) (by decide)
      · right
        exact rec11971 14 170 (by decide) (by decide)
      · right
        exact rec11978 14 170 (by decide) (by decide)
      · right
        exact rec11984 14 170 (by decide) (by decide)
      · right
        exact rec11993 14 170 (by decide) (by decide)
      · right
        exact rec11999 14 170 (by decide) (by decide)
      · right
        exact rec12005 14 170 (by decide) (by decide)
      · right
        exact rec12013 14 170 (by decide) (by decide)
      · right
        exact rec12019 14 170 (by decide) (by decide)
      · right
        exact rec12027 14 170 (by decide) (by decide)
      · right
        exact rec12033 14 170 (by decide) (by decide)
      · right
        exact rec12039 14 170 (by decide) (by decide)
      · right
        exact rec12047 14 170 (by decide) (by decide)
      · right
        exact rec12053 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 231)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12061 14 170 (by decide) (by decide)
      · right
        exact rec12068 14 170 (by decide) (by decide)
      · right
        exact rec12076 14 170 (by decide) (by decide)
      · right
        exact rec12082 14 170 (by decide) (by decide)
      · right
        exact rec12088 14 170 (by decide) (by decide)
      · right
        exact rec12095 14 170 (by decide) (by decide)
      · right
        exact rec12103 14 170 (by decide) (by decide)
      · right
        exact rec12109 14 170 (by decide) (by decide)
      · right
        exact rec12115 14 170 (by decide) (by decide)
      · right
        exact rec12121 14 170 (by decide) (by decide)
      · right
        exact rec12127 14 170 (by decide) (by decide)
      · right
        exact rec12133 14 170 (by decide) (by decide)
      · right
        exact rec12139 14 170 (by decide) (by decide)
      · right
        exact rec12145 14 170 (by decide) (by decide)
      · right
        exact rec12151 14 170 (by decide) (by decide)
      · right
        exact rec12157 14 170 (by decide) (by decide)
      · right
        exact rec12163 14 170 (by decide) (by decide)
      · right
        exact rec12169 14 170 (by decide) (by decide)
      · right
        exact rec12175 14 170 (by decide) (by decide)
      · right
        exact rec12181 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 232)).length = 20 := by decide +kernel
      have hjj : j < 20 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12187 14 170 (by decide) (by decide)
      · right
        exact rec12193 14 170 (by decide) (by decide)
      · right
        exact rec12199 14 170 (by decide) (by decide)
      · right
        exact rec12206 14 170 (by decide) (by decide)
      · right
        exact rec12213 14 170 (by decide) (by decide)
      · right
        exact rec12220 14 170 (by decide) (by decide)
      · right
        exact rec12226 14 170 (by decide) (by decide)
      · right
        exact rec12232 14 170 (by decide) (by decide)
      · right
        exact rec12239 14 170 (by decide) (by decide)
      · right
        exact rec12245 14 170 (by decide) (by decide)
      · right
        exact rec12253 14 170 (by decide) (by decide)
      · right
        exact rec12259 14 170 (by decide) (by decide)
      · right
        exact rec12265 14 170 (by decide) (by decide)
      · right
        exact rec12272 14 170 (by decide) (by decide)
      · right
        exact rec12278 14 170 (by decide) (by decide)
      · right
        exact rec12286 14 170 (by decide) (by decide)
      · right
        exact rec12292 14 170 (by decide) (by decide)
      · right
        exact rec12298 14 170 (by decide) (by decide)
      · right
        exact rec12305 14 170 (by decide) (by decide)
      · right
        exact rec12311 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 233)).length = 4 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 234)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12319 14 170 (by decide) (by decide)
      · right
        exact rec12325 14 170 (by decide) (by decide)
      · right
        exact rec12333 14 170 (by decide) (by decide)
      · right
        exact rec12341 14 170 (by decide) (by decide)
      · right
        exact rec12349 14 170 (by decide) (by decide)
      · right
        exact rec12355 14 170 (by decide) (by decide)
      · right
        exact rec12363 14 170 (by decide) (by decide)
      · right
        exact rec12371 14 170 (by decide) (by decide)
      · right
        exact rec12379 14 170 (by decide) (by decide)
      · right
        exact rec12385 14 170 (by decide) (by decide)
      · right
        exact rec12393 14 170 (by decide) (by decide)
      · right
        exact rec12401 14 170 (by decide) (by decide)
      · right
        exact rec12409 14 170 (by decide) (by decide)
      · right
        exact rec12415 14 170 (by decide) (by decide)
      · right
        exact rec12423 14 170 (by decide) (by decide)
      · right
        exact rec12431 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 235)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12439 14 170 (by decide) (by decide)
      · right
        exact rec12445 14 170 (by decide) (by decide)
      · right
        exact rec12451 14 170 (by decide) (by decide)
      · right
        exact rec12459 14 170 (by decide) (by decide)
      · right
        exact rec12465 14 170 (by decide) (by decide)
      · right
        exact rec12471 14 170 (by decide) (by decide)
      · right
        exact rec12477 14 170 (by decide) (by decide)
      · right
        exact rec12485 14 170 (by decide) (by decide)
      · right
        exact rec12491 14 170 (by decide) (by decide)
      · right
        exact rec12497 14 170 (by decide) (by decide)
      · right
        exact rec12503 14 170 (by decide) (by decide)
      · right
        exact rec12511 14 170 (by decide) (by decide)
      · right
        exact rec12517 14 170 (by decide) (by decide)
      · right
        exact rec12523 14 170 (by decide) (by decide)
      · right
        exact rec12529 14 170 (by decide) (by decide)
      · right
        exact rec12537 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 236)).length = 4 := by decide +kernel
      have hjj : j < 4 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12543 14 170 (by decide) (by decide)
      · right
        exact rec12550 14 170 (by decide) (by decide)
      · right
        exact rec12557 14 170 (by decide) (by decide)
      · right
        exact rec12566 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 237)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12573 14 170 (by decide) (by decide)
      · right
        exact rec12580 14 170 (by decide) (by decide)
      · right
        exact rec12587 14 170 (by decide) (by decide)
      · right
        exact rec12593 14 170 (by decide) (by decide)
      · right
        exact rec12601 14 170 (by decide) (by decide)
      · right
        exact rec12608 14 170 (by decide) (by decide)
      · right
        exact rec12614 14 170 (by decide) (by decide)
      · right
        exact rec12620 14 170 (by decide) (by decide)
      · right
        exact rec12626 14 170 (by decide) (by decide)
      · right
        exact rec12635 14 170 (by decide) (by decide)
      · right
        exact rec12641 14 170 (by decide) (by decide)
      · right
        exact rec12647 14 170 (by decide) (by decide)
      · right
        exact rec12653 14 170 (by decide) (by decide)
      · right
        exact rec12660 14 170 (by decide) (by decide)
      · right
        exact rec12666 14 170 (by decide) (by decide)
      · right
        exact rec12672 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 238)).length = 16 := by decide +kernel
      have hjj : j < 16 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · right
        exact rec12678 14 170 (by decide) (by decide)
      · right
        exact rec12684 14 170 (by decide) (by decide)
      · right
        exact rec12690 14 170 (by decide) (by decide)
      · right
        exact rec12698 14 170 (by decide) (by decide)
      · right
        exact rec12705 14 170 (by decide) (by decide)
      · right
        exact rec12711 14 170 (by decide) (by decide)
      · right
        exact rec12717 14 170 (by decide) (by decide)
      · right
        exact rec12725 14 170 (by decide) (by decide)
      · right
        exact rec12731 14 170 (by decide) (by decide)
      · right
        exact rec12737 14 170 (by decide) (by decide)
      · right
        exact rec12743 14 170 (by decide) (by decide)
      · right
        exact rec12751 14 170 (by decide) (by decide)
      · right
        exact rec12757 14 170 (by decide) (by decide)
      · right
        exact rec12763 14 170 (by decide) (by decide)
      · right
        exact rec12769 14 170 (by decide) (by decide)
      · right
        exact rec12777 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 239)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 240)).length = 20 := by decide +kernel
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
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 243)).length = 20 := by decide +kernel
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
        exact rec12883 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec12889 14 170 (by decide) (by decide)
      · right
        exact rec12895 14 170 (by decide) (by decide)
      · right
        exact rec12904 14 170 (by decide) (by decide)
      · left
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
        exact rec12907 14 170 (by decide) (by decide)
      · right
        exact rec12913 14 170 (by decide) (by decide)
      · right
        exact rec12919 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec12924 14 170 (by decide) (by decide)
    · intro j hj
      have hlen : (section14GoalBranches section14Catalog (section14Goal section14Catalog 640)).length = 10 := by decide +kernel
      have hjj : j < 10 := by simpa only [List.mem_range,hlen] using hj
      interval_cases j
      · left
        decide +kernel
      · right
        exact rec16570 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec16572 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · left
        decide +kernel
      · right
        exact rec16574 14 170 (by decide) (by decide)
      · left
        decide +kernel
      · right
        exact rec16576 14 170 (by decide) (by decide)
      · left
        decide +kernel
  · left
    exact rec7382 14 171 (by decide) (by decide)
  · left
    exact rec7375 14 172 (by decide) (by decide)
  · left
    exact rec7375 14 173 (by decide) (by decide)
  · left
    exact rec7389 14 174 (by decide) (by decide)
  · left
    exact rec7382 14 175 (by decide) (by decide)
end Section14Coverage_14_5_p160_176

#print axioms solution
