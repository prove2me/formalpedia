-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_coverage0007_parents_0192_0256
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T05:44:32.391313+00:00
-- url     : https://prove2.me/submissions/44ec33a6-03f2-48d6-9263-cb58974d6476

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0192_0208
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_7_p192_208
private theorem rec13278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[830]? = some (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec13279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[831]? = some (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec13290 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[842]? = some (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec13294 (si parent : ℕ) (hs : si ∈ ([1, 5, 6, 13] : List ℕ)) (hp : parent ∈ ([194, 198] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,5,6,13],[194,198],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[846]? = some (⟨260,(-1),[1,5,6,13],[194,198],910⟩) from rfl))
private theorem rec13297 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([195, 199, 211, 215, 235, 239, 251, 255] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[849]? = some (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0007_parents_0192_0208 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 192).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec13278 5 192 (by decide) (by decide)
  · left
    exact rec13278 5 193 (by decide) (by decide)
  · left
    exact rec13294 5 194 (by decide) (by decide)
  · left
    exact rec13297 5 195 (by decide) (by decide)
  · left
    exact rec13278 5 196 (by decide) (by decide)
  · left
    exact rec13278 5 197 (by decide) (by decide)
  · left
    exact rec13294 5 198 (by decide) (by decide)
  · left
    exact rec13297 5 199 (by decide) (by decide)
  · left
    exact rec13290 5 200 (by decide) (by decide)
  · left
    exact rec13290 5 201 (by decide) (by decide)
  · left
    exact rec13279 5 202 (by decide) (by decide)
  · left
    exact rec13279 5 203 (by decide) (by decide)
  · left
    exact rec13290 5 204 (by decide) (by decide)
  · left
    exact rec13290 5 205 (by decide) (by decide)
  · left
    exact rec13279 5 206 (by decide) (by decide)
  · left
    exact rec13279 5 207 (by decide) (by decide)
end Section14Coverage_5_7_p192_208

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0192_0208


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0208_0224
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_7_p208_224
private theorem rec13278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[830]? = some (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec13279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[831]? = some (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec13289 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([210, 214, 234, 238, 250, 254] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[841]? = some (⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) from rfl))
private theorem rec13290 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[842]? = some (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec13297 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([195, 199, 211, 215, 235, 239, 251, 255] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[849]? = some (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0007_parents_0208_0224 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 208).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec13278 5 208 (by decide) (by decide)
  · left
    exact rec13278 5 209 (by decide) (by decide)
  · left
    exact rec13289 5 210 (by decide) (by decide)
  · left
    exact rec13297 5 211 (by decide) (by decide)
  · left
    exact rec13278 5 212 (by decide) (by decide)
  · left
    exact rec13278 5 213 (by decide) (by decide)
  · left
    exact rec13289 5 214 (by decide) (by decide)
  · left
    exact rec13297 5 215 (by decide) (by decide)
  · left
    exact rec13290 5 216 (by decide) (by decide)
  · left
    exact rec13290 5 217 (by decide) (by decide)
  · left
    exact rec13279 5 218 (by decide) (by decide)
  · left
    exact rec13279 5 219 (by decide) (by decide)
  · left
    exact rec13290 5 220 (by decide) (by decide)
  · left
    exact rec13290 5 221 (by decide) (by decide)
  · left
    exact rec13279 5 222 (by decide) (by decide)
  · left
    exact rec13279 5 223 (by decide) (by decide)
end Section14Coverage_5_7_p208_224

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0208_0224


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0224_0240
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_7_p224_240
private theorem rec13278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[830]? = some (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec13279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[831]? = some (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec13289 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([210, 214, 234, 238, 250, 254] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[841]? = some (⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) from rfl))
private theorem rec13290 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[842]? = some (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec13297 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([195, 199, 211, 215, 235, 239, 251, 255] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[849]? = some (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0007_parents_0224_0240 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 224).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec13290 5 224 (by decide) (by decide)
  · left
    exact rec13290 5 225 (by decide) (by decide)
  · left
    exact rec13279 5 226 (by decide) (by decide)
  · left
    exact rec13279 5 227 (by decide) (by decide)
  · left
    exact rec13290 5 228 (by decide) (by decide)
  · left
    exact rec13290 5 229 (by decide) (by decide)
  · left
    exact rec13279 5 230 (by decide) (by decide)
  · left
    exact rec13279 5 231 (by decide) (by decide)
  · left
    exact rec13278 5 232 (by decide) (by decide)
  · left
    exact rec13278 5 233 (by decide) (by decide)
  · left
    exact rec13289 5 234 (by decide) (by decide)
  · left
    exact rec13297 5 235 (by decide) (by decide)
  · left
    exact rec13278 5 236 (by decide) (by decide)
  · left
    exact rec13278 5 237 (by decide) (by decide)
  · left
    exact rec13289 5 238 (by decide) (by decide)
  · left
    exact rec13297 5 239 (by decide) (by decide)
end Section14Coverage_5_7_p224_240

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0224_0240


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0240_0256
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Coverage_5_7_p240_256
private theorem rec13278 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([42, 43, 46, 47, 58, 59, 62, 63, 66, 67, 70, 71, 82, 83, 86, 87, 106, 107, 110, 111, 122, 123, 126, 127, 128, 129, 132, 133, 144, 145, 148, 149, 168, 169, 172, 173, 184, 185, 188, 189, 192, 193, 196, 197, 208, 209, 212, 213, 232, 233, 236, 237, 248, 249, 252, 253] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[830]? = some (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) from rfl))
private theorem rec13279 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([8, 9, 12, 13, 24, 25, 28, 29, 32, 33, 36, 37, 48, 49, 52, 53, 72, 73, 76, 77, 88, 89, 92, 93, 96, 97, 100, 101, 112, 113, 116, 117, 138, 139, 142, 143, 154, 155, 158, 159, 162, 163, 166, 167, 178, 179, 182, 183, 202, 203, 206, 207, 218, 219, 222, 223, 226, 227, 230, 231, 242, 243, 246, 247] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[831]? = some (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) from rfl))
private theorem rec13289 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 13, 14] : List ℕ)) (hp : parent ∈ ([210, 214, 234, 238, 250, 254] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[841]? = some (⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) from rfl))
private theorem rec13290 (si parent : ℕ) (hs : si ∈ ([1, 2, 5, 6, 14] : List ℕ)) (hp : parent ∈ ([10, 11, 14, 15, 26, 27, 30, 31, 34, 35, 38, 39, 50, 51, 54, 55, 74, 75, 78, 79, 90, 91, 94, 95, 98, 99, 102, 103, 114, 115, 118, 119, 136, 137, 140, 141, 152, 153, 156, 157, 160, 161, 164, 165, 176, 177, 180, 181, 200, 201, 204, 205, 216, 217, 220, 221, 224, 225, 228, 229, 240, 241, 244, 245] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[842]? = some (⟨260,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) from rfl))
private theorem rec13297 (si parent : ℕ) (hs : si ∈ ([1, 5, 13] : List ℕ)) (hp : parent ∈ ([195, 199, 211, 215, 235, 239, 251, 255] : List ℕ)) : section14Recorded section14Catalog si parent 260 (-1) := by
  apply M7Section14Sep18.RecordMembership.recorded (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) ?_ si parent hs hp
  exact M7Section14Sep18.RecordMembership.part12 (List.mem_of_getElem? (show section14DataRecords4Part1[849]? = some (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) from rfl))
theorem _root_.Freiman.workReverse20260919_s0005_coverage0007_parents_0240_0256 : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 240).take 16, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  have hplan : ((section14State section14Catalog 5).plans.drop 7).take 1 = [⟨8,260,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(261,⟨([1],[]),true,([1],[]),false,false,[]⟩),(262,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(263,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(264,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(265,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(266,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(267,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(268,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(269,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(270,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(271,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(272,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(273,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(274,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(275,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(276,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(277,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(278,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(279,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(280,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(281,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(282,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(283,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(284,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(285,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(286,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(287,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(288,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(289,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(290,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(291,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(292,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(293,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(294,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(295,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(296,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(297,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(298,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(299,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(300,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(301,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(302,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(303,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(304,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(305,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(306,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(307,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(308,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(309,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(310,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(311,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(312,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(313,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(314,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(315,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(316,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(317,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(318,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(319,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(320,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(321,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(322,⟨([1],[]),true,([],[]),true,false,[]⟩),(323,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩] := by rfl
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
    exact rec13290 5 240 (by decide) (by decide)
  · left
    exact rec13290 5 241 (by decide) (by decide)
  · left
    exact rec13279 5 242 (by decide) (by decide)
  · left
    exact rec13279 5 243 (by decide) (by decide)
  · left
    exact rec13290 5 244 (by decide) (by decide)
  · left
    exact rec13290 5 245 (by decide) (by decide)
  · left
    exact rec13279 5 246 (by decide) (by decide)
  · left
    exact rec13279 5 247 (by decide) (by decide)
  · left
    exact rec13278 5 248 (by decide) (by decide)
  · left
    exact rec13278 5 249 (by decide) (by decide)
  · left
    exact rec13289 5 250 (by decide) (by decide)
  · left
    exact rec13297 5 251 (by decide) (by decide)
  · left
    exact rec13278 5 252 (by decide) (by decide)
  · left
    exact rec13278 5 253 (by decide) (by decide)
  · left
    exact rec13289 5 254 (by decide) (by decide)
  · left
    exact rec13297 5 255 (by decide) (by decide)
end Section14Coverage_5_7_p240_256

end WorkReverseInterface_Freiman_workReverse20260919_s0005_coverage0007_parents_0240_0256

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

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : ∀ pl ∈ ((section14State section14Catalog 5).plans.drop 7).take 1, ∀ b ∈ ((section14Parents section14Catalog (section14State section14Catalog 5)).drop 192).take 64, section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j := by
  intro pl hpl
  let xs := section14Parents section14Catalog (section14State section14Catalog 5)
  let P := fun b : Section14Parent => section14Recorded section14Catalog 5 b.branch pl.excludedGoal (-1) ∨ ∀ gs ∈ pl.specs, ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length, (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 = .automatic ∨ section14Recorded section14Catalog 5 b.branch gs.1 j
  exact (all_of_interval_split P xs 192 224 256 (by decide) (by decide) (all_of_interval_split P xs 192 208 224 (by decide) (by decide) (Freiman.workReverse20260919_s0005_coverage0007_parents_0192_0208 pl hpl) (Freiman.workReverse20260919_s0005_coverage0007_parents_0208_0224 pl hpl)) (all_of_interval_split P xs 224 240 256 (by decide) (by decide) (Freiman.workReverse20260919_s0005_coverage0007_parents_0224_0240 pl hpl) (Freiman.workReverse20260919_s0005_coverage0007_parents_0240_0256 pl hpl)))

#print axioms solution
